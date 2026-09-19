import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory049
import SunPrize.Certificate.Theory050
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule28257 (p1987 p2027 p2169 p2313 p2553 p2577 p2810 p3347 p3487 p3956 : Prop) (h : p2027 ∨ (¬ p2313) ∨ (¬ p3347) ∨ (¬ p1987) ∨ (¬ p2577) ∨ (¬ p3487) ∨ (¬ p2810) ∨ (¬ p3956) ∨ (¬ p2553) ∨ p2169) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2810) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial28257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory17513 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28257 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2810) (meaning t m 3347) (meaning t m 3487) (meaning t m 3956) source

theorem rule28258 (p1994 p2027 p2440 p2459 p2633 p3556 p3692 p4031 p4119 : Prop) (h : (¬ p2440) ∨ (¬ p4031) ∨ (¬ p1994) ∨ (¬ p2459) ∨ (¬ p4119) ∨ p2633 ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3556)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4031) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial28258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory17514 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28258 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2459) (meaning t m 2633) (meaning t m 3556) (meaning t m 3692) (meaning t m 4031) (meaning t m 4119) source

theorem rule28274 (p2027 p2138 p2166 p3371 p3694 p4734 : Prop) (h : (¬ p3371) ∨ (¬ p4734) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3694) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial28274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory17530 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule28274 (meaning t m 2027) (meaning t m 2138) (meaning t m 2166) (meaning t m 3371) (meaning t m 3694) (meaning t m 4734) source

theorem rule28282 (p2027 p2241 p2493 p2579 p2750 p3541 p4108 : Prop) (h : (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p2493) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial28282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory17538 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 6)
  exact rule28282 (meaning t m 2027) (meaning t m 2241) (meaning t m 2493) (meaning t m 2579) (meaning t m 2750) (meaning t m 3541) (meaning t m 4108) source

theorem rule28283 (p2027 p2088 p2319 p2563 p3957 p4340 p4359 p4590 p4882 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p3957) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p2563) ∨ (¬ p4590) ∨ (¬ p2319) ∨ (¬ p4359) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2319) ∨ (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4590) ∨ (¬ p4882) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial28283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory17539 t (m.theta 0 6) (m.theta 0 7) (m.theta 0 8) (m.theta 1 6) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 8 9)
  exact rule28283 (meaning t m 2027) (meaning t m 2088) (meaning t m 2319) (meaning t m 2563) (meaning t m 3957) (meaning t m 4340) (meaning t m 4359) (meaning t m 4590) (meaning t m 4882) (meaning t m 5016) source

theorem rule28299 (p2027 p2104 p2230 p2363 p2427 p2881 p3366 p3519 p4340 p4376 p4503 : Prop) (h : (¬ p3519) ∨ (¬ p2881) ∨ (¬ p4503) ∨ (¬ p4340) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2363) ∨ (¬ p2104) ∨ (¬ p4376) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2363) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17555 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28299 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2363) (meaning t m 2427) (meaning t m 2881) (meaning t m 3366) (meaning t m 3519) (meaning t m 4340) (meaning t m 4376) (meaning t m 4503) source

theorem rule28300 (p2027 p3266 p3292 p3366 p3399 p3452 p3631 p3950 p4236 p4376 p5284 : Prop) (h : (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3292) ∨ (¬ p5284) ∨ (¬ p3631) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4376) ∨ (¬ p3950) ∨ (¬ p3266)) : (p2027) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17556 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 3 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28300 (meaning t m 2027) (meaning t m 3266) (meaning t m 3292) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3631) (meaning t m 3950) (meaning t m 4236) (meaning t m 4376) (meaning t m 5284) source

theorem rule28301 (p2027 p2241 p2750 p2753 p3324 p3471 p3591 p3609 p4319 p4348 p4503 p4805 : Prop) (h : (¬ p3591) ∨ (¬ p2753) ∨ (¬ p4319) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4348) ∨ (¬ p3471) ∨ (¬ p4805) ∨ (¬ p4503) ∨ (¬ p2750) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3324) ∨ (¬ p3471) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p4319) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial28301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory17557 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28301 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3324) (meaning t m 3471) (meaning t m 3591) (meaning t m 3609) (meaning t m 4319) (meaning t m 4348) (meaning t m 4503) (meaning t m 4805) source

theorem rule28302 (p1976 p2027 p2545 p2992 p3365 p4111 p4315 : Prop) (h : (¬ p4111) ∨ p2027 ∨ (¬ p3365) ∨ p2545 ∨ (¬ p1976) ∨ (¬ p4315) ∨ (¬ p2992)) : (¬ p1976) ∨ (p2027) ∨ (p2545) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial28302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory17558 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule28302 (meaning t m 1976) (meaning t m 2027) (meaning t m 2545) (meaning t m 2992) (meaning t m 3365) (meaning t m 4111) (meaning t m 4315) source

theorem rule28303 (p2027 p2192 p2901 p3486 p4110 p4705 : Prop) (h : (¬ p4110) ∨ (¬ p3486) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4705) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2901) ∨ (¬ p3486) ∨ (¬ p4110) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17559 t (m.theta 1 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule28303 (meaning t m 2027) (meaning t m 2192) (meaning t m 2901) (meaning t m 3486) (meaning t m 4110) (meaning t m 4705) source

theorem rule28305 (p2027 p2341 p2590 p2901 p3581 p3644 p3691 p4705 : Prop) (h : (¬ p2901) ∨ (¬ p2590) ∨ (¬ p4705) ∨ (¬ p3581) ∨ (¬ p2341) ∨ (¬ p3691) ∨ p2027 ∨ (¬ p3644)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2590) ∨ (¬ p2901) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17561 t (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28305 (meaning t m 2027) (meaning t m 2341) (meaning t m 2590) (meaning t m 2901) (meaning t m 3581) (meaning t m 3644) (meaning t m 3691) (meaning t m 4705) source

theorem rule28307 (p1982 p2027 p2363 p2470 p2545 p2579 p3016 p4157 : Prop) (h : (¬ p2579) ∨ p2545 ∨ (¬ p3016) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p4157) ∨ (¬ p2363) ∨ (¬ p2470)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2470) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial28307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2470)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory17563 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule28307 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2470) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) (meaning t m 4157) source

theorem rule28309 (p2027 p2104 p2210 p2363 p2881 p2891 p4340 p4503 p4736 : Prop) (h : (¬ p4503) ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2363) ∨ (¬ p2891) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17565 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28309 (meaning t m 2027) (meaning t m 2104) (meaning t m 2210) (meaning t m 2363) (meaning t m 2881) (meaning t m 2891) (meaning t m 4340) (meaning t m 4503) (meaning t m 4736) source

theorem rule28310 (p2027 p2363 p2598 p2911 p2963 p3201 p4118 p4196 p4503 p4789 : Prop) (h : (¬ p4118) ∨ (¬ p2911) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p4196) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p4789) ∨ (¬ p4503) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial28310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory17566 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28310 (meaning t m 2027) (meaning t m 2363) (meaning t m 2598) (meaning t m 2911) (meaning t m 2963) (meaning t m 3201) (meaning t m 4118) (meaning t m 4196) (meaning t m 4503) (meaning t m 4789) source

theorem rule28315 (p1987 p2027 p2114 p2241 p2727 p2810 p3954 : Prop) (h : (¬ p3954) ∨ p2114 ∨ (¬ p2241) ∨ (¬ p1987) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2727)) : (¬ p1987) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial28315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory17571 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule28315 (meaning t m 1987) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2727) (meaning t m 2810) (meaning t m 3954) source

theorem rule28316 (p2027 p2829 p3585 p3876 p4390 p4708 : Prop) (h : (¬ p2829) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p4708) ∨ (¬ p4390) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p4390) ∨ (¬ p4708) := by
  classical
  tauto

theorem initial28316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4708)) := by
  have source := ElevenTheory.theory17572 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7)
  exact rule28316 (meaning t m 2027) (meaning t m 2829) (meaning t m 3585) (meaning t m 3876) (meaning t m 4390) (meaning t m 4708) source

theorem rule28317 (p2027 p2274 p2312 p2341 p3548 p4105 p4514 : Prop) (h : (¬ p2312) ∨ p2027 ∨ (¬ p4105) ∨ (¬ p3548) ∨ (¬ p2274) ∨ (¬ p2341) ∨ (¬ p4514)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial28317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory17573 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule28317 (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 2341) (meaning t m 3548) (meaning t m 4105) (meaning t m 4514) source

theorem rule28318 (p1987 p2027 p2344 p2383 p2737 p3688 p4358 : Prop) (h : (¬ p1987) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p4358) ∨ (¬ p3688) ∨ p2344) : (¬ p1987) ∨ (p2027) ∨ (p2344) ∨ (¬ p2383) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial28318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory17574 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule28318 (meaning t m 1987) (meaning t m 2027) (meaning t m 2344) (meaning t m 2383) (meaning t m 2737) (meaning t m 3688) (meaning t m 4358) source

theorem rule28320 (p1982 p2027 p2518 p2528 p2952 p2997 p3097 p3136 p3379 p3745 p4195 p4236 p4736 : Prop) (h : (¬ p3097) ∨ (¬ p1982) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4736) ∨ (¬ p3136) ∨ (¬ p2952) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3379) ∨ p2997) : (¬ p1982) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17576 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule28320 (meaning t m 1982) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2952) (meaning t m 2997) (meaning t m 3097) (meaning t m 3136) (meaning t m 3379) (meaning t m 3745) (meaning t m 4195) (meaning t m 4236) (meaning t m 4736) source

theorem rule28325 (p2341 p3166 p4104 p4548 : Prop) (h : (¬ p2341) ∨ (¬ p4548) ∨ (¬ p4104) ∨ p3166) : (¬ p2341) ∨ (p3166) ∨ (¬ p4104) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial28325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (meaning t m 3166) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory17581 (m.theta 0 3) (m.theta 0 7) (m.theta 3 8) (m.theta 7 8)
  exact rule28325 (meaning t m 2341) (meaning t m 3166) (meaning t m 4104) (meaning t m 4548) source

theorem rule28328 (p1983 p2027 p2114 p2299 p2319 p2341 p2396 p2779 p2829 : Prop) (h : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2779) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p1983) ∨ p2114 ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2779) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial28328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory17584 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28328 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2396) (meaning t m 2779) (meaning t m 2829) source

theorem rule28330 (p2027 p2307 p2962 p3097 p4110 p4539 : Prop) (h : (¬ p3097) ∨ (¬ p2962) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4539) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial28330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory17586 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule28330 (meaning t m 2027) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 4110) (meaning t m 4539) source

theorem rule28337 (p1992 p2027 p2202 p2608 p3641 p3684 p3860 p4370 : Prop) (h : (¬ p3641) ∨ (¬ p1992) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2608) ∨ p2202 ∨ (¬ p3684) ∨ (¬ p4370)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2608) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3860) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial28337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory17593 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule28337 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2608) (meaning t m 3641) (meaning t m 3684) (meaning t m 3860) (meaning t m 4370) source

theorem rule28339 (p1994 p2027 p2323 p2440 p2946 p3156 p3880 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p2440) ∨ p2323 ∨ (¬ p3156) ∨ (¬ p3880) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2440) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial28339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory17595 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule28339 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2440) (meaning t m 2946) (meaning t m 3156) (meaning t m 3880) source

theorem rule28343 (p1981 p2027 p2247 p2352 p2493 p2688 p3379 : Prop) (h : p2688 ∨ (¬ p3379) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2247) ∨ (¬ p2493)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (p2688) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial28343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory17599 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8)
  exact rule28343 (meaning t m 1981) (meaning t m 2027) (meaning t m 2247) (meaning t m 2352) (meaning t m 2493) (meaning t m 2688) (meaning t m 3379) source

theorem rule28348 (p2027 p2254 p2363 p2608 p2839 p3105 p3172 p4118 p4335 p4433 : Prop) (h : (¬ p2839) ∨ (¬ p4433) ∨ (¬ p4118) ∨ (¬ p3172) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p4335) ∨ (¬ p3105) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4335) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial28348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory17604 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 8) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule28348 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3172) (meaning t m 4118) (meaning t m 4335) (meaning t m 4433) source

theorem rule28352 (p2027 p2156 p2187 p2363 p2608 p3370 p3452 p3590 p4377 p4697 p5160 : Prop) (h : (¬ p2608) ∨ (¬ p4697) ∨ (¬ p3452) ∨ (¬ p5160) ∨ (¬ p3590) ∨ (¬ p4377) ∨ (¬ p3370) ∨ (¬ p2363) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2187)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4377) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial28352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory17608 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule28352 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2608) (meaning t m 3370) (meaning t m 3452) (meaning t m 3590) (meaning t m 4377) (meaning t m 4697) (meaning t m 5160) source

theorem rule28353 (p2027 p2307 p3055 p3319 p3549 p3684 p4368 p4736 p4948 p5020 : Prop) (h : (¬ p4368) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p4948) ∨ (¬ p3684) ∨ (¬ p3549) ∨ (¬ p5020) ∨ (¬ p2307) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3684) ∨ (¬ p4368) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial28353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory17609 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule28353 (meaning t m 2027) (meaning t m 2307) (meaning t m 3055) (meaning t m 3319) (meaning t m 3549) (meaning t m 3684) (meaning t m 4368) (meaning t m 4736) (meaning t m 4948) (meaning t m 5020) source

theorem rule28354 (p2958 p3178 p4238 : Prop) (h : (¬ p2958) ∨ p3178 ∨ (¬ p4238)) : (¬ p2958) ∨ (p3178) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial28354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2958)) ∨ (meaning t m 3178) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory17610 (m.theta 0 3) (m.theta 0 5) (m.theta 0 8)
  exact rule28354 (meaning t m 2958) (meaning t m 3178) (meaning t m 4238) source

theorem rule28355 (p1985 p2027 p2449 p2807 p3042 p3172 p3690 : Prop) (h : p3042 ∨ (¬ p3172) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3690)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (p3042) ∨ (¬ p3172) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial28355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory17611 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9)
  exact rule28355 (meaning t m 1985) (meaning t m 2027) (meaning t m 2449) (meaning t m 2807) (meaning t m 3042) (meaning t m 3172) (meaning t m 3690) source

theorem rule28357 (p3878 p4111 p4360 : Prop) (h : (¬ p4111) ∨ (¬ p3878) ∨ p4360) : (¬ p3878) ∨ (¬ p4111) ∨ (p4360) := by
  classical
  tauto

theorem initial28357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4111)) ∨ (meaning t m 4360) := by
  have source := ElevenTheory.theory17613 (m.theta 1 3) (m.theta 3 4) (m.theta 3 8)
  exact rule28357 (meaning t m 3878) (meaning t m 4111) (meaning t m 4360) source

theorem rule28358 (p2534 p4118 p4437 : Prop) (h : (¬ p4437) ∨ (¬ p2534) ∨ p4118) : (¬ p2534) ∨ (p4118) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial28358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2534)) ∨ (meaning t m 4118) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory17614 (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule28358 (meaning t m 2534) (meaning t m 4118) (meaning t m 4437) source

theorem rule28361 (p2927 p3527 p3644 : Prop) (h : (¬ p2927) ∨ (¬ p3527) ∨ (¬ p3644)) : (¬ p2927) ∨ (¬ p3527) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial28361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory17617 (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule28361 (meaning t m 2927) (meaning t m 3527) (meaning t m 3644) source

theorem rule28362 (p2911 p2927 p3527 : Prop) (h : (¬ p2927) ∨ (¬ p3527) ∨ p2911) : (p2911) ∨ (¬ p2927) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial28362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2911) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory17618 (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule28362 (meaning t m 2911) (meaning t m 2927) (meaning t m 3527) source

theorem rule28364 (p2996 p4067 p4154 : Prop) (h : (¬ p4154) ∨ (¬ p4067) ∨ p2996) : (p2996) ∨ (¬ p4067) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial28364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2996) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory17620 (m.theta 1 3) (m.theta 3 6) (m.theta 3 7)
  exact rule28364 (meaning t m 2996) (meaning t m 4067) (meaning t m 4154) source

theorem rule28365 (p2027 p3946 p3998 p4114 p4186 p4286 p4620 p4710 : Prop) (h : (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4710) ∨ (¬ p3946) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p4114) ∨ (¬ p3998)) : (p2027) ∨ (¬ p3946) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial28365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory17621 t (m.theta 0 6) (m.theta 0 8) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 10)
  exact rule28365 (meaning t m 2027) (meaning t m 3946) (meaning t m 3998) (meaning t m 4114) (meaning t m 4186) (meaning t m 4286) (meaning t m 4620) (meaning t m 4710) source

theorem rule28369 (p2027 p2870 p2881 p3553 p4386 p5053 : Prop) (h : (¬ p2881) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p4386) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4386) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial28369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory17625 t (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28369 (meaning t m 2027) (meaning t m 2870) (meaning t m 2881) (meaning t m 3553) (meaning t m 4386) (meaning t m 5053) source

theorem rule28371 (p3322 p3744 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p3322) ∨ p3744) : (¬ p3322) ∨ (p3744) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial28371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3322)) ∨ (meaning t m 3744) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory17627 (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule28371 (meaning t m 3322) (meaning t m 3744) (meaning t m 3989) source

theorem rule28379 (p2027 p2299 p3097 p3379 p3641 p3645 p3646 p3954 p4030 p4420 p4877 : Prop) (h : (¬ p3954) ∨ (¬ p4030) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3645) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p4877) ∨ (¬ p2299) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4420) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial28379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory17635 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule28379 (meaning t m 2027) (meaning t m 2299) (meaning t m 3097) (meaning t m 3379) (meaning t m 3641) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 4030) (meaning t m 4420) (meaning t m 4877) source

theorem rule28384 (p1986 p2027 p2553 p2598 p2780 p3008 p3822 : Prop) (h : (¬ p2598) ∨ (¬ p1986) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p2780) ∨ p2027 ∨ (¬ p3822)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p3008) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial28384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory17640 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule28384 (meaning t m 1986) (meaning t m 2027) (meaning t m 2553) (meaning t m 2598) (meaning t m 2780) (meaning t m 3008) (meaning t m 3822) source

theorem rule28386 (p1977 p2027 p2241 p2553 p3008 p3568 p3591 p4319 : Prop) (h : p3008 ∨ (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p3568)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial28386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory17642 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule28386 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 3008) (meaning t m 3568) (meaning t m 3591) (meaning t m 4319) source

theorem rule28389 (p2027 p2668 p2696 p2797 p3238 p3452 p3880 p4134 p4733 : Prop) (h : (¬ p4134) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p2797) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17645 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8)
  exact rule28389 (meaning t m 2027) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 4134) (meaning t m 4733) source

theorem rule28394 (p2027 p2891 p3568 p4140 p4173 p4564 : Prop) (h : (¬ p2891) ∨ (¬ p4564) ∨ (¬ p4140) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p3568)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3568) ∨ (¬ p4140) ∨ (¬ p4173) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial28394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory17650 t (m.theta 1 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule28394 (meaning t m 2027) (meaning t m 2891) (meaning t m 3568) (meaning t m 4140) (meaning t m 4173) (meaning t m 4564) source

theorem rule28395 (p2027 p2248 p2807 p3238 p3256 p3452 p3880 p4044 p4348 p4905 : Prop) (h : (¬ p4348) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4044) ∨ (¬ p4905) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3880) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3238) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial28395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory17651 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28395 (meaning t m 2027) (meaning t m 2248) (meaning t m 2807) (meaning t m 3238) (meaning t m 3256) (meaning t m 3452) (meaning t m 3880) (meaning t m 4044) (meaning t m 4348) (meaning t m 4905) source

theorem rule28396 (p1994 p2027 p2528 p2630 p3177 p3498 p3857 p3877 : Prop) (h : (¬ p2528) ∨ (¬ p3177) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p1994) ∨ p3498 ∨ (¬ p2630) ∨ (¬ p3877)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (p3498) ∨ (¬ p3857) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial28396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3177)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory17652 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule28396 (meaning t m 1994) (meaning t m 2027) (meaning t m 2528) (meaning t m 2630) (meaning t m 3177) (meaning t m 3498) (meaning t m 3857) (meaning t m 3877) source

theorem rule28397 (p2027 p2245 p2406 p2509 p2589 p2655 p3471 p3609 p4348 p4438 p4733 p4805 : Prop) (h : (¬ p2589) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2245) ∨ (¬ p2406) ∨ (¬ p4733) ∨ (¬ p4438) ∨ (¬ p3471) ∨ (¬ p2509) ∨ (¬ p2655) ∨ (¬ p4805) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3471) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4733) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial28397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory17653 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28397 (meaning t m 2027) (meaning t m 2245) (meaning t m 2406) (meaning t m 2509) (meaning t m 2589) (meaning t m 2655) (meaning t m 3471) (meaning t m 3609) (meaning t m 4348) (meaning t m 4438) (meaning t m 4733) (meaning t m 4805) source

theorem rule28401 (p2027 p2588 p3276 p4191 p4422 p4624 : Prop) (h : (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p4422) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial28401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory17657 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule28401 (meaning t m 2027) (meaning t m 2588) (meaning t m 3276) (meaning t m 4191) (meaning t m 4422) (meaning t m 4624) source

theorem rule28407 (p1976 p2027 p2169 p3055 p3309 p3822 p3923 p5220 : Prop) (h : p2169 ∨ (¬ p3923) ∨ (¬ p3309) ∨ (¬ p3055) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p5220)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p3055) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3923) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial28407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory17663 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28407 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 3055) (meaning t m 3309) (meaning t m 3822) (meaning t m 3923) (meaning t m 5220) source

theorem rule28410 (p2027 p2630 p2922 p3361 p3414 p3740 p4814 : Prop) (h : (¬ p3740) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3414) ∨ (¬ p3361) ∨ (¬ p4814) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial28410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory17666 t (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule28410 (meaning t m 2027) (meaning t m 2630) (meaning t m 2922) (meaning t m 3361) (meaning t m 3414) (meaning t m 3740) (meaning t m 4814) source

theorem rule28414 (p2926 p3452 p4366 : Prop) (h : (¬ p3452) ∨ (¬ p2926) ∨ p4366) : (¬ p2926) ∨ (¬ p3452) ∨ (p4366) := by
  classical
  tauto

theorem initial28414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 4366) := by
  have source := ElevenTheory.theory17670 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7)
  exact rule28414 (meaning t m 2926) (meaning t m 3452) (meaning t m 4366) source

theorem rule28418 (p2027 p2363 p2383 p3055 p3266 p3876 p3987 p4786 p4831 p5503 : Prop) (h : (¬ p2363) ∨ (¬ p3987) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p3266) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial28418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory17674 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule28418 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 3055) (meaning t m 3266) (meaning t m 3876) (meaning t m 3987) (meaning t m 4786) (meaning t m 4831) (meaning t m 5503) source

theorem rule28420 (p2027 p2577 p3389 p3564 p3660 p3946 p4646 : Prop) (h : (¬ p4646) ∨ (¬ p3660) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p3946)) : (p2027) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3946) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial28420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory17676 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule28420 (meaning t m 2027) (meaning t m 2577) (meaning t m 3389) (meaning t m 3564) (meaning t m 3660) (meaning t m 3946) (meaning t m 4646) source

theorem rule28421 (p2027 p2132 p2579 p2619 p2753 p3146 p3324 p3347 p3984 p5118 p5216 p5580 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p5580) ∨ (¬ p5118) ∨ (¬ p2619) ∨ (¬ p2579) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3324) ∨ (¬ p3984)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p3347) ∨ (¬ p3984) ∨ (¬ p5118) ∨ (¬ p5216) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial28421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory17677 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 6) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule28421 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2619) (meaning t m 2753) (meaning t m 3146) (meaning t m 3324) (meaning t m 3347) (meaning t m 3984) (meaning t m 5118) (meaning t m 5216) (meaning t m 5580) source

theorem rule28422 (p3984 p4037 p5247 p5514 : Prop) (h : (¬ p4037) ∨ (¬ p5247) ∨ (¬ p3984) ∨ p5514) : (¬ p3984) ∨ (¬ p4037) ∨ (¬ p5247) ∨ (p5514) := by
  classical
  tauto

theorem initial28422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 5247)) ∨ (meaning t m 5514) := by
  have source := ElevenTheory.theory17678 (m.theta 3 6) (m.theta 4 6) (m.theta 6 10) (m.theta 6 9)
  exact rule28422 (meaning t m 3984) (meaning t m 4037) (meaning t m 5247) (meaning t m 5514) source

theorem rule28423 (p2027 p2254 p2608 p2707 p2963 p4037 p4191 p4253 p4826 : Prop) (h : (¬ p2963) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4253)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial28423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory17679 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule28423 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2963) (meaning t m 4037) (meaning t m 4191) (meaning t m 4253) (meaning t m 4826) source

theorem rule28425 (p2027 p2655 p3136 p3156 p3904 p4120 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p2655) ∨ (¬ p3904)) : (p2027) ∨ (¬ p2655) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial28425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory17681 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule28425 (meaning t m 2027) (meaning t m 2655) (meaning t m 3136) (meaning t m 3156) (meaning t m 3904) (meaning t m 4120) (meaning t m 4787) source

theorem rule28432 (p2027 p2247 p2459 p2881 p3051 p4037 p4154 p4521 p4604 : Prop) (h : (¬ p2459) ∨ (¬ p4037) ∨ (¬ p2881) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial28432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory17688 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule28432 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2881) (meaning t m 3051) (meaning t m 4037) (meaning t m 4154) (meaning t m 4521) (meaning t m 4604) source

theorem rule28437 (p2891 p2901 p3412 : Prop) (h : (¬ p3412) ∨ (¬ p2891) ∨ p2901) : (¬ p2891) ∨ (p2901) ∨ (¬ p3412) := by
  classical
  tauto

theorem initial28437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 3412)) := by
  have source := ElevenTheory.theory17693 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule28437 (meaning t m 2891) (meaning t m 2901) (meaning t m 3412) source

theorem rule28439 (p2027 p2156 p2274 p2396 p2696 p3370 p3425 p3659 p4418 p4668 p5049 : Prop) (h : (¬ p3659) ∨ (¬ p2274) ∨ (¬ p4418) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p2396) ∨ (¬ p3425) ∨ (¬ p2156) ∨ (¬ p3370) ∨ (¬ p5049)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (¬ p3370) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4418) ∨ (¬ p4668) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial28439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory17695 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28439 (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2696) (meaning t m 3370) (meaning t m 3425) (meaning t m 3659) (meaning t m 4418) (meaning t m 4668) (meaning t m 5049) source

theorem rule28440 (p2881 p3569 p3644 : Prop) (h : (¬ p2881) ∨ (¬ p3569) ∨ (¬ p3644)) : (¬ p2881) ∨ (¬ p3569) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial28440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory17696 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28440 (meaning t m 2881) (meaning t m 3569) (meaning t m 3644) source

theorem rule28444 (p1987 p2545 p2751 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p1987) ∨ p2751 ∨ p2545) : (¬ p1987) ∨ (p2545) ∨ (p2751) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial28444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2545) ∨ (meaning t m 2751) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory17700 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule28444 (meaning t m 1987) (meaning t m 2545) (meaning t m 2751) (meaning t m 4111) source

theorem rule28449 (p1979 p2027 p2766 p2860 p3692 p3694 p3952 : Prop) (h : p2027 ∨ (¬ p3694) ∨ p2766 ∨ (¬ p1979) ∨ (¬ p3952) ∨ (¬ p3692) ∨ (¬ p2860)) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p2860) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial28449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory17705 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule28449 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 2860) (meaning t m 3692) (meaning t m 3694) (meaning t m 3952) source

theorem rule28450 (p1979 p2027 p2156 p2766 p3692 p3952 p4120 : Prop) (h : (¬ p3692) ∨ (¬ p3952) ∨ (¬ p1979) ∨ p2027 ∨ p2766 ∨ (¬ p4120) ∨ (¬ p2156)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2156) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial28450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory17706 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule28450 (meaning t m 1979) (meaning t m 2027) (meaning t m 2156) (meaning t m 2766) (meaning t m 3692) (meaning t m 3952) (meaning t m 4120) source

theorem rule28456 (p2027 p2245 p2657 p2727 p2749 p3093 p4870 : Prop) (h : (¬ p2245) ∨ p2027 ∨ (¬ p4870) ∨ (¬ p3093) ∨ (¬ p2749) ∨ (¬ p2727) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3093) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial28456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory17712 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4)
  exact rule28456 (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) (meaning t m 3093) (meaning t m 4870) source

theorem rule28458 (p2010 p2027 p2247 p2437 p2688 p3232 p3359 p3830 : Prop) (h : p2688 ∨ (¬ p3359) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3232) ∨ (¬ p3830) ∨ (¬ p2010) ∨ (¬ p2437)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2437) ∨ (p2688) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830) := by
  classical
  tauto

theorem initial28458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3830)) := by
  have source := ElevenTheory.theory17714 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule28458 (meaning t m 2010) (meaning t m 2027) (meaning t m 2247) (meaning t m 2437) (meaning t m 2688) (meaning t m 3232) (meaning t m 3359) (meaning t m 3830) source

theorem rule28461 (p2027 p3005 p4311 p4315 p5569 p5740 : Prop) (h : (¬ p5569) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p4311) ∨ (¬ p5740) ∨ (¬ p4315)) : (p2027) ∨ (¬ p3005) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p5569) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial28461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5569)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory17717 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 10) (m.theta 5 8)
  exact rule28461 (meaning t m 2027) (meaning t m 3005) (meaning t m 4311) (meaning t m 4315) (meaning t m 5569) (meaning t m 5740) source

theorem rule28466 (p2027 p2341 p2589 p3553 p3984 p4067 p4717 p5201 : Prop) (h : p2027 ∨ (¬ p4717) ∨ (¬ p2341) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p2589) ∨ (¬ p5201) ∨ (¬ p3984)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3553) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial28466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory17722 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 8)
  exact rule28466 (meaning t m 2027) (meaning t m 2341) (meaning t m 2589) (meaning t m 3553) (meaning t m 3984) (meaning t m 4067) (meaning t m 4717) (meaning t m 5201) source

theorem rule28469 (p1977 p2027 p2331 p2764 p3292 p4154 p5284 : Prop) (h : p2764 ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p5284) ∨ (¬ p1977) ∨ (¬ p3292)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2764) ∨ (¬ p3292) ∨ (¬ p4154) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17725 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 9) (m.theta 9 10)
  exact rule28469 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2764) (meaning t m 3292) (meaning t m 4154) (meaning t m 5284) source

theorem rule28472 (p2022 p3551 p3578 p4905 : Prop) (h : p3578 ∨ (¬ p3551) ∨ p4905 ∨ (¬ p2022)) : (¬ p2022) ∨ (¬ p3551) ∨ (p3578) ∨ (p4905) := by
  classical
  tauto

theorem initial28472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (¬ (meaning t m 3551)) ∨ (meaning t m 3578) ∨ (meaning t m 4905) := by
  have source := ElevenTheory.theory17728 t (m.theta 0 7) (m.theta 5 8) (m.theta 7 8)
  exact rule28472 (meaning t m 2022) (meaning t m 3551) (meaning t m 3578) (meaning t m 4905) source

theorem rule28473 (p1983 p2027 p2449 p2696 p2699 p2707 p2743 p3589 p4325 : Prop) (h : p2699 ∨ (¬ p4325) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2696) ∨ (¬ p3589) ∨ (¬ p2707) ∨ (¬ p2743)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3589) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial28473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory17729 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule28473 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2696) (meaning t m 2699) (meaning t m 2707) (meaning t m 2743) (meaning t m 3589) (meaning t m 4325) source

theorem rule28474 (p1990 p2027 p2241 p2284 p2699 p2891 p4320 p4365 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p1990) ∨ (¬ p4365) ∨ (¬ p4320) ∨ (¬ p2891)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p4320) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial28474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory17730 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule28474 (meaning t m 1990) (meaning t m 2027) (meaning t m 2241) (meaning t m 2284) (meaning t m 2699) (meaning t m 2891) (meaning t m 4320) (meaning t m 4365) source

theorem rule28475 (p3486 p4173 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p4173) ∨ p3486) : (p3486) ∨ (¬ p4173) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial28475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3486) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory17731 (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule28475 (meaning t m 3486) (meaning t m 4173) (meaning t m 4204) source

theorem rule28477 (p2027 p2241 p2641 p3323 p3540 p3644 p4330 p4348 p5193 : Prop) (h : (¬ p2641) ∨ (¬ p3323) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial28477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17733 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule28477 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3323) (meaning t m 3540) (meaning t m 3644) (meaning t m 4330) (meaning t m 4348) (meaning t m 5193) source

theorem rule28481 (p2027 p2922 p3193 p3246 p4264 p4277 p5295 : Prop) (h : (¬ p4264) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p5295) ∨ (¬ p3246) ∨ (¬ p3193) ∨ (¬ p4277)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p4264) ∨ (¬ p4277) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial28481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4264)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory17737 t (m.theta 0 9) (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule28481 (meaning t m 2027) (meaning t m 2922) (meaning t m 3193) (meaning t m 3246) (meaning t m 4264) (meaning t m 4277) (meaning t m 5295) source

theorem rule28485 (p2509 p3487 p4256 : Prop) (h : (¬ p2509) ∨ (¬ p3487) ∨ p4256) : (¬ p2509) ∨ (¬ p3487) ∨ (p4256) := by
  classical
  tauto

theorem initial28485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3487)) ∨ (meaning t m 4256) := by
  have source := ElevenTheory.theory17741 (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule28485 (meaning t m 2509) (meaning t m 3487) (meaning t m 4256) source

theorem rule28490 (p1982 p2027 p2114 p2363 p2518 p3379 p3954 p4157 : Prop) (h : (¬ p3954) ∨ (¬ p4157) ∨ (¬ p2518) ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2114 ∨ p2027 ∨ (¬ p3379)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial28490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory17746 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule28490 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2363) (meaning t m 2518) (meaning t m 3379) (meaning t m 3954) (meaning t m 4157) source

theorem rule28494 (p2027 p2191 p2774 p2819 p3555 p3692 p3979 p4733 p5122 : Prop) (h : (¬ p3979) ∨ (¬ p2819) ∨ (¬ p2774) ∨ (¬ p2191) ∨ (¬ p4733) ∨ (¬ p3555) ∨ (¬ p5122) ∨ (¬ p3692) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial28494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory17750 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule28494 (meaning t m 2027) (meaning t m 2191) (meaning t m 2774) (meaning t m 2819) (meaning t m 3555) (meaning t m 3692) (meaning t m 3979) (meaning t m 4733) (meaning t m 5122) source

theorem rule28499 (p2493 p3016 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2493) ∨ p3016) : (¬ p2493) ∨ (p3016) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial28499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (meaning t m 3016) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory17755 (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule28499 (meaning t m 2493) (meaning t m 3016) (meaning t m 4116) source

theorem rule28501 (p2027 p2252 p2476 p2534 p2655 p2750 p3146 p3399 p3527 p3954 p4905 : Prop) (h : p2027 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4905) ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p3146) ∨ (¬ p2655) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3146) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial28501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory17757 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28501 (meaning t m 2027) (meaning t m 2252) (meaning t m 2476) (meaning t m 2534) (meaning t m 2655) (meaning t m 2750) (meaning t m 3146) (meaning t m 3399) (meaning t m 3527) (meaning t m 3954) (meaning t m 4905) source

theorem rule28502 (p2027 p2532 p3105 p3694 p4348 p4905 : Prop) (h : p2027 ∨ (¬ p4905) ∨ (¬ p3694) ∨ (¬ p2532) ∨ (¬ p4348) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial28502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory17758 t (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule28502 (meaning t m 2027) (meaning t m 2532) (meaning t m 3105) (meaning t m 3694) (meaning t m 4348) (meaning t m 4905) source

theorem rule28508 (p2008 p2027 p2737 p3365 p3471 p3474 p3583 : Prop) (h : p2027 ∨ (¬ p2008) ∨ (¬ p2737) ∨ (¬ p3471) ∨ (¬ p3365) ∨ p3474 ∨ (¬ p3583)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (p3474) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial28508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory17764 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule28508 (meaning t m 2008) (meaning t m 2027) (meaning t m 2737) (meaning t m 3365) (meaning t m 3471) (meaning t m 3474) (meaning t m 3583) source

theorem rule28509 (p2027 p2156 p3115 p3588 p3952 p3954 p4106 p4278 p4521 p4621 p5045 : Prop) (h : (¬ p3588) ∨ (¬ p4278) ∨ (¬ p3954) ∨ (¬ p3115) ∨ (¬ p4621) ∨ (¬ p2156) ∨ (¬ p4106) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4521) ∨ (¬ p5045)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3115) ∨ (¬ p3588) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4278) ∨ (¬ p4521) ∨ (¬ p4621) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial28509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory17765 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9)
  exact rule28509 (meaning t m 2027) (meaning t m 2156) (meaning t m 3115) (meaning t m 3588) (meaning t m 3952) (meaning t m 3954) (meaning t m 4106) (meaning t m 4278) (meaning t m 4521) (meaning t m 4621) (meaning t m 5045) source

theorem rule28511 (p2027 p2563 p2668 p3745 p4235 p4275 p4405 : Prop) (h : (¬ p2668) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p4275) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p3745)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3745) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial28511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory17767 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule28511 (meaning t m 2027) (meaning t m 2563) (meaning t m 2668) (meaning t m 3745) (meaning t m 4235) (meaning t m 4275) (meaning t m 4405) source

theorem rule28512 (p2027 p2417 p3051 p4032 p4382 p4647 : Prop) (h : (¬ p4032) ∨ (¬ p4647) ∨ (¬ p3051) ∨ (¬ p4382) ∨ p2027 ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial28512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory17768 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule28512 (meaning t m 2027) (meaning t m 2417) (meaning t m 3051) (meaning t m 4032) (meaning t m 4382) (meaning t m 4647) source

theorem rule28515 (p1985 p2027 p2138 p2177 p2307 p2786 p3474 p3570 : Prop) (h : (¬ p2177) ∨ (¬ p2138) ∨ (¬ p2786) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p2307) ∨ p3474 ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (p3474) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial28515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory17771 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule28515 (meaning t m 1985) (meaning t m 2027) (meaning t m 2138) (meaning t m 2177) (meaning t m 2307) (meaning t m 2786) (meaning t m 3474) (meaning t m 3570) source

theorem rule28516 (p2187 p3550 p3570 p4204 : Prop) (h : (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial28516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory17772 (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule28516 (meaning t m 2187) (meaning t m 3550) (meaning t m 3570) (meaning t m 4204) source

theorem rule28520 (p2027 p2248 p2901 p2946 p3193 p3452 p4129 p4425 p4826 : Prop) (h : (¬ p4425) ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p3193) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p4129) ∨ (¬ p3452) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial28520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory17776 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule28520 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3193) (meaning t m 3452) (meaning t m 4129) (meaning t m 4425) (meaning t m 4826) source

theorem rule28521 (p2027 p2122 p2132 p2476 p3083 p3097 p3574 p3589 p3985 p4718 p5193 : Prop) (h : (¬ p2122) ∨ (¬ p3985) ∨ (¬ p3589) ∨ (¬ p5193) ∨ (¬ p3574) ∨ (¬ p2132) ∨ (¬ p4718) ∨ (¬ p3083) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2476)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p3589) ∨ (¬ p3985) ∨ (¬ p4718) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial28521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4718)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17777 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule28521 (meaning t m 2027) (meaning t m 2122) (meaning t m 2132) (meaning t m 2476) (meaning t m 3083) (meaning t m 3097) (meaning t m 3574) (meaning t m 3589) (meaning t m 3985) (meaning t m 4718) (meaning t m 5193) source

theorem rule28523 (p2122 p2274 p4185 : Prop) (h : (¬ p4185) ∨ (¬ p2274) ∨ p2122) : (p2122) ∨ (¬ p2274) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial28523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory17779 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule28523 (meaning t m 2122) (meaning t m 2274) (meaning t m 4185) source

theorem rule28525 (p2027 p2210 p2254 p2963 p2972 p3324 p3680 p5123 p5580 : Prop) (h : (¬ p2963) ∨ (¬ p5580) ∨ (¬ p3324) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p5123) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p2972)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p2972) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial28525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory17781 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule28525 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2963) (meaning t m 2972) (meaning t m 3324) (meaning t m 3680) (meaning t m 5123) (meaning t m 5580) source

theorem rule28531 (p2011 p2027 p2241 p2699 p2992 p3506 p4322 p5038 : Prop) (h : p2699 ∨ (¬ p4322) ∨ (¬ p2992) ∨ (¬ p2011) ∨ p2027 ∨ (¬ p5038) ∨ (¬ p2241) ∨ (¬ p3506)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p5038) := by
  classical
  tauto

theorem initial28531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5038)) := by
  have source := ElevenTheory.theory17787 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule28531 (meaning t m 2011) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2992) (meaning t m 3506) (meaning t m 4322) (meaning t m 5038) source

theorem rule28536 (p2027 p2619 p3051 p4120 p4235 p4885 : Prop) (h : (¬ p2619) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p4885) ∨ (¬ p4235) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial28536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory17792 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule28536 (meaning t m 2027) (meaning t m 2619) (meaning t m 3051) (meaning t m 4120) (meaning t m 4235) (meaning t m 4885) source

theorem rule28544 (p2027 p2573 p2663 p2952 p3574 p4701 : Prop) (h : p2027 ∨ (¬ p2952) ∨ (¬ p3574) ∨ (¬ p2663) ∨ (¬ p4701) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3574) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial28544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory17800 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule28544 (meaning t m 2027) (meaning t m 2573) (meaning t m 2663) (meaning t m 2952) (meaning t m 3574) (meaning t m 4701) source

theorem rule28547 (p1998 p2027 p2220 p2622 p2951 p3136 p3146 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2622 ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2951) ∨ (¬ p3136)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2220) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial28547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory17803 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28547 (meaning t m 1998) (meaning t m 2027) (meaning t m 2220) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) (meaning t m 3146) (meaning t m 4348) source

theorem rule28550 (p1987 p2027 p2169 p2651 p2810 p2963 p3324 : Prop) (h : (¬ p2651) ∨ p2169 ∨ (¬ p2963) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p3324)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial28550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory17806 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule28550 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2651) (meaning t m 2810) (meaning t m 2963) (meaning t m 3324) source

theorem rule28556 (p2027 p2104 p2264 p2807 p4117 p4807 : Prop) (h : (¬ p2807) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4807) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p4807) := by
  classical
  tauto

theorem initial28556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4807)) := by
  have source := ElevenTheory.theory17812 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 7) (m.theta 7 8)
  exact rule28556 (meaning t m 2027) (meaning t m 2104) (meaning t m 2264) (meaning t m 2807) (meaning t m 4117) (meaning t m 4807) source

theorem rule28557 (p2027 p2192 p3146 p4261 p4492 p4507 : Prop) (h : (¬ p4492) ∨ (¬ p3146) ∨ (¬ p2192) ∨ (¬ p4507) ∨ p2027 ∨ (¬ p4261)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3146) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial28557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory17813 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule28557 (meaning t m 2027) (meaning t m 2192) (meaning t m 3146) (meaning t m 4261) (meaning t m 4492) (meaning t m 4507) source

theorem rule28560 (p2027 p2406 p2589 p2655 p2807 p4116 p4652 : Prop) (h : p2027 ∨ (¬ p2406) ∨ (¬ p4652) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p2655) ∨ (¬ p4116)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4116) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial28560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory17816 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule28560 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2655) (meaning t m 2807) (meaning t m 4116) (meaning t m 4652) source

theorem rule28562 (p3553 p3570 p4333 : Prop) (h : (¬ p4333) ∨ (¬ p3553) ∨ p3570) : (¬ p3553) ∨ (p3570) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial28562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3553)) ∨ (meaning t m 3570) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory17818 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28562 (meaning t m 3553) (meaning t m 3570) (meaning t m 4333) source

theorem rule28575 (p1984 p2027 p2247 p2545 p2797 p2810 p4154 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p2797)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial28575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory17831 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule28575 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 4154) source

theorem rule28577 (p2027 p2138 p3471 p4173 p4243 p4344 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p4173) ∨ (¬ p2138) ∨ (¬ p4344) ∨ (¬ p3471) ∨ (¬ p4243)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4344) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory17833 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule28577 (meaning t m 2027) (meaning t m 2138) (meaning t m 3471) (meaning t m 4173) (meaning t m 4243) (meaning t m 4344) (meaning t m 4558) source

theorem rule28578 (p2027 p2476 p2936 p3389 p3527 p4383 : Prop) (h : (¬ p3527) ∨ (¬ p3389) ∨ (¬ p2936) ∨ (¬ p4383) ∨ p2027 ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2936) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial28578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory17834 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule28578 (meaning t m 2027) (meaning t m 2476) (meaning t m 2936) (meaning t m 3389) (meaning t m 3527) (meaning t m 4383) source

theorem rule28580 (p2027 p2104 p2187 p2774 p4857 p4889 : Prop) (h : (¬ p2187) ∨ (¬ p2774) ∨ (¬ p4857) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p4889)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p4857) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial28580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4857)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory17836 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8)
  exact rule28580 (meaning t m 2027) (meaning t m 2104) (meaning t m 2187) (meaning t m 2774) (meaning t m 4857) (meaning t m 4889) source

theorem rule28581 (p2027 p2177 p2553 p2573 p3954 p4242 p4324 p4666 p4805 p5190 : Prop) (h : (¬ p2177) ∨ (¬ p4666) ∨ (¬ p3954) ∨ (¬ p2573) ∨ (¬ p5190) ∨ (¬ p4324) ∨ (¬ p4805) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4324) ∨ (¬ p4666) ∨ (¬ p4805) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial28581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory17837 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28581 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 3954) (meaning t m 4242) (meaning t m 4324) (meaning t m 4666) (meaning t m 4805) (meaning t m 5190) source

theorem rule28582 (p2027 p2743 p2810 p3537 p4967 p5011 : Prop) (h : (¬ p3537) ∨ (¬ p4967) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p5011) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial28582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory17838 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8)
  exact rule28582 (meaning t m 2027) (meaning t m 2743) (meaning t m 2810) (meaning t m 3537) (meaning t m 4967) (meaning t m 5011) source

theorem rule28585 (p1990 p2027 p2545 p2641 p2668 p3989 p4111 : Prop) (h : (¬ p2668) ∨ (¬ p4111) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p1990) ∨ p2545 ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial28585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory17841 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule28585 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 2668) (meaning t m 3989) (meaning t m 4111) source

theorem rule28587 (p2027 p2295 p3019 p3189 p3549 p4245 p5011 : Prop) (h : (¬ p5011) ∨ (¬ p3019) ∨ (¬ p4245) ∨ (¬ p2295) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p3549)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3019) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial28587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory17843 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule28587 (meaning t m 2027) (meaning t m 2295) (meaning t m 3019) (meaning t m 3189) (meaning t m 3549) (meaning t m 4245) (meaning t m 5011) source

theorem rule28591 (p2027 p2417 p2437 p3686 p4324 p4750 : Prop) (h : (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4750) ∨ (¬ p4324) ∨ (¬ p2417) ∨ p2027) : (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4324) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial28591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory17847 t (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule28591 (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 3686) (meaning t m 4324) (meaning t m 4750) source

theorem rule28593 (p1987 p2027 p3146 p3661 p3982 p4118 p4315 p5568 : Prop) (h : p2027 ∨ (¬ p4315) ∨ (¬ p4118) ∨ (¬ p1987) ∨ (¬ p3661) ∨ p3982 ∨ (¬ p3146) ∨ (¬ p5568)) : (¬ p1987) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (p3982) ∨ (¬ p4118) ∨ (¬ p4315) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial28593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory17849 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule28593 (meaning t m 1987) (meaning t m 2027) (meaning t m 3146) (meaning t m 3661) (meaning t m 3982) (meaning t m 4118) (meaning t m 4315) (meaning t m 5568) source

theorem rule28595 (p2027 p2122 p2143 p3097 p3985 p4032 p5043 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p5043) ∨ (¬ p4032) ∨ (¬ p3985) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2143) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4032) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial28595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory17851 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule28595 (meaning t m 2027) (meaning t m 2122) (meaning t m 2143) (meaning t m 3097) (meaning t m 3985) (meaning t m 4032) (meaning t m 5043) source

theorem rule28597 (p1990 p2027 p2156 p2166 p2938 p4120 p4244 p4418 : Prop) (h : (¬ p1990) ∨ (¬ p4244) ∨ (¬ p2166) ∨ (¬ p4418) ∨ (¬ p2156) ∨ (¬ p4120) ∨ p2027 ∨ p2938) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (p2938) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial28597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory17853 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule28597 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 2938) (meaning t m 4120) (meaning t m 4244) (meaning t m 4418) source

theorem rule28601 (p1986 p2027 p2230 p2476 p2534 p2766 p3684 : Prop) (h : (¬ p2534) ∨ (¬ p1986) ∨ p2027 ∨ p2766 ∨ (¬ p3684) ∨ (¬ p2230) ∨ (¬ p2476)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial28601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory17857 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule28601 (meaning t m 1986) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2534) (meaning t m 2766) (meaning t m 3684) source

theorem rule28605 (p1990 p2027 p2169 p2191 p2192 p2363 p3857 p4115 : Prop) (h : (¬ p2192) ∨ p2027 ∨ (¬ p2363) ∨ p2169 ∨ (¬ p2191) ∨ (¬ p1990) ∨ (¬ p3857) ∨ (¬ p4115)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4115) := by
  classical
  tauto

theorem initial28605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4115)) := by
  have source := ElevenTheory.theory17861 t (m.theta 0 8) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule28605 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2191) (meaning t m 2192) (meaning t m 2363) (meaning t m 3857) (meaning t m 4115) source

theorem rule28606 (p2027 p2187 p3093 p3860 p4514 p4993 : Prop) (h : (¬ p4514) ∨ (¬ p4993) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p3093) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial28606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4514)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory17862 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8)
  exact rule28606 (meaning t m 2027) (meaning t m 2187) (meaning t m 3093) (meaning t m 3860) (meaning t m 4514) (meaning t m 4993) source

theorem rule28608 (p3695 p4705 p4906 : Prop) (h : (¬ p4705) ∨ (¬ p3695) ∨ p4906) : (¬ p3695) ∨ (¬ p4705) ∨ (p4906) := by
  classical
  tauto

theorem initial28608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4705)) ∨ (meaning t m 4906) := by
  have source := ElevenTheory.theory17864 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 5)
  exact rule28608 (meaning t m 3695) (meaning t m 4705) (meaning t m 4906) source

theorem rule28611 (p2785 p3204 p4024 : Prop) (h : (¬ p4024) ∨ (¬ p3204) ∨ p2785) : (p2785) ∨ (¬ p3204) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial28611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2785) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory17867 (m.theta 0 6) (m.theta 1 6) (m.theta 2 6)
  exact rule28611 (meaning t m 2785) (meaning t m 3204) (meaning t m 4024) source

theorem rule28612 (p2027 p2177 p2254 p2608 p3201 p3367 p3414 p3553 p4276 : Prop) (h : (¬ p2254) ∨ (¬ p3367) ∨ (¬ p3201) ∨ (¬ p2177) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4276) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial28612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory17868 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule28612 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2608) (meaning t m 3201) (meaning t m 3367) (meaning t m 3414) (meaning t m 3553) (meaning t m 4276) source

theorem rule28613 (p2018 p2027 p2088 p2437 p2482 p2545 p3540 p4340 : Prop) (h : (¬ p4340) ∨ (¬ p2018) ∨ p2545 ∨ (¬ p2437) ∨ p2027 ∨ (¬ p2482) ∨ (¬ p3540) ∨ (¬ p2088)) : (¬ p2018) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2437) ∨ (¬ p2482) ∨ (p2545) ∨ (¬ p3540) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial28613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2482)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory17869 t (m.theta 0 4) (m.theta 0 8) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 8 9)
  exact rule28613 (meaning t m 2018) (meaning t m 2027) (meaning t m 2088) (meaning t m 2437) (meaning t m 2482) (meaning t m 2545) (meaning t m 3540) (meaning t m 4340) source

theorem rule28615 (p2027 p3055 p3516 p3819 p4324 p4357 p4749 : Prop) (h : (¬ p3516) ∨ (¬ p3819) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p3055) ∨ (¬ p4749) ∨ (¬ p4357)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial28615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory17871 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9)
  exact rule28615 (meaning t m 2027) (meaning t m 3055) (meaning t m 3516) (meaning t m 3819) (meaning t m 4324) (meaning t m 4357) (meaning t m 4749) source

theorem rule28616 (p3874 p4045 p5160 : Prop) (h : (¬ p4045) ∨ (¬ p3874) ∨ p5160) : (¬ p3874) ∨ (¬ p4045) ∨ (p5160) := by
  classical
  tauto

theorem initial28616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4045)) ∨ (meaning t m 5160) := by
  have source := ElevenTheory.theory17872 (m.theta 2 4) (m.theta 4 8) (m.theta 4 9)
  exact rule28616 (meaning t m 3874) (meaning t m 4045) (meaning t m 5160) source

theorem rule28620 (p1982 p2027 p2098 p2136 p2363 p2860 p3474 p3646 p4326 : Prop) (h : p2027 ∨ (¬ p3646) ∨ (¬ p1982) ∨ (¬ p2136) ∨ (¬ p2363) ∨ (¬ p4326) ∨ (¬ p2098) ∨ p3474 ∨ (¬ p2860)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2136) ∨ (¬ p2363) ∨ (¬ p2860) ∨ (p3474) ∨ (¬ p3646) ∨ (¬ p4326) := by
  classical
  tauto

theorem initial28620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4326)) := by
  have source := ElevenTheory.theory17876 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule28620 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2136) (meaning t m 2363) (meaning t m 2860) (meaning t m 3474) (meaning t m 3646) (meaning t m 4326) source

theorem rule28622 (p2027 p2088 p2484 p3266 p4045 p4425 : Prop) (h : (¬ p4045) ∨ (¬ p2088) ∨ (¬ p2484) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3266)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2484) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial28622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2484)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory17878 t (m.theta 0 8) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28622 (meaning t m 2027) (meaning t m 2088) (meaning t m 2484) (meaning t m 3266) (meaning t m 4045) (meaning t m 4425) source

theorem rule28624 (p2027 p2387 p2459 p2518 p3204 p3379 p3954 p4347 p4420 p4870 : Prop) (h : (¬ p4870) ∨ (¬ p3204) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p2387) ∨ (¬ p4420) ∨ (¬ p2459) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (¬ p3204) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4420) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial28624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory17880 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28624 (meaning t m 2027) (meaning t m 2387) (meaning t m 2459) (meaning t m 2518) (meaning t m 3204) (meaning t m 3379) (meaning t m 3954) (meaning t m 4347) (meaning t m 4420) (meaning t m 4870) source

theorem rule28634 (p2027 p2662 p2810 p3136 p3540 p4241 p4644 : Prop) (h : (¬ p4644) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p4241) ∨ (¬ p3540) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3540) ∨ (¬ p4241) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial28634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory17890 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule28634 (meaning t m 2027) (meaning t m 2662) (meaning t m 2810) (meaning t m 3136) (meaning t m 3540) (meaning t m 4241) (meaning t m 4644) source

theorem rule28638 (p2995 p3136 p3572 : Prop) (h : (¬ p2995) ∨ (¬ p3136) ∨ (¬ p3572)) : (¬ p2995) ∨ (¬ p3136) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial28638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory17894 (m.theta 2 3) (m.theta 3 5) (m.theta 3 7)
  exact rule28638 (meaning t m 2995) (meaning t m 3136) (meaning t m 3572) source

theorem rule28644 (p2027 p2220 p2249 p2656 p2727 p3146 p3292 p3461 p4399 p4604 p5284 : Prop) (h : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p5284) ∨ (¬ p4399) ∨ (¬ p3461) ∨ (¬ p3292) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p4604) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3146) ∨ (¬ p3292) ∨ (¬ p3461) ∨ (¬ p4399) ∨ (¬ p4604) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17900 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28644 (meaning t m 2027) (meaning t m 2220) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 3146) (meaning t m 3292) (meaning t m 3461) (meaning t m 4399) (meaning t m 4604) (meaning t m 5284) source

theorem rule28649 (p2027 p2252 p2396 p2750 p3292 p3399 p3547 p3680 p3951 p3954 p5284 : Prop) (h : (¬ p3292) ∨ (¬ p3680) ∨ (¬ p2252) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p3951) ∨ (¬ p3547) ∨ (¬ p3399) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3680) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17905 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule28649 (meaning t m 2027) (meaning t m 2252) (meaning t m 2396) (meaning t m 2750) (meaning t m 3292) (meaning t m 3399) (meaning t m 3547) (meaning t m 3680) (meaning t m 3951) (meaning t m 3954) (meaning t m 5284) source

theorem rule28650 (p2027 p2598 p2780 p3016 p4342 p4750 : Prop) (h : (¬ p2780) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3016) ∨ (¬ p4342)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial28650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory17906 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule28650 (meaning t m 2027) (meaning t m 2598) (meaning t m 2780) (meaning t m 3016) (meaning t m 4342) (meaning t m 4750) source

theorem rule28651 (p2027 p2098 p2743 p2963 p3324 p3361 p3609 p4348 p4503 p4737 : Prop) (h : (¬ p3324) ∨ (¬ p4503) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p4348) ∨ (¬ p3361) ∨ (¬ p2963) ∨ (¬ p2098) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial28651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory17907 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28651 (meaning t m 2027) (meaning t m 2098) (meaning t m 2743) (meaning t m 2963) (meaning t m 3324) (meaning t m 3361) (meaning t m 3609) (meaning t m 4348) (meaning t m 4503) (meaning t m 4737) source

theorem rule28653 (p2027 p3631 p3687 p3688 p4324 p4357 p4842 : Prop) (h : (¬ p4324) ∨ (¬ p3687) ∨ (¬ p4842) ∨ (¬ p3688) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p4357)) : (p2027) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3688) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial28653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory17909 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7) (m.theta 7 9)
  exact rule28653 (meaning t m 2027) (meaning t m 3631) (meaning t m 3687) (meaning t m 3688) (meaning t m 4324) (meaning t m 4357) (meaning t m 4842) source

theorem rule28654 (p2027 p2839 p2860 p4242 p4507 p4740 : Prop) (h : (¬ p2839) ∨ (¬ p4740) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4242) ∨ (¬ p4507) ∨ (¬ p4740) := by
  classical
  tauto

theorem initial28654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4740)) := by
  have source := ElevenTheory.theory17910 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8)
  exact rule28654 (meaning t m 2027) (meaning t m 2839) (meaning t m 2860) (meaning t m 4242) (meaning t m 4507) (meaning t m 4740) source

theorem rule28656 (p2006 p2027 p2764 p2901 p4208 p4244 p4322 : Prop) (h : p2027 ∨ (¬ p2006) ∨ (¬ p4244) ∨ (¬ p2901) ∨ p2764 ∨ (¬ p4208) ∨ (¬ p4322)) : (¬ p2006) ∨ (p2027) ∨ (p2764) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4244) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial28656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory17912 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule28656 (meaning t m 2006) (meaning t m 2027) (meaning t m 2764) (meaning t m 2901) (meaning t m 4208) (meaning t m 4244) (meaning t m 4322) source

theorem rule28657 (p1988 p2027 p2441 p3146 p3222 p3276 p3347 p3578 p3584 p3685 p3759 p4253 p4340 p4715 p5503 : Prop) (h : (¬ p3347) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3759) ∨ (¬ p1988) ∨ (¬ p4715) ∨ (¬ p3584) ∨ (¬ p2441) ∨ (¬ p5503) ∨ (¬ p3146) ∨ p3578 ∨ (¬ p4340) ∨ (¬ p3685) ∨ p2027 ∨ (¬ p4253)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2441) ∨ (¬ p3146) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3347) ∨ (p3578) ∨ (¬ p3584) ∨ (¬ p3685) ∨ (¬ p3759) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p4715) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial28657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3347)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory17913 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 2 8) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule28657 (meaning t m 1988) (meaning t m 2027) (meaning t m 2441) (meaning t m 3146) (meaning t m 3222) (meaning t m 3276) (meaning t m 3347) (meaning t m 3578) (meaning t m 3584) (meaning t m 3685) (meaning t m 3759) (meaning t m 4253) (meaning t m 4340) (meaning t m 4715) (meaning t m 5503) source

theorem rule28659 (p2933 p3817 p4278 : Prop) (h : (¬ p2933) ∨ (¬ p3817) ∨ p4278) : (¬ p2933) ∨ (¬ p3817) ∨ (p4278) := by
  classical
  tauto

theorem initial28659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3817)) ∨ (meaning t m 4278) := by
  have source := ElevenTheory.theory17915 (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule28659 (meaning t m 2933) (meaning t m 3817) (meaning t m 4278) source

theorem rule28661 (p2027 p2252 p2352 p2363 p2573 p2741 p3292 p3519 p3680 p4376 p5059 p5284 : Prop) (h : (¬ p2363) ∨ (¬ p5059) ∨ (¬ p3680) ∨ (¬ p3519) ∨ (¬ p2352) ∨ (¬ p4376) ∨ (¬ p2573) ∨ (¬ p3292) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2741) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2741) ∨ (¬ p3292) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4376) ∨ (¬ p5059) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17917 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule28661 (meaning t m 2027) (meaning t m 2252) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2741) (meaning t m 3292) (meaning t m 3519) (meaning t m 3680) (meaning t m 4376) (meaning t m 5059) (meaning t m 5284) source

theorem rule28666 (p1998 p2027 p2156 p2699 p2881 p2891 p4172 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p2881) ∨ (¬ p2156) ∨ p2699 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p4172) ∨ (¬ p2891)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2156) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4172) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial28666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory17922 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule28666 (meaning t m 1998) (meaning t m 2027) (meaning t m 2156) (meaning t m 2699) (meaning t m 2881) (meaning t m 2891) (meaning t m 4172) (meaning t m 4173) source

theorem rule28667 (p2027 p2132 p2166 p2743 p3146 p3361 p3414 p3947 p4418 p4669 p4737 : Prop) (h : (¬ p4669) ∨ (¬ p3361) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3414) ∨ (¬ p2132) ∨ (¬ p4418) ∨ (¬ p3947) ∨ (¬ p4737) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4418) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial28667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory17923 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28667 (meaning t m 2027) (meaning t m 2132) (meaning t m 2166) (meaning t m 2743) (meaning t m 3146) (meaning t m 3361) (meaning t m 3414) (meaning t m 3947) (meaning t m 4418) (meaning t m 4669) (meaning t m 4737) source

theorem rule28668 (p3292 p3414 p4429 : Prop) (h : (¬ p3414) ∨ (¬ p4429) ∨ p3292) : (p3292) ∨ (¬ p3414) ∨ (¬ p4429) := by
  classical
  tauto

theorem initial28668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3292) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4429)) := by
  have source := ElevenTheory.theory17924 (m.theta 0 3) (m.theta 3 7) (m.theta 3 9)
  exact rule28668 (meaning t m 3292) (meaning t m 3414) (meaning t m 4429) source

theorem rule28670 (p2027 p3201 p3868 p4067 p4194 p4391 p4753 : Prop) (h : (¬ p4194) ∨ (¬ p4753) ∨ (¬ p4067) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4391)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4067) ∨ (¬ p4194) ∨ (¬ p4391) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial28670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory17926 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10)
  exact rule28670 (meaning t m 2027) (meaning t m 3201) (meaning t m 3868) (meaning t m 4067) (meaning t m 4194) (meaning t m 4391) (meaning t m 4753) source

theorem rule28672 (p1976 p2027 p2589 p2764 p2850 p3905 p4425 p5160 : Prop) (h : p2764 ∨ (¬ p1976) ∨ (¬ p3905) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p5160) ∨ (¬ p4425)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial28672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory17928 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule28672 (meaning t m 1976) (meaning t m 2027) (meaning t m 2589) (meaning t m 2764) (meaning t m 2850) (meaning t m 3905) (meaning t m 4425) (meaning t m 5160) source

theorem rule28678 (p2027 p2230 p2246 p2440 p2531 p2608 p2663 p2744 p3083 p3548 p4366 p4902 : Prop) (h : p2027 ∨ (¬ p2440) ∨ (¬ p2230) ∨ (¬ p4366) ∨ (¬ p2663) ∨ (¬ p4902) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p2608) ∨ (¬ p2531)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial28678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory17934 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule28678 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2440) (meaning t m 2531) (meaning t m 2608) (meaning t m 2663) (meaning t m 2744) (meaning t m 3083) (meaning t m 3548) (meaning t m 4366) (meaning t m 4902) source

theorem rule28688 (p1976 p2027 p2313 p2633 p2778 p3553 p3931 p4260 : Prop) (h : (¬ p2313) ∨ (¬ p1976) ∨ p2633 ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4260) ∨ (¬ p2778) ∨ (¬ p3931)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2778) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial28688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory17944 t (m.theta 0 2) (m.theta 0 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule28688 (meaning t m 1976) (meaning t m 2027) (meaning t m 2313) (meaning t m 2633) (meaning t m 2778) (meaning t m 3553) (meaning t m 3931) (meaning t m 4260) source

theorem rule28692 (p2027 p2881 p3051 p3365 p3366 p3370 p3941 p4035 p4377 p5119 p5284 : Prop) (h : (¬ p3941) ∨ (¬ p4035) ∨ (¬ p2881) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p5284) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p4377) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial28692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory17948 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule28692 (meaning t m 2027) (meaning t m 2881) (meaning t m 3051) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 3941) (meaning t m 4035) (meaning t m 4377) (meaning t m 5119) (meaning t m 5284) source

theorem rule28703 (p4432 p4771 p5009 : Prop) (h : (¬ p4771) ∨ (¬ p4432) ∨ p5009) : (¬ p4432) ∨ (¬ p4771) ∨ (p5009) := by
  classical
  tauto

theorem initial28703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4771)) ∨ (meaning t m 5009) := by
  have source := ElevenTheory.theory17959 t (m.theta 3 8) (m.theta 4 8) (m.theta 6 8)
  exact rule28703 (meaning t m 4432) (meaning t m 4771) (meaning t m 5009) source

theorem rule28705 (p2027 p2274 p2313 p2383 p3324 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2383) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial28705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory17961 t (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28705 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2383) (meaning t m 3324) (meaning t m 4564) source

theorem rule28707 (p2027 p2248 p2534 p2651 p3256 p3486 p3555 p3570 p4121 p4420 : Prop) (h : p2027 ∨ (¬ p3555) ∨ (¬ p2651) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p2248) ∨ (¬ p4420) ∨ (¬ p2534) ∨ (¬ p4121)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4121) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial28707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory17963 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28707 (meaning t m 2027) (meaning t m 2248) (meaning t m 2534) (meaning t m 2651) (meaning t m 3256) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4121) (meaning t m 4420) source

theorem rule28710 (p3989 p4358 p4428 : Prop) (h : (¬ p3989) ∨ (¬ p4428) ∨ p4358) : (¬ p3989) ∨ (p4358) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial28710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3989)) ∨ (meaning t m 4358) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory17966 (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule28710 (meaning t m 3989) (meaning t m 4358) (meaning t m 4428) source

theorem rule28711 (p2027 p2352 p2363 p2573 p2952 p3136 p3366 p3519 p4035 p4236 p4376 p5113 : Prop) (h : (¬ p3519) ∨ (¬ p3136) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p4236) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p5113) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial28711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory17967 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule28711 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2952) (meaning t m 3136) (meaning t m 3366) (meaning t m 3519) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 5113) source

theorem rule28714 (p2027 p2210 p2870 p4366 p4875 p4909 : Prop) (h : (¬ p4366) ∨ (¬ p4909) ∨ (¬ p2870) ∨ (¬ p2210) ∨ (¬ p4875) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2870) ∨ (¬ p4366) ∨ (¬ p4875) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial28714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4875)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory17970 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7)
  exact rule28714 (meaning t m 2027) (meaning t m 2210) (meaning t m 2870) (meaning t m 4366) (meaning t m 4875) (meaning t m 4909) source

theorem rule28715 (p2027 p2579 p2819 p3956 p4375 p4727 : Prop) (h : p2027 ∨ (¬ p4727) ∨ (¬ p2579) ∨ (¬ p4375) ∨ (¬ p3956) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial28715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory17971 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule28715 (meaning t m 2027) (meaning t m 2579) (meaning t m 2819) (meaning t m 3956) (meaning t m 4375) (meaning t m 4727) source

theorem rule28716 (p1976 p2027 p2579 p2764 p3422 p3905 p4425 p5160 : Prop) (h : p2764 ∨ (¬ p4425) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p3422) ∨ (¬ p2579) ∨ (¬ p5160) ∨ (¬ p3905)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2579) ∨ (p2764) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial28716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory17972 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule28716 (meaning t m 1976) (meaning t m 2027) (meaning t m 2579) (meaning t m 2764) (meaning t m 3422) (meaning t m 3905) (meaning t m 4425) (meaning t m 5160) source

theorem rule28718 (p2363 p4118 p4417 : Prop) (h : (¬ p4417) ∨ (¬ p2363) ∨ (¬ p4118)) : (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial28718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory17974 (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule28718 (meaning t m 2363) (meaning t m 4118) (meaning t m 4417) source

theorem rule28719 (p1988 p2027 p2363 p3266 p3449 p3591 p3818 p4318 : Prop) (h : p3818 ∨ (¬ p3266) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3449) ∨ (¬ p2363) ∨ (¬ p4318) ∨ (¬ p3591)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (p3818) ∨ (¬ p4318) := by
  classical
  tauto

theorem initial28719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 4318)) := by
  have source := ElevenTheory.theory17975 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule28719 (meaning t m 1988) (meaning t m 2027) (meaning t m 2363) (meaning t m 3266) (meaning t m 3449) (meaning t m 3591) (meaning t m 3818) (meaning t m 4318) source

theorem rule28722 (p1984 p2027 p2138 p2633 p2839 p3570 p3588 p3873 p4169 : Prop) (h : p2027 ∨ (¬ p2138) ∨ p2633 ∨ (¬ p1984) ∨ (¬ p3570) ∨ (¬ p3873) ∨ (¬ p3588) ∨ (¬ p2839) ∨ (¬ p4169)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (p2633) ∨ (¬ p2839) ∨ (¬ p3570) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial28722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory17978 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28722 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2633) (meaning t m 2839) (meaning t m 3570) (meaning t m 3588) (meaning t m 3873) (meaning t m 4169) source

theorem rule28723 (p1975 p2027 p2295 p2331 p2622 p2630 p2657 : Prop) (h : (¬ p2295) ∨ (¬ p2657) ∨ (¬ p2331) ∨ p2622 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2630)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) := by
  classical
  tauto

theorem initial28723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) := by
  have source := ElevenTheory.theory17979 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule28723 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) source

theorem rule28725 (p1997 p2027 p2406 p2764 p3347 p3540 p4278 p4381 : Prop) (h : (¬ p2406) ∨ (¬ p3347) ∨ (¬ p1997) ∨ (¬ p4381) ∨ p2764 ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (p2764) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial28725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory17981 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule28725 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2764) (meaning t m 3347) (meaning t m 3540) (meaning t m 4278) (meaning t m 4381) source

theorem rule28727 (p1990 p2027 p2563 p2611 p2946 p4117 p4272 p5433 : Prop) (h : (¬ p2946) ∨ (¬ p2563) ∨ p2611 ∨ p2027 ∨ (¬ p1990) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2611) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial28727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory17983 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 10) (m.theta 5 6)
  exact rule28727 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2611) (meaning t m 2946) (meaning t m 4117) (meaning t m 4272) (meaning t m 5433) source

theorem rule28728 (p1997 p2027 p2619 p2622 p2743 p2839 p3880 : Prop) (h : (¬ p2619) ∨ p2622 ∨ p2027 ∨ (¬ p2839) ∨ (¬ p2743) ∨ (¬ p1997) ∨ (¬ p3880)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2619) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial28728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory17984 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule28728 (meaning t m 1997) (meaning t m 2027) (meaning t m 2619) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3880) source

theorem rule28729 (p2027 p2891 p3136 p3572 p3691 p4155 p4960 : Prop) (h : p2027 ∨ (¬ p3136) ∨ (¬ p4960) ∨ (¬ p3572) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial28729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory17985 t (m.theta 0 7) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule28729 (meaning t m 2027) (meaning t m 2891) (meaning t m 3136) (meaning t m 3572) (meaning t m 3691) (meaning t m 4155) (meaning t m 4960) source

theorem rule28730 (p2027 p2122 p2839 p3549 p3953 p4426 p5052 : Prop) (h : (¬ p3953) ∨ (¬ p4426) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p2122) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2839) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4426) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial28730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory17986 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule28730 (meaning t m 2027) (meaning t m 2122) (meaning t m 2839) (meaning t m 3549) (meaning t m 3953) (meaning t m 4426) (meaning t m 5052) source

theorem rule28731 (p2027 p2274 p2829 p3588 p3958 p4390 p4471 : Prop) (h : p2027 ∨ (¬ p3958) ∨ (¬ p4390) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p4471) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p3958) ∨ (¬ p4390) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial28731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory17987 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule28731 (meaning t m 2027) (meaning t m 2274) (meaning t m 2829) (meaning t m 3588) (meaning t m 3958) (meaning t m 4390) (meaning t m 4471) source

theorem rule28732 (p2027 p2386 p3609 p3684 p3857 p4197 p4354 p4717 : Prop) (h : (¬ p4197) ∨ (¬ p4717) ∨ (¬ p4354) ∨ p2027 ∨ (¬ p2386) ∨ (¬ p3857) ∨ (¬ p3609) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2386) ∨ (¬ p3609) ∨ (¬ p3684) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4354) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial28732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4354)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory17988 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 6) (m.theta 8 9)
  exact rule28732 (meaning t m 2027) (meaning t m 2386) (meaning t m 3609) (meaning t m 3684) (meaning t m 3857) (meaning t m 4197) (meaning t m 4354) (meaning t m 4717) source

theorem rule28734 (p2027 p2248 p2901 p2946 p3246 p3591 p3923 p3950 p4347 : Prop) (h : (¬ p4347) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p3923) ∨ (¬ p2901) ∨ (¬ p2248) ∨ (¬ p3591) ∨ (¬ p2946) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial28734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory17990 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28734 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3591) (meaning t m 3923) (meaning t m 3950) (meaning t m 4347) source

theorem rule28737 (p1995 p2027 p2534 p3146 p3379 p3578 p3860 p4370 : Prop) (h : (¬ p2534) ∨ p2027 ∨ (¬ p4370) ∨ (¬ p3146) ∨ p3578 ∨ (¬ p3860) ∨ (¬ p3379) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (p3578) ∨ (¬ p3860) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial28737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory17993 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule28737 (meaning t m 1995) (meaning t m 2027) (meaning t m 2534) (meaning t m 3146) (meaning t m 3379) (meaning t m 3578) (meaning t m 3860) (meaning t m 4370) source

theorem rule28738 (p2027 p2132 p2363 p2870 p2881 p3591 p4261 p4371 p4503 p4733 : Prop) (h : (¬ p2881) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3591) ∨ (¬ p4503) ∨ (¬ p2870) ∨ (¬ p2363) ∨ (¬ p4371) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3591) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17994 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28738 (meaning t m 2027) (meaning t m 2132) (meaning t m 2363) (meaning t m 2870) (meaning t m 2881) (meaning t m 3591) (meaning t m 4261) (meaning t m 4371) (meaning t m 4503) (meaning t m 4733) source

theorem rule28739 (p3037 p3543 p4155 : Prop) (h : (¬ p3543) ∨ (¬ p4155) ∨ p3037) : (p3037) ∨ (¬ p3543) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial28739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3037) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory17995 (m.theta 0 7) (m.theta 1 7) (m.theta 3 7)
  exact rule28739 (meaning t m 3037) (meaning t m 3543) (meaning t m 4155) source

theorem rule28741 (p2027 p2396 p2668 p3947 p4067 p4405 : Prop) (h : (¬ p2668) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2668) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial28741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory17997 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule28741 (meaning t m 2027) (meaning t m 2396) (meaning t m 2668) (meaning t m 3947) (meaning t m 4067) (meaning t m 4405) source

theorem rule28742 (p2027 p2145 p3266 p3343 p3362 p3389 p3742 p4120 p4322 p4332 p4335 : Prop) (h : p2027 ∨ (¬ p2145) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4335) ∨ (¬ p3742) ∨ (¬ p3343) ∨ (¬ p4332) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2145) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial28742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory17998 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28742 (meaning t m 2027) (meaning t m 2145) (meaning t m 3266) (meaning t m 3343) (meaning t m 3362) (meaning t m 3389) (meaning t m 3742) (meaning t m 4120) (meaning t m 4322) (meaning t m 4332) (meaning t m 4335) source

theorem rule28744 (p2027 p2797 p3986 p4208 p4315 p5043 : Prop) (h : (¬ p2797) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3986) ∨ (¬ p5043) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial28744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory18000 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9)
  exact rule28744 (meaning t m 2027) (meaning t m 2797) (meaning t m 3986) (meaning t m 4208) (meaning t m 4315) (meaning t m 5043) source

theorem rule28745 (p2427 p2891 p4034 : Prop) (h : (¬ p4034) ∨ (¬ p2891) ∨ p2427) : (p2427) ∨ (¬ p2891) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial28745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory18001 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule28745 (meaning t m 2427) (meaning t m 2891) (meaning t m 4034) source

theorem rule28748 (p2027 p2145 p2264 p2459 p2563 p2807 p3646 p4117 p4948 p5059 : Prop) (h : (¬ p3646) ∨ (¬ p2563) ∨ (¬ p2459) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p5059) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2145) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial28748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18004 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule28748 (meaning t m 2027) (meaning t m 2145) (meaning t m 2264) (meaning t m 2459) (meaning t m 2563) (meaning t m 2807) (meaning t m 3646) (meaning t m 4117) (meaning t m 4948) (meaning t m 5059) source

theorem rule28750 (p2027 p3670 p4322 p4363 p4875 p5031 : Prop) (h : (¬ p5031) ∨ (¬ p4875) ∨ p2027 ∨ (¬ p3670) ∨ (¬ p4363) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4875) ∨ (¬ p5031) := by
  classical
  tauto

theorem initial28750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4875)) ∨ (¬ (meaning t m 5031)) := by
  have source := ElevenTheory.theory18006 t (m.theta 1 5) (m.theta 2 5) (m.theta 2 9) (m.theta 5 9) (m.theta 9 10)
  exact rule28750 (meaning t m 2027) (meaning t m 3670) (meaning t m 4322) (meaning t m 4363) (meaning t m 4875) (meaning t m 5031) source

theorem rule28755 (p2192 p2493 p3096 p3948 : Prop) (h : (¬ p3948) ∨ (¬ p3096) ∨ (¬ p2192) ∨ p2493) : (¬ p2192) ∨ (p2493) ∨ (¬ p3096) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial28755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (meaning t m 2493) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory18011 (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 6)
  exact rule28755 (meaning t m 2192) (meaning t m 2493) (meaning t m 3096) (meaning t m 3948) source

theorem rule28756 (p2027 p3105 p3570 p4135 p4244 p4668 : Prop) (h : (¬ p4244) ∨ (¬ p4668) ∨ (¬ p3105) ∨ (¬ p4135) ∨ p2027 ∨ (¬ p3570)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial28756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory18012 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule28756 (meaning t m 2027) (meaning t m 3105) (meaning t m 3570) (meaning t m 4135) (meaning t m 4244) (meaning t m 4668) source

theorem rule28758 (p2027 p2241 p2352 p2387 p2449 p3027 p4137 p4625 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p3027) ∨ (¬ p4625) ∨ (¬ p2387) ∨ (¬ p2241) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial28758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory18014 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule28758 (meaning t m 2027) (meaning t m 2241) (meaning t m 2352) (meaning t m 2387) (meaning t m 2449) (meaning t m 3027) (meaning t m 4137) (meaning t m 4625) (meaning t m 5021) source

theorem rule28762 (p2027 p2641 p3125 p3848 p4190 p4564 : Prop) (h : p2027 ∨ (¬ p4190) ∨ (¬ p3125) ∨ (¬ p4564) ∨ (¬ p3848) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3848) ∨ (¬ p4190) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial28762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4190)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory18018 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9)
  exact rule28762 (meaning t m 2027) (meaning t m 2641) (meaning t m 3125) (meaning t m 3848) (meaning t m 4190) (meaning t m 4564) source

theorem rule28763 (p1992 p2027 p2177 p2311 p2462 p2785 p3551 p3688 p4107 : Prop) (h : p2462 ∨ (¬ p3551) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p3688)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (p2462) ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial28763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory18019 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28763 (meaning t m 1992) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2462) (meaning t m 2785) (meaning t m 3551) (meaning t m 3688) (meaning t m 4107) source

theorem rule28764 (p2027 p2138 p2190 p2247 p2744 p3063 p3093 p3097 p3366 p3694 p4405 : Prop) (h : (¬ p4405) ∨ (¬ p3097) ∨ (¬ p3694) ∨ (¬ p2190) ∨ (¬ p2247) ∨ (¬ p2138) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2190) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3694) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial28764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory18020 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule28764 (meaning t m 2027) (meaning t m 2138) (meaning t m 2190) (meaning t m 2247) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3097) (meaning t m 3366) (meaning t m 3694) (meaning t m 4405) source

theorem rule28766 (p2027 p2911 p2922 p3097 p3379 p3646 p4107 p4524 p4666 : Prop) (h : (¬ p3379) ∨ (¬ p2911) ∨ (¬ p3097) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p4666) ∨ (¬ p4107) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial28766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory18022 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28766 (meaning t m 2027) (meaning t m 2911) (meaning t m 2922) (meaning t m 3097) (meaning t m 3379) (meaning t m 3646) (meaning t m 4107) (meaning t m 4524) (meaning t m 4666) source

theorem rule28767 (p2005 p2027 p3016 p3128 p3359 p3461 p4425 : Prop) (h : (¬ p3016) ∨ p3128 ∨ (¬ p2005) ∨ (¬ p3359) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p4425)) : (¬ p2005) ∨ (p2027) ∨ (¬ p3016) ∨ (p3128) ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial28767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory18023 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule28767 (meaning t m 2005) (meaning t m 2027) (meaning t m 3016) (meaning t m 3128) (meaning t m 3359) (meaning t m 3461) (meaning t m 4425) source

theorem rule28768 (p2027 p2138 p2437 p2651 p3868 p4322 p4385 p4786 p4826 : Prop) (h : (¬ p4786) ∨ (¬ p2138) ∨ (¬ p4385) ∨ (¬ p2651) ∨ (¬ p4826) ∨ (¬ p4322) ∨ (¬ p3868) ∨ p2027 ∨ (¬ p2437)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial28768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory18024 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule28768 (meaning t m 2027) (meaning t m 2138) (meaning t m 2437) (meaning t m 2651) (meaning t m 3868) (meaning t m 4322) (meaning t m 4385) (meaning t m 4786) (meaning t m 4826) source

theorem rule28770 (p1992 p2027 p2766 p3266 p3346 p3363 p3585 p4425 : Prop) (h : (¬ p1992) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p4425) ∨ p2766) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial28770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory18026 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28770 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3346) (meaning t m 3363) (meaning t m 3585) (meaning t m 4425) source

theorem rule28773 (p1987 p2027 p2534 p2651 p2766 p2810 p3172 p4437 : Prop) (h : (¬ p4437) ∨ (¬ p2651) ∨ (¬ p2810) ∨ p2766 ∨ (¬ p1987) ∨ (¬ p3172) ∨ (¬ p2534) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial28773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory18029 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule28773 (meaning t m 1987) (meaning t m 2027) (meaning t m 2534) (meaning t m 2651) (meaning t m 2766) (meaning t m 2810) (meaning t m 3172) (meaning t m 4437) source

theorem rule28774 (p1983 p2027 p2247 p2688 p3707 p3830 p4381 : Prop) (h : p2688 ∨ (¬ p3707) ∨ (¬ p1983) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial28774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory18030 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule28774 (meaning t m 1983) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3707) (meaning t m 3830) (meaning t m 4381) source

theorem rule28776 (p2499 p3096 p3948 p4173 : Prop) (h : (¬ p2499) ∨ (¬ p3948) ∨ (¬ p3096) ∨ p4173) : (¬ p2499) ∨ (¬ p3096) ∨ (¬ p3948) ∨ (p4173) := by
  classical
  tauto

theorem initial28776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3948)) ∨ (meaning t m 4173) := by
  have source := ElevenTheory.theory18032 (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 6)
  exact rule28776 (meaning t m 2499) (meaning t m 3096) (meaning t m 3948) (meaning t m 4173) source

theorem rule28778 (p2027 p2191 p2668 p2696 p2753 p2797 p3379 p3555 p4134 p5216 : Prop) (h : (¬ p2191) ∨ (¬ p2696) ∨ (¬ p3555) ∨ (¬ p4134) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3379) ∨ (¬ p2797) ∨ (¬ p5216) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4134) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial28778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18034 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8)
  exact rule28778 (meaning t m 2027) (meaning t m 2191) (meaning t m 2668) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3379) (meaning t m 3555) (meaning t m 4134) (meaning t m 5216) source

theorem rule28780 (p2027 p2122 p2589 p2774 p3791 p4322 p4729 p4826 p4948 : Prop) (h : (¬ p4322) ∨ (¬ p4826) ∨ (¬ p4948) ∨ (¬ p2589) ∨ (¬ p4729) ∨ (¬ p3791) ∨ (¬ p2774) ∨ (¬ p2122) ∨ p2027) : (p2027) ∨ (¬ p2122) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial28780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory18036 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule28780 (meaning t m 2027) (meaning t m 2122) (meaning t m 2589) (meaning t m 2774) (meaning t m 3791) (meaning t m 4322) (meaning t m 4729) (meaning t m 4826) (meaning t m 4948) source

theorem rule28783 (p2027 p2589 p2685 p2696 p3931 p4322 p4729 p4826 p4948 : Prop) (h : (¬ p4322) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3931) ∨ (¬ p2696) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial28783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory18039 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule28783 (meaning t m 2027) (meaning t m 2589) (meaning t m 2685) (meaning t m 2696) (meaning t m 3931) (meaning t m 4322) (meaning t m 4729) (meaning t m 4826) (meaning t m 4948) source

theorem rule28784 (p1984 p2027 p2633 p3246 p3570 p3817 p4366 : Prop) (h : (¬ p1984) ∨ (¬ p3817) ∨ p2633 ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3246) ∨ (¬ p4366)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial28784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory18040 t (m.theta 0 1) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28784 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3817) (meaning t m 4366) source

theorem rule28786 (p2027 p2190 p2901 p3146 p3661 p4118 p4558 : Prop) (h : (¬ p2190) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p3146) ∨ (¬ p4558) ∨ (¬ p3661) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2190) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory18042 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule28786 (meaning t m 2027) (meaning t m 2190) (meaning t m 2901) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4558) source

theorem rule28787 (p1994 p2027 p2352 p2387 p2630 p2667 p3008 p4195 : Prop) (h : p3008 ∨ (¬ p4195) ∨ (¬ p2667) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p1994) ∨ (¬ p2387)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2667) ∨ (p3008) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial28787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory18043 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule28787 (meaning t m 1994) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2630) (meaning t m 2667) (meaning t m 3008) (meaning t m 4195) source

theorem rule28789 (p1983 p2027 p2202 p2396 p2563 p3051 p3646 p4140 : Prop) (h : p2202 ∨ (¬ p4140) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p1983) ∨ (¬ p3051) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial28789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory18045 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule28789 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2396) (meaning t m 2563) (meaning t m 3051) (meaning t m 3646) (meaning t m 4140) source

theorem rule28795 (p2027 p2136 p2619 p3471 p4120 p4897 : Prop) (h : p2027 ∨ (¬ p2136) ∨ (¬ p4120) ∨ (¬ p4897) ∨ (¬ p2619) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p3471) ∨ (¬ p4120) ∨ (¬ p4897) := by
  classical
  tauto

theorem initial28795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4897)) := by
  have source := ElevenTheory.theory18051 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 8)
  exact rule28795 (meaning t m 2027) (meaning t m 2136) (meaning t m 2619) (meaning t m 3471) (meaning t m 4120) (meaning t m 4897) source

theorem rule28796 (p2972 p3645 p4032 : Prop) (h : (¬ p3645) ∨ (¬ p2972) ∨ (¬ p4032)) : (¬ p2972) ∨ (¬ p3645) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial28796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory18052 (m.theta 0 5) (m.theta 1 5) (m.theta 5 9)
  exact rule28796 (meaning t m 2972) (meaning t m 3645) (meaning t m 4032) source

theorem rule28799 (p2027 p2246 p2608 p2744 p2901 p2946 p3193 p3246 p3452 p4641 : Prop) (h : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p4641) ∨ (¬ p3452) ∨ (¬ p3246) ∨ (¬ p3193)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4641) := by
  classical
  tauto

theorem initial28799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4641)) := by
  have source := ElevenTheory.theory18055 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule28799 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3193) (meaning t m 3246) (meaning t m 3452) (meaning t m 4641) source

theorem rule28803 (p1977 p2027 p2191 p2241 p2766 p3555 p3692 : Prop) (h : (¬ p3555) ∨ (¬ p2241) ∨ (¬ p2191) ∨ (¬ p3692) ∨ p2766 ∨ p2027 ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2241) ∨ (p2766) ∨ (¬ p3555) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial28803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory18059 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9)
  exact rule28803 (meaning t m 1977) (meaning t m 2027) (meaning t m 2191) (meaning t m 2241) (meaning t m 2766) (meaning t m 3555) (meaning t m 3692) source

theorem rule28804 (p1998 p2027 p2202 p2563 p2881 p2891 p3645 p3646 : Prop) (h : (¬ p2563) ∨ (¬ p1998) ∨ (¬ p3645) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3646) ∨ p2202 ∨ (¬ p2891)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3645) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial28804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory18060 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule28804 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2881) (meaning t m 2891) (meaning t m 3645) (meaning t m 3646) source

theorem rule28805 (p1998 p2027 p2202 p2563 p2881 p3051 p3646 : Prop) (h : (¬ p2563) ∨ p2027 ∨ p2202 ∨ (¬ p2881) ∨ (¬ p3646) ∨ (¬ p1998) ∨ (¬ p3051)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial28805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory18061 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule28805 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2881) (meaning t m 3051) (meaning t m 3646) source

theorem rule28808 (p2187 p2274 p3955 : Prop) (h : (¬ p3955) ∨ (¬ p2187) ∨ p2274) : (¬ p2187) ∨ (p2274) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial28808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (meaning t m 2274) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory18064 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28808 (meaning t m 2187) (meaning t m 2274) (meaning t m 3955) source

theorem rule28810 (p2027 p2220 p2870 p3646 p3694 p4558 : Prop) (h : (¬ p4558) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3646) ∨ (¬ p2870) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory18066 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule28810 (meaning t m 2027) (meaning t m 2220) (meaning t m 2870) (meaning t m 3646) (meaning t m 3694) (meaning t m 4558) source

end SunPrize.SMT
