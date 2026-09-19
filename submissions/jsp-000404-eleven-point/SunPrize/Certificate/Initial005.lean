import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory001
import SunPrize.Certificate.Theory002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule5207 (p3367 p3582 p3583 : Prop) (h : (¬ p3582) ∨ (¬ p3367) ∨ (¬ p3583)) : (¬ p3367) ∨ (¬ p3582) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial5207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory309 (m.theta 1 2) (m.theta 2 4) (m.theta 2 5)
  exact rule5207 (meaning t m 3367) (meaning t m 3582) (meaning t m 3583) source

theorem rule5208 (p3201 p3581 p3584 : Prop) (h : (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3581)) : (¬ p3201) ∨ (¬ p3581) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial5208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory310 (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule5208 (meaning t m 3201) (meaning t m 3581) (meaning t m 3584) source

theorem rule5209 (p2230 p2440 p2656 : Prop) (h : (¬ p2440) ∨ (¬ p2656) ∨ (¬ p2230)) : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2656) := by
  classical
  tauto

theorem initial5209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2656)) := by
  have source := ElevenTheory.theory311 (m.theta 0 4) (m.theta 3 4) (m.theta 4 5)
  exact rule5209 (meaning t m 2230) (meaning t m 2440) (meaning t m 2656) source

theorem rule5210 (p2598 p2753 p3585 : Prop) (h : (¬ p3585) ∨ (¬ p2753) ∨ (¬ p2598)) : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial5210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory312 (m.theta 0 2) (m.theta 1 2) (m.theta 2 4)
  exact rule5210 (meaning t m 2598) (meaning t m 2753) (meaning t m 3585) source

theorem rule5211 (p2065 p3586 : Prop) (h : ((¬ p2065) ↔ (¬ p3586))) : (p2065) ∨ (¬ p3586) := by
  classical
  tauto

theorem initial5211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2065) ∨ (¬ (meaning t m 3586)) := by
  have source := ElevenTheory.theory313 t (m.theta 2 6)
  exact rule5211 (meaning t m 2065) (meaning t m 3586) source

theorem rule5213 (p2383 p3324 p3567 : Prop) (h : (¬ p3567) ∨ (¬ p3324) ∨ (¬ p2383)) : (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial5213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory314 (m.theta 0 6) (m.theta 3 6) (m.theta 6 8)
  exact rule5213 (meaning t m 2383) (meaning t m 3324) (meaning t m 3567) source

theorem rule5214 (p3583 p3587 p3588 : Prop) (h : (¬ p3587) ∨ (¬ p3588) ∨ p3583) : (p3583) ∨ (¬ p3587) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial5214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3583) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory315 (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule5214 (meaning t m 3583) (meaning t m 3587) (meaning t m 3588) source

theorem rule5215 (p2504 p2505 p2590 p3238 : Prop) (h : (¬ p2590) ∨ (¬ p3238) ∨ (¬ p2505) ∨ (¬ p2504)) : (¬ p2504) ∨ (¬ p2505) ∨ (¬ p2590) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial5215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory316 (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6)
  exact rule5215 (meaning t m 2504) (meaning t m 2505) (meaning t m 2590) (meaning t m 3238) source

theorem rule5216 (p2493 p2579 p3347 : Prop) (h : (¬ p2493) ∨ (¬ p3347) ∨ (¬ p2579)) : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial5216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory317 (m.theta 0 4) (m.theta 1 4) (m.theta 4 6)
  exact rule5216 (meaning t m 2493) (meaning t m 2579) (meaning t m 3347) source

theorem rule5218 (p1394 p1400 : Prop) : (¬ p1394) ∨ ((p1394 ∨ p1400)) := by
  classical
  tauto

theorem initial5218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1394)) ∨ (meaning t m 3592) := by
  exact rule5218 (meaning t m 1394) (meaning t m 1400)

theorem rule5219 (p1394 p1400 : Prop) : (¬ p1400) ∨ ((p1394 ∨ p1400)) := by
  classical
  tauto

theorem initial5219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1400)) ∨ (meaning t m 3592) := by
  exact rule5219 (meaning t m 1394) (meaning t m 1400)

theorem rule5236 (p3592 p3593 : Prop) (h : (p3592 ↔ p3593)) : (¬ p3592) ∨ (p3593) := by
  classical
  tauto

theorem initial5236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3592)) ∨ (meaning t m 3593) := by
  have source := ElevenTheory.theory319 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 9)
  exact rule5236 (meaning t m 3592) (meaning t m 3593) source

theorem rule5238 (p1406 p1412 : Prop) : (¬ p1406) ∨ ((p1406 ∨ p1412)) := by
  classical
  tauto

theorem initial5238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1406)) ∨ (meaning t m 3602) := by
  exact rule5238 (meaning t m 1406) (meaning t m 1412)

theorem rule5239 (p1406 p1412 : Prop) : (¬ p1412) ∨ ((p1406 ∨ p1412)) := by
  classical
  tauto

theorem initial5239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1412)) ∨ (meaning t m 3602) := by
  exact rule5239 (meaning t m 1406) (meaning t m 1412)

theorem rule5256 (p3602 p3603 : Prop) (h : (p3602 ↔ p3603)) : (¬ p3602) ∨ (p3603) := by
  classical
  tauto

theorem initial5256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3602)) ∨ (meaning t m 3603) := by
  have source := ElevenTheory.theory320 t (m.theta 2 8) (m.theta 2 9) (m.theta 8 9)
  exact rule5256 (meaning t m 3602) (meaning t m 3603) source

theorem rule5258 (p1418 p1424 : Prop) : (¬ p1418) ∨ ((p1418 ∨ p1424)) := by
  classical
  tauto

theorem initial5258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1418)) ∨ (meaning t m 3612) := by
  exact rule5258 (meaning t m 1418) (meaning t m 1424)

theorem rule5259 (p1418 p1424 : Prop) : (¬ p1424) ∨ ((p1418 ∨ p1424)) := by
  classical
  tauto

theorem initial5259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1424)) ∨ (meaning t m 3612) := by
  exact rule5259 (meaning t m 1418) (meaning t m 1424)

theorem rule5276 (p3612 p3613 : Prop) (h : (p3612 ↔ p3613)) : (¬ p3612) ∨ (p3613) := by
  classical
  tauto

theorem initial5276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3612)) ∨ (meaning t m 3613) := by
  have source := ElevenTheory.theory321 t (m.theta 0 2) (m.theta 0 9) (m.theta 2 9)
  exact rule5276 (meaning t m 3612) (meaning t m 3613) source

theorem rule5278 (p2066 p3622 : Prop) (h : ((¬ p2066) ↔ (¬ p3622))) : (p2066) ∨ (¬ p3622) := by
  classical
  tauto

theorem initial5278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2066) ∨ (¬ (meaning t m 3622)) := by
  have source := ElevenTheory.theory322 t (m.theta 2 9)
  exact rule5278 (meaning t m 2066) (meaning t m 3622) source

theorem rule5280 (p2067 p3623 : Prop) (h : ((¬ p2067) ↔ (¬ p3623))) : (p2067) ∨ (¬ p3623) := by
  classical
  tauto

theorem initial5280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2067) ∨ (¬ (meaning t m 3623)) := by
  have source := ElevenTheory.theory323 t (m.theta 1 7)
  exact rule5280 (meaning t m 2067) (meaning t m 3623) source

theorem rule5282 (p1430 p1436 : Prop) : (¬ p1430) ∨ ((p1430 ∨ p1436)) := by
  classical
  tauto

theorem initial5282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1430)) ∨ (meaning t m 3624) := by
  exact rule5282 (meaning t m 1430) (meaning t m 1436)

theorem rule5283 (p1430 p1436 : Prop) : (¬ p1436) ∨ ((p1430 ∨ p1436)) := by
  classical
  tauto

theorem initial5283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1436)) ∨ (meaning t m 3624) := by
  exact rule5283 (meaning t m 1430) (meaning t m 1436)

theorem rule5300 (p3624 p3625 : Prop) (h : (p3624 ↔ p3625)) : (¬ p3624) ∨ (p3625) := by
  classical
  tauto

theorem initial5300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3624)) ∨ (meaning t m 3625) := by
  have source := ElevenTheory.theory324 t (m.theta 1 7) (m.theta 1 9) (m.theta 7 9)
  exact rule5300 (meaning t m 3624) (meaning t m 3625) source

theorem rule5302 (p1442 p1448 : Prop) : (¬ p1442) ∨ ((p1442 ∨ p1448)) := by
  classical
  tauto

theorem initial5302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1442)) ∨ (meaning t m 3634) := by
  exact rule5302 (meaning t m 1442) (meaning t m 1448)

theorem rule5303 (p1442 p1448 : Prop) : (¬ p1448) ∨ ((p1442 ∨ p1448)) := by
  classical
  tauto

theorem initial5303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1448)) ∨ (meaning t m 3634) := by
  exact rule5303 (meaning t m 1442) (meaning t m 1448)

theorem rule5320 (p3634 p3635 : Prop) (h : (p3634 ↔ p3635)) : (¬ p3634) ∨ (p3635) := by
  classical
  tauto

theorem initial5320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3634)) ∨ (meaning t m 3635) := by
  have source := ElevenTheory.theory325 t (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule5320 (meaning t m 3634) (meaning t m 3635) source

theorem rule5322 (p2933 p3548 p3644 : Prop) (h : (¬ p3548) ∨ (¬ p2933) ∨ p3644) : (¬ p2933) ∨ (¬ p3548) ∨ (p3644) := by
  classical
  tauto

theorem initial5322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3548)) ∨ (meaning t m 3644) := by
  have source := ElevenTheory.theory326 (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule5322 (meaning t m 2933) (meaning t m 3548) (meaning t m 3644) source

theorem rule5323 (p2192 p3645 p3646 : Prop) (h : (¬ p3645) ∨ (¬ p2192) ∨ (¬ p3646)) : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial5323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory327 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6)
  exact rule5323 (meaning t m 2192) (meaning t m 3645) (meaning t m 3646) source

theorem rule5324 (p1454 p1460 : Prop) : (¬ p1454) ∨ ((p1454 ∨ p1460)) := by
  classical
  tauto

theorem initial5324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1454)) ∨ (meaning t m 3647) := by
  exact rule5324 (meaning t m 1454) (meaning t m 1460)

theorem rule5325 (p1454 p1460 : Prop) : (¬ p1460) ∨ ((p1454 ∨ p1460)) := by
  classical
  tauto

theorem initial5325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1460)) ∨ (meaning t m 3647) := by
  exact rule5325 (meaning t m 1454) (meaning t m 1460)

theorem rule5342 (p3647 p3648 : Prop) (h : (p3647 ↔ p3648)) : (¬ p3647) ∨ (p3648) := by
  classical
  tauto

theorem initial5342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3647)) ∨ (meaning t m 3648) := by
  have source := ElevenTheory.theory328 t (m.theta 0 6) (m.theta 0 9) (m.theta 6 9)
  exact rule5342 (meaning t m 3647) (meaning t m 3648) source

theorem rule5344 (p2417 p3657 p3658 p3659 : Prop) (h : (¬ p3657) ∨ (¬ p3658) ∨ (¬ p2417) ∨ (¬ p3659)) : (¬ p2417) ∨ (¬ p3657) ∨ (¬ p3658) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial5344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory329 (m.theta 2 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule5344 (meaning t m 2417) (meaning t m 3657) (meaning t m 3658) (meaning t m 3659) source

theorem rule5345 (p2230 p2579 p3660 : Prop) (h : (¬ p2230) ∨ (¬ p3660) ∨ (¬ p2579)) : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial5345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory330 (m.theta 0 4) (m.theta 4 5) (m.theta 4 6)
  exact rule5345 (meaning t m 2230) (meaning t m 2579) (meaning t m 3660) source

theorem rule5346 (p3189 p3661 p3662 : Prop) (h : (¬ p3661) ∨ (¬ p3189) ∨ (¬ p3662)) : (¬ p3189) ∨ (¬ p3661) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial5346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory331 (m.theta 1 3) (m.theta 3 5) (m.theta 3 8)
  exact rule5346 (meaning t m 3189) (meaning t m 3661) (meaning t m 3662) source

theorem rule5347 (p2252 p3172 p3189 : Prop) (h : (¬ p3189) ∨ (¬ p3172) ∨ (¬ p2252)) : (¬ p2252) ∨ (¬ p3172) ∨ (¬ p3189) := by
  classical
  tauto

theorem initial5347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) := by
  have source := ElevenTheory.theory332 (m.theta 0 3) (m.theta 1 3) (m.theta 3 8)
  exact rule5347 (meaning t m 2252) (meaning t m 3172) (meaning t m 3189) source

theorem rule5348 (p2192 p2284 p3412 : Prop) (h : (¬ p2192) ∨ (¬ p3412) ∨ p2284) : (¬ p2192) ∨ (p2284) ∨ (¬ p3412) := by
  classical
  tauto

theorem initial5348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (meaning t m 2284) ∨ (¬ (meaning t m 3412)) := by
  have source := ElevenTheory.theory333 (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule5348 (meaning t m 2192) (meaning t m 2284) (meaning t m 3412) source

theorem rule5349 (p3548 p3576 p3659 : Prop) (h : (¬ p3548) ∨ (¬ p3576) ∨ p3659) : (¬ p3548) ∨ (¬ p3576) ∨ (p3659) := by
  classical
  tauto

theorem initial5349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (meaning t m 3659) := by
  have source := ElevenTheory.theory334 (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule5349 (meaning t m 3548) (meaning t m 3576) (meaning t m 3659) source

theorem rule5350 (p1466 p1472 : Prop) : (¬ p1466) ∨ ((p1466 ∨ p1472)) := by
  classical
  tauto

theorem initial5350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1466)) ∨ (meaning t m 3663) := by
  exact rule5350 (meaning t m 1466) (meaning t m 1472)

theorem rule5351 (p1466 p1472 : Prop) : (¬ p1472) ∨ ((p1466 ∨ p1472)) := by
  classical
  tauto

theorem initial5351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1472)) ∨ (meaning t m 3663) := by
  exact rule5351 (meaning t m 1466) (meaning t m 1472)

theorem rule5368 (p3663 p3664 : Prop) (h : (p3663 ↔ p3664)) : (¬ p3663) ∨ (p3664) := by
  classical
  tauto

theorem initial5368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3663)) ∨ (meaning t m 3664) := by
  have source := ElevenTheory.theory335 t (m.theta 2 10) (m.theta 2 9) (m.theta 9 10)
  exact rule5368 (meaning t m 3663) (meaning t m 3664) source

theorem rule5370 (p1478 p1484 : Prop) : (¬ p1478) ∨ ((p1478 ∨ p1484)) := by
  classical
  tauto

theorem initial5370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1478)) ∨ (meaning t m 3673) := by
  exact rule5370 (meaning t m 1478) (meaning t m 1484)

theorem rule5371 (p1478 p1484 : Prop) : (¬ p1484) ∨ ((p1478 ∨ p1484)) := by
  classical
  tauto

theorem initial5371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1484)) ∨ (meaning t m 3673) := by
  exact rule5371 (meaning t m 1478) (meaning t m 1484)

theorem rule5388 (p3673 p3674 : Prop) (h : (p3673 ↔ p3674)) : (¬ p3673) ∨ (p3674) := by
  classical
  tauto

theorem initial5388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3673)) ∨ (meaning t m 3674) := by
  have source := ElevenTheory.theory336 t (m.theta 5 10) (m.theta 5 9) (m.theta 9 10)
  exact rule5388 (meaning t m 3673) (meaning t m 3674) source

theorem rule5390 (p2542 p3683 p3684 : Prop) (h : (¬ p2542) ∨ (¬ p3683) ∨ (¬ p3684)) : (¬ p2542) ∨ (¬ p3683) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial5390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory337 (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule5390 (meaning t m 2542) (meaning t m 3683) (meaning t m 3684) source

theorem rule5391 (p2132 p2753 p3583 : Prop) (h : (¬ p2753) ∨ (¬ p2132) ∨ (¬ p3583)) : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial5391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory338 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5)
  exact rule5391 (meaning t m 2132) (meaning t m 2753) (meaning t m 3583) source

theorem rule5392 (p3537 p3588 p3685 : Prop) (h : (¬ p3685) ∨ (¬ p3537) ∨ (¬ p3588)) : (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3685) := by
  classical
  tauto

theorem initial5392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3685)) := by
  have source := ElevenTheory.theory339 (m.theta 1 2) (m.theta 2 7) (m.theta 2 8)
  exact rule5392 (meaning t m 3537) (meaning t m 3588) (meaning t m 3685) source

theorem rule5393 (p3576 p3585 p3686 p3687 : Prop) (h : (¬ p3686) ∨ (¬ p3576) ∨ (¬ p3687) ∨ (¬ p3585)) : (¬ p3576) ∨ (¬ p3585) ∨ (¬ p3686) ∨ (¬ p3687) := by
  classical
  tauto

theorem initial5393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 3687)) := by
  have source := ElevenTheory.theory340 (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7)
  exact rule5393 (meaning t m 3576) (meaning t m 3585) (meaning t m 3686) (meaning t m 3687) source

theorem rule5394 (p2707 p3688 p3689 : Prop) (h : (¬ p3688) ∨ (¬ p3689) ∨ (¬ p2707)) : (¬ p2707) ∨ (¬ p3688) ∨ (¬ p3689) := by
  classical
  tauto

theorem initial5394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3689)) := by
  have source := ElevenTheory.theory341 (m.theta 1 2) (m.theta 2 6) (m.theta 2 7)
  exact rule5394 (meaning t m 2707) (meaning t m 3688) (meaning t m 3689) source

theorem rule5395 (p3516 p3690 p3691 : Prop) (h : (¬ p3516) ∨ (¬ p3690) ∨ (¬ p3691)) : (¬ p3516) ∨ (¬ p3690) ∨ (¬ p3691) := by
  classical
  tauto

theorem initial5395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3691)) := by
  have source := ElevenTheory.theory342 (m.theta 0 7) (m.theta 5 7) (m.theta 7 9)
  exact rule5395 (meaning t m 3516) (meaning t m 3690) (meaning t m 3691) source

theorem rule5396 (p2528 p3692 p3693 : Prop) (h : (¬ p3692) ∨ (¬ p2528) ∨ (¬ p3693)) : (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3693) := by
  classical
  tauto

theorem initial5396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3693)) := by
  have source := ElevenTheory.theory343 (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule5396 (meaning t m 2528) (meaning t m 3692) (meaning t m 3693) source

theorem rule5397 (p2373 p3694 p3695 : Prop) (h : (¬ p3694) ∨ (¬ p3695) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p3694) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial5397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory344 (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule5397 (meaning t m 2373) (meaning t m 3694) (meaning t m 3695) source

theorem rule5398 (p2143 p2619 p3696 p3697 : Prop) (h : (¬ p3696) ∨ (¬ p3697) ∨ (¬ p2143) ∨ (¬ p2619)) : (¬ p2143) ∨ (¬ p2619) ∨ (¬ p3696) ∨ (¬ p3697) := by
  classical
  tauto

theorem initial5398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3697)) := by
  have source := ElevenTheory.theory345 (m.theta 0 5) (m.theta 0 8) (m.theta 2 5) (m.theta 5 8)
  exact rule5398 (meaning t m 2143) (meaning t m 2619) (meaning t m 3696) (meaning t m 3697) source

theorem rule5399 (p2406 p3541 p3583 p3698 : Prop) (h : (¬ p3541) ∨ (¬ p3698) ∨ (¬ p3583) ∨ (¬ p2406)) : (¬ p2406) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial5399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory346 (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 5)
  exact rule5399 (meaning t m 2406) (meaning t m 3541) (meaning t m 3583) (meaning t m 3698) source

theorem rule5400 (p2449 p3690 p3699 : Prop) (h : (¬ p2449) ∨ (¬ p3690) ∨ (¬ p3699)) : (¬ p2449) ∨ (¬ p3690) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial5400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory347 (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule5400 (meaning t m 2449) (meaning t m 3690) (meaning t m 3699) source

theorem rule5402 (p1490 p1496 : Prop) : (¬ p1490) ∨ ((p1490 ∨ p1496)) := by
  classical
  tauto

theorem initial5402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1490)) ∨ (meaning t m 3700) := by
  exact rule5402 (meaning t m 1490) (meaning t m 1496)

theorem rule5403 (p1490 p1496 : Prop) : (¬ p1496) ∨ ((p1490 ∨ p1496)) := by
  classical
  tauto

theorem initial5403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1496)) ∨ (meaning t m 3700) := by
  exact rule5403 (meaning t m 1490) (meaning t m 1496)

theorem rule5420 (p3700 p3701 : Prop) (h : (p3700 ↔ p3701)) : (¬ p3700) ∨ (p3701) := by
  classical
  tauto

theorem initial5420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3700)) ∨ (meaning t m 3701) := by
  have source := ElevenTheory.theory349 t (m.theta 1 10) (m.theta 1 9) (m.theta 9 10)
  exact rule5420 (meaning t m 3700) (meaning t m 3701) source

theorem rule5422 (p1502 p1508 : Prop) : (¬ p1502) ∨ ((p1502 ∨ p1508)) := by
  classical
  tauto

theorem initial5422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1502)) ∨ (meaning t m 3710) := by
  exact rule5422 (meaning t m 1502) (meaning t m 1508)

theorem rule5423 (p1502 p1508 : Prop) : (¬ p1508) ∨ ((p1502 ∨ p1508)) := by
  classical
  tauto

theorem initial5423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1508)) ∨ (meaning t m 3710) := by
  exact rule5423 (meaning t m 1502) (meaning t m 1508)

theorem rule5440 (p3710 p3711 : Prop) (h : (p3710 ↔ p3711)) : (¬ p3710) ∨ (p3711) := by
  classical
  tauto

theorem initial5440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3710)) ∨ (meaning t m 3711) := by
  have source := ElevenTheory.theory350 t (m.theta 2 10) (m.theta 2 5) (m.theta 5 10)
  exact rule5440 (meaning t m 3710) (meaning t m 3711) source

theorem rule5442 (p1514 p1520 : Prop) : (¬ p1514) ∨ ((p1514 ∨ p1520)) := by
  classical
  tauto

theorem initial5442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1514)) ∨ (meaning t m 3720) := by
  exact rule5442 (meaning t m 1514) (meaning t m 1520)

theorem rule5443 (p1514 p1520 : Prop) : (¬ p1520) ∨ ((p1514 ∨ p1520)) := by
  classical
  tauto

theorem initial5443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1520)) ∨ (meaning t m 3720) := by
  exact rule5443 (meaning t m 1514) (meaning t m 1520)

theorem rule5460 (p3720 p3721 : Prop) (h : (p3720 ↔ p3721)) : (¬ p3720) ∨ (p3721) := by
  classical
  tauto

theorem initial5460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3720)) ∨ (meaning t m 3721) := by
  have source := ElevenTheory.theory351 t (m.theta 4 10) (m.theta 4 5) (m.theta 5 10)
  exact rule5460 (meaning t m 3720) (meaning t m 3721) source

theorem rule5462 (p1526 p1532 : Prop) : (¬ p1526) ∨ ((p1526 ∨ p1532)) := by
  classical
  tauto

theorem initial5462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1526)) ∨ (meaning t m 3730) := by
  exact rule5462 (meaning t m 1526) (meaning t m 1532)

theorem rule5463 (p1526 p1532 : Prop) : (¬ p1532) ∨ ((p1526 ∨ p1532)) := by
  classical
  tauto

theorem initial5463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1532)) ∨ (meaning t m 3730) := by
  exact rule5463 (meaning t m 1526) (meaning t m 1532)

theorem rule5480 (p3730 p3731 : Prop) (h : (p3730 ↔ p3731)) : (¬ p3730) ∨ (p3731) := by
  classical
  tauto

theorem initial5480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3730)) ∨ (meaning t m 3731) := by
  have source := ElevenTheory.theory352 t (m.theta 5 10) (m.theta 5 6) (m.theta 6 10)
  exact rule5480 (meaning t m 3730) (meaning t m 3731) source

theorem rule5483 (p2542 p3741 p3742 : Prop) (h : (¬ p3741) ∨ (¬ p2542) ∨ (¬ p3742)) : (¬ p2542) ∨ (¬ p3741) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial5483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory354 (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule5483 (meaning t m 2542) (meaning t m 3741) (meaning t m 3742) source

theorem rule5485 (p3323 p3744 p3745 : Prop) (h : (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3745)) : (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial5485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory356 (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule5485 (meaning t m 3323) (meaning t m 3744) (meaning t m 3745) source

theorem rule5486 (p2499 p3222 p3746 : Prop) (h : (¬ p3222) ∨ (¬ p2499) ∨ (¬ p3746)) : (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3746) := by
  classical
  tauto

theorem initial5486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3746)) := by
  have source := ElevenTheory.theory357 (m.theta 1 4) (m.theta 4 6) (m.theta 4 9)
  exact rule5486 (meaning t m 2499) (meaning t m 3222) (meaning t m 3746) source

theorem rule5487 (p3051 p3696 p3697 p3747 : Prop) (h : (¬ p3697) ∨ (¬ p3696) ∨ (¬ p3747) ∨ (¬ p3051)) : (¬ p3051) ∨ (¬ p3696) ∨ (¬ p3697) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial5487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory358 (m.theta 0 5) (m.theta 0 8) (m.theta 5 7) (m.theta 5 8)
  exact rule5487 (meaning t m 3051) (meaning t m 3696) (meaning t m 3697) (meaning t m 3747) source

theorem rule5488 (p1538 p1544 : Prop) : (¬ p1538) ∨ ((p1538 ∨ p1544)) := by
  classical
  tauto

theorem initial5488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1538)) ∨ (meaning t m 3748) := by
  exact rule5488 (meaning t m 1538) (meaning t m 1544)

theorem rule5489 (p1538 p1544 : Prop) : (¬ p1544) ∨ ((p1538 ∨ p1544)) := by
  classical
  tauto

theorem initial5489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1544)) ∨ (meaning t m 3748) := by
  exact rule5489 (meaning t m 1538) (meaning t m 1544)

theorem rule5506 (p3748 p3749 : Prop) (h : (p3748 ↔ p3749)) : (¬ p3748) ∨ (p3749) := by
  classical
  tauto

theorem initial5506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3748)) ∨ (meaning t m 3749) := by
  have source := ElevenTheory.theory359 t (m.theta 2 3) (m.theta 2 9) (m.theta 3 9)
  exact rule5506 (meaning t m 3748) (meaning t m 3749) source

theorem rule5508 (p2137 p2156 p3758 : Prop) (h : (¬ p3758) ∨ (¬ p2156) ∨ (¬ p2137)) : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial5508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory360 (m.theta 0 5) (m.theta 2 5) (m.theta 5 6)
  exact rule5508 (meaning t m 2137) (meaning t m 2156) (meaning t m 3758) source

theorem rule5509 (p2911 p2933 p3548 : Prop) (h : (¬ p3548) ∨ (¬ p2911) ∨ (¬ p2933)) : (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial5509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory361 (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule5509 (meaning t m 2911) (meaning t m 2933) (meaning t m 3548) source

theorem rule5510 (p3363 p3759 : Prop) (h : p3759 ∨ p3363) : (p3363) ∨ (p3759) := by
  classical
  tauto

theorem initial5510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3363) ∨ (meaning t m 3759) := by
  have source := ElevenTheory.theory362 (m.theta 0 4) (m.theta 2 4)
  exact rule5510 (meaning t m 3363) (meaning t m 3759) source

theorem rule5511 (p2230 p2850 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p2230) ∨ p2850) : (¬ p2230) ∨ (p2850) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial5511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (meaning t m 2850) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory363 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5)
  exact rule5511 (meaning t m 2230) (meaning t m 2850) (meaning t m 3759) source

theorem rule5512 (p2573 p3584 p3759 : Prop) (h : (¬ p3584) ∨ (¬ p3759) ∨ (¬ p2573)) : (¬ p2573) ∨ (¬ p3584) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial5512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory364 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6)
  exact rule5512 (meaning t m 2573) (meaning t m 3584) (meaning t m 3759) source

theorem rule5513 (p1550 p1556 : Prop) : (¬ p1550) ∨ ((p1550 ∨ p1556)) := by
  classical
  tauto

theorem initial5513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1550)) ∨ (meaning t m 3760) := by
  exact rule5513 (meaning t m 1550) (meaning t m 1556)

theorem rule5514 (p1550 p1556 : Prop) : (¬ p1556) ∨ ((p1550 ∨ p1556)) := by
  classical
  tauto

theorem initial5514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1556)) ∨ (meaning t m 3760) := by
  exact rule5514 (meaning t m 1550) (meaning t m 1556)

theorem rule5531 (p3760 p3761 : Prop) (h : (p3760 ↔ p3761)) : (¬ p3760) ∨ (p3761) := by
  classical
  tauto

theorem initial5531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3760)) ∨ (meaning t m 3761) := by
  have source := ElevenTheory.theory365 t (m.theta 0 10) (m.theta 0 9) (m.theta 9 10)
  exact rule5531 (meaning t m 3760) (meaning t m 3761) source

theorem rule5535 (p3771 p3772 p3773 p3774 p3775 : Prop) : (¬ (p3771 ∧ p3772 ∧ p3773 ∧ p3774 ∧ p3775)) ∨ (p3773) := by
  classical
  tauto

theorem initial5535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3770)) ∨ (meaning t m 3773) := by
  exact rule5535 (meaning t m 3771) (meaning t m 3772) (meaning t m 3773) (meaning t m 3774) (meaning t m 3775)

theorem rule5543 (p3771 p3772 p3773 p3774 p3775 : Prop) : (p3773) ∨ (((¬ p3775) ∨ (¬ p3771) ∨ (¬ p3772) ∨ (¬ p3774) ∨ (¬ p3773))) := by
  classical
  tauto

theorem initial5543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3773) ∨ (meaning t m 3776) := by
  exact rule5543 (meaning t m 3771) (meaning t m 3772) (meaning t m 3773) (meaning t m 3774) (meaning t m 3775)

theorem rule5545 (p3770 p3776 : Prop) (h : (p3770 ↔ (¬ p3776))) : (¬ p3770) ∨ (¬ p3776) := by
  classical
  tauto

theorem initial5545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3770)) ∨ (¬ (meaning t m 3776)) := by
  have source := ElevenTheory.theory366 t (m.theta 0 10) (m.theta 0 9) (m.theta 9 10)
  exact rule5545 (meaning t m 3770) (meaning t m 3776) source

theorem rule5549 (p3767 p3778 p3779 p3780 p3781 : Prop) : (p3767) ∨ (¬ (p3778 ∧ p3779 ∧ p3767 ∧ p3780 ∧ p3781)) := by
  classical
  tauto

theorem initial5549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3767) ∨ (¬ (meaning t m 3777)) := by
  exact rule5549 (meaning t m 3767) (meaning t m 3778) (meaning t m 3779) (meaning t m 3780) (meaning t m 3781)

theorem rule5554 (p3767 p3778 p3779 p3780 p3781 : Prop) : (p3767) ∨ (((¬ p3779) ∨ (¬ p3767) ∨ (¬ p3780) ∨ (¬ p3781) ∨ (¬ p3778))) := by
  classical
  tauto

theorem initial5554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3767) ∨ (meaning t m 3782) := by
  exact rule5554 (meaning t m 3767) (meaning t m 3778) (meaning t m 3779) (meaning t m 3780) (meaning t m 3781)

theorem rule5559 (p3777 p3782 : Prop) (h : (p3777 ↔ (¬ p3782))) : (¬ p3777) ∨ (¬ p3782) := by
  classical
  tauto

theorem initial5559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3777)) ∨ (¬ (meaning t m 3782)) := by
  have source := ElevenTheory.theory367 t (m.theta 0 10) (m.theta 0 9) (m.theta 9 10)
  exact rule5559 (meaning t m 3777) (meaning t m 3782) source

theorem rule5561 (p2068 p3783 : Prop) (h : ((¬ p2068) ↔ (¬ p3783))) : (p2068) ∨ (¬ p3783) := by
  classical
  tauto

theorem initial5561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2068) ∨ (¬ (meaning t m 3783)) := by
  have source := ElevenTheory.theory368 t (m.theta 0 9)
  exact rule5561 (meaning t m 2068) (meaning t m 3783) source

theorem rule5563 (p1562 p1568 : Prop) : (¬ p1562) ∨ ((p1562 ∨ p1568)) := by
  classical
  tauto

theorem initial5563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1562)) ∨ (meaning t m 3784) := by
  exact rule5563 (meaning t m 1562) (meaning t m 1568)

theorem rule5564 (p1562 p1568 : Prop) : (¬ p1568) ∨ ((p1562 ∨ p1568)) := by
  classical
  tauto

theorem initial5564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1568)) ∨ (meaning t m 3784) := by
  exact rule5564 (meaning t m 1562) (meaning t m 1568)

theorem rule5581 (p3784 p3785 : Prop) (h : (p3784 ↔ p3785)) : (¬ p3784) ∨ (p3785) := by
  classical
  tauto

theorem initial5581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3784)) ∨ (meaning t m 3785) := by
  have source := ElevenTheory.theory369 t (m.theta 6 10) (m.theta 6 7) (m.theta 7 10)
  exact rule5581 (meaning t m 3784) (meaning t m 3785) source

theorem rule5583 (p1574 p1580 : Prop) : (¬ p1574) ∨ ((p1574 ∨ p1580)) := by
  classical
  tauto

theorem initial5583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1574)) ∨ (meaning t m 3794) := by
  exact rule5583 (meaning t m 1574) (meaning t m 1580)

theorem rule5584 (p1574 p1580 : Prop) : (¬ p1580) ∨ ((p1574 ∨ p1580)) := by
  classical
  tauto

theorem initial5584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1580)) ∨ (meaning t m 3794) := by
  exact rule5584 (meaning t m 1574) (meaning t m 1580)

theorem rule5601 (p3794 p3795 : Prop) (h : (p3794 ↔ p3795)) : (¬ p3794) ∨ (p3795) := by
  classical
  tauto

theorem initial5601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3794)) ∨ (meaning t m 3795) := by
  have source := ElevenTheory.theory370 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule5601 (meaning t m 3794) (meaning t m 3795) source

theorem rule5610 (p3805 p3806 p3807 p3808 p3809 : Prop) : (p3807) ∨ (((¬ p3808) ∨ (¬ p3807) ∨ (¬ p3805) ∨ (¬ p3806) ∨ (¬ p3809))) := by
  classical
  tauto

theorem initial5610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3807) ∨ (meaning t m 3810) := by
  exact rule5610 (meaning t m 3805) (meaning t m 3806) (meaning t m 3807) (meaning t m 3808) (meaning t m 3809)

theorem rule5615 (p3804 p3810 : Prop) (h : (p3804 ↔ (¬ p3810))) : (¬ p3804) ∨ (¬ p3810) := by
  classical
  tauto

theorem initial5615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3804)) ∨ (¬ (meaning t m 3810)) := by
  have source := ElevenTheory.theory371 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule5615 (meaning t m 3804) (meaning t m 3810) source

theorem rule5616 (p3804 p3810 : Prop) (h : (p3804 ↔ (¬ p3810))) : (p3804) ∨ (p3810) := by
  classical
  tauto

theorem initial5616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3804) ∨ (meaning t m 3810) := by
  have source := ElevenTheory.theory371 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule5616 (meaning t m 3804) (meaning t m 3810) source

theorem rule5625 (p3801 p3812 p3813 p3814 p3815 : Prop) : (p3801) ∨ (((¬ p3812) ∨ (¬ p3813) ∨ (¬ p3801) ∨ (¬ p3814) ∨ (¬ p3815))) := by
  classical
  tauto

theorem initial5625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3801) ∨ (meaning t m 3816) := by
  exact rule5625 (meaning t m 3801) (meaning t m 3812) (meaning t m 3813) (meaning t m 3814) (meaning t m 3815)

theorem rule5629 (p3811 p3816 : Prop) (h : (p3811 ↔ (¬ p3816))) : (¬ p3811) ∨ (¬ p3816) := by
  classical
  tauto

theorem initial5629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3811)) ∨ (¬ (meaning t m 3816)) := by
  have source := ElevenTheory.theory372 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule5629 (meaning t m 3811) (meaning t m 3816) source

theorem rule5630 (p3811 p3816 : Prop) (h : (p3811 ↔ (¬ p3816))) : (p3811) ∨ (p3816) := by
  classical
  tauto

theorem initial5630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3811) ∨ (meaning t m 3816) := by
  have source := ElevenTheory.theory372 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule5630 (meaning t m 3811) (meaning t m 3816) source

theorem rule5631 (p2449 p3037 p3817 : Prop) (h : (¬ p2449) ∨ (¬ p3037) ∨ (¬ p3817)) : (¬ p2449) ∨ (¬ p3037) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial5631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory373 (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule5631 (meaning t m 2449) (meaning t m 3037) (meaning t m 3817) source

theorem rule5632 (p2069 p3818 : Prop) (h : ((¬ p2069) ↔ (¬ p3818))) : (p2069) ∨ (¬ p3818) := by
  classical
  tauto

theorem initial5632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2069) ∨ (¬ (meaning t m 3818)) := by
  have source := ElevenTheory.theory374 t (m.theta 1 6)
  exact rule5632 (meaning t m 2069) (meaning t m 3818) source

theorem rule5635 (p3546 p3631 p3821 : Prop) (h : (¬ p3546) ∨ (¬ p3821) ∨ (¬ p3631)) : (¬ p3546) ∨ (¬ p3631) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial5635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory376 (m.theta 0 7) (m.theta 1 7) (m.theta 7 9)
  exact rule5635 (meaning t m 3546) (meaning t m 3631) (meaning t m 3821) source

theorem rule5636 (p2307 p2779 p3822 : Prop) (h : (¬ p2307) ∨ (¬ p3822) ∨ (¬ p2779)) : (¬ p2307) ∨ (¬ p2779) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial5636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory377 (m.theta 0 6) (m.theta 2 6) (m.theta 6 7)
  exact rule5636 (meaning t m 2307) (meaning t m 2779) (meaning t m 3822) source

theorem rule5637 (p1586 p1592 : Prop) : (¬ p1586) ∨ ((p1586 ∨ p1592)) := by
  classical
  tauto

theorem initial5637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1586)) ∨ (meaning t m 3823) := by
  exact rule5637 (meaning t m 1586) (meaning t m 1592)

theorem rule5638 (p1586 p1592 : Prop) : (¬ p1592) ∨ ((p1586 ∨ p1592)) := by
  classical
  tauto

theorem initial5638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1592)) ∨ (meaning t m 3823) := by
  exact rule5638 (meaning t m 1586) (meaning t m 1592)

theorem rule5655 (p3823 p3824 : Prop) (h : (p3823 ↔ p3824)) : (¬ p3823) ∨ (p3824) := by
  classical
  tauto

theorem initial5655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3823)) ∨ (meaning t m 3824) := by
  have source := ElevenTheory.theory378 t (m.theta 0 1) (m.theta 0 9) (m.theta 1 9)
  exact rule5655 (meaning t m 3823) (meaning t m 3824) source

theorem rule5657 (p2241 p3833 p3834 : Prop) (h : (¬ p2241) ∨ (¬ p3833) ∨ (¬ p3834)) : (¬ p2241) ∨ (¬ p3833) ∨ (¬ p3834) := by
  classical
  tauto

theorem initial5657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3833)) ∨ (¬ (meaning t m 3834)) := by
  have source := ElevenTheory.theory379 (m.theta 0 1) (m.theta 1 3) (m.theta 1 9)
  exact rule5657 (meaning t m 2241) (meaning t m 3833) (meaning t m 3834) source

theorem rule5658 (p1598 p1604 : Prop) : (¬ p1598) ∨ ((p1598 ∨ p1604)) := by
  classical
  tauto

theorem initial5658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1598)) ∨ (meaning t m 3835) := by
  exact rule5658 (meaning t m 1598) (meaning t m 1604)

theorem rule5659 (p1598 p1604 : Prop) : (¬ p1604) ∨ ((p1598 ∨ p1604)) := by
  classical
  tauto

theorem initial5659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1604)) ∨ (meaning t m 3835) := by
  exact rule5659 (meaning t m 1598) (meaning t m 1604)

theorem rule5676 (p3835 p3836 : Prop) (h : (p3835 ↔ p3836)) : (¬ p3835) ∨ (p3836) := by
  classical
  tauto

theorem initial5676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3835)) ∨ (meaning t m 3836) := by
  have source := ElevenTheory.theory380 t (m.theta 1 3) (m.theta 1 9) (m.theta 3 9)
  exact rule5676 (meaning t m 3835) (meaning t m 3836) source

theorem rule5678 (p3846 p3847 p3848 p3849 p3850 : Prop) : (¬ (p3846 ∧ p3847 ∧ p3848 ∧ p3849 ∧ p3850)) ∨ (p3846) := by
  classical
  tauto

theorem initial5678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3845)) ∨ (meaning t m 3846) := by
  exact rule5678 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5679 (p3846 p3847 p3848 p3849 p3850 : Prop) : (¬ (p3846 ∧ p3847 ∧ p3848 ∧ p3849 ∧ p3850)) ∨ (p3847) := by
  classical
  tauto

theorem initial5679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3845)) ∨ (meaning t m 3847) := by
  exact rule5679 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5680 (p3846 p3847 p3848 p3849 p3850 : Prop) : (¬ (p3846 ∧ p3847 ∧ p3848 ∧ p3849 ∧ p3850)) ∨ (p3848) := by
  classical
  tauto

theorem initial5680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3845)) ∨ (meaning t m 3848) := by
  exact rule5680 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5685 (p3846 p3847 p3848 p3849 p3850 : Prop) : (p3847) ∨ (((¬ p3849) ∨ (¬ p3847) ∨ (¬ p3846) ∨ (¬ p3850) ∨ (¬ p3848))) := by
  classical
  tauto

theorem initial5685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3847) ∨ (meaning t m 3851) := by
  exact rule5685 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5686 (p3846 p3847 p3848 p3849 p3850 : Prop) : (p3846) ∨ (((¬ p3849) ∨ (¬ p3847) ∨ (¬ p3846) ∨ (¬ p3850) ∨ (¬ p3848))) := by
  classical
  tauto

theorem initial5686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3846) ∨ (meaning t m 3851) := by
  exact rule5686 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5688 (p3846 p3847 p3848 p3849 p3850 : Prop) : (p3848) ∨ (((¬ p3849) ∨ (¬ p3847) ∨ (¬ p3846) ∨ (¬ p3850) ∨ (¬ p3848))) := by
  classical
  tauto

theorem initial5688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3848) ∨ (meaning t m 3851) := by
  exact rule5688 (meaning t m 3846) (meaning t m 3847) (meaning t m 3848) (meaning t m 3849) (meaning t m 3850)

theorem rule5690 (p3845 p3851 : Prop) (h : (p3845 ↔ (¬ p3851))) : (¬ p3845) ∨ (¬ p3851) := by
  classical
  tauto

theorem initial5690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3845)) ∨ (¬ (meaning t m 3851)) := by
  have source := ElevenTheory.theory381 t (m.theta 1 3) (m.theta 1 9) (m.theta 3 9)
  exact rule5690 (meaning t m 3845) (meaning t m 3851) source

theorem rule5692 (p3833 p3842 p3853 p3854 p3855 : Prop) : (¬ (p3853 ∧ p3833 ∧ p3842 ∧ p3854 ∧ p3855)) ∨ (p3853) := by
  classical
  tauto

theorem initial5692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3852)) ∨ (meaning t m 3853) := by
  exact rule5692 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5693 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3833) ∨ (¬ (p3853 ∧ p3833 ∧ p3842 ∧ p3854 ∧ p3855)) := by
  classical
  tauto

theorem initial5693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3833) ∨ (¬ (meaning t m 3852)) := by
  exact rule5693 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5694 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3842) ∨ (¬ (p3853 ∧ p3833 ∧ p3842 ∧ p3854 ∧ p3855)) := by
  classical
  tauto

theorem initial5694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3842) ∨ (¬ (meaning t m 3852)) := by
  exact rule5694 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5695 (p3833 p3842 p3853 p3854 p3855 : Prop) : (¬ (p3853 ∧ p3833 ∧ p3842 ∧ p3854 ∧ p3855)) ∨ (p3854) := by
  classical
  tauto

theorem initial5695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3852)) ∨ (meaning t m 3854) := by
  exact rule5695 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5698 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3853) ∨ (((¬ p3853) ∨ (¬ p3854) ∨ (¬ p3855) ∨ (¬ p3833) ∨ (¬ p3842))) := by
  classical
  tauto

theorem initial5698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3853) ∨ (meaning t m 3856) := by
  exact rule5698 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5699 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3854) ∨ (((¬ p3853) ∨ (¬ p3854) ∨ (¬ p3855) ∨ (¬ p3833) ∨ (¬ p3842))) := by
  classical
  tauto

theorem initial5699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3854) ∨ (meaning t m 3856) := by
  exact rule5699 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5701 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3833) ∨ (((¬ p3853) ∨ (¬ p3854) ∨ (¬ p3855) ∨ (¬ p3833) ∨ (¬ p3842))) := by
  classical
  tauto

theorem initial5701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3833) ∨ (meaning t m 3856) := by
  exact rule5701 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5702 (p3833 p3842 p3853 p3854 p3855 : Prop) : (p3842) ∨ (((¬ p3853) ∨ (¬ p3854) ∨ (¬ p3855) ∨ (¬ p3833) ∨ (¬ p3842))) := by
  classical
  tauto

theorem initial5702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3842) ∨ (meaning t m 3856) := by
  exact rule5702 (meaning t m 3833) (meaning t m 3842) (meaning t m 3853) (meaning t m 3854) (meaning t m 3855)

theorem rule5704 (p3852 p3856 : Prop) (h : (p3852 ↔ (¬ p3856))) : (¬ p3852) ∨ (¬ p3856) := by
  classical
  tauto

theorem initial5704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3852)) ∨ (¬ (meaning t m 3856)) := by
  have source := ElevenTheory.theory382 t (m.theta 1 3) (m.theta 1 9) (m.theta 3 9)
  exact rule5704 (meaning t m 3852) (meaning t m 3856) source

theorem rule5706 (p3073 p3857 p3858 : Prop) (h : (¬ p3857) ∨ (¬ p3858) ∨ (¬ p3073)) : (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3858) := by
  classical
  tauto

theorem initial5706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3858)) := by
  have source := ElevenTheory.theory383 (m.theta 0 8) (m.theta 1 8) (m.theta 8 9)
  exact rule5706 (meaning t m 3073) (meaning t m 3857) (meaning t m 3858) source

theorem rule5707 (p2241 p3859 p3860 : Prop) (h : (¬ p3859) ∨ (¬ p3860) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p3859) ∨ (¬ p3860) := by
  classical
  tauto

theorem initial5707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3860)) := by
  have source := ElevenTheory.theory384 (m.theta 0 1) (m.theta 1 3) (m.theta 1 8)
  exact rule5707 (meaning t m 2241) (meaning t m 3859) (meaning t m 3860) source

theorem rule5708 (p1610 p1616 : Prop) : (¬ p1610) ∨ ((p1610 ∨ p1616)) := by
  classical
  tauto

theorem initial5708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1610)) ∨ (meaning t m 3861) := by
  exact rule5708 (meaning t m 1610) (meaning t m 1616)

theorem rule5709 (p1610 p1616 : Prop) : (¬ p1616) ∨ ((p1610 ∨ p1616)) := by
  classical
  tauto

theorem initial5709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1616)) ∨ (meaning t m 3861) := by
  exact rule5709 (meaning t m 1610) (meaning t m 1616)

theorem rule5726 (p3861 p3862 : Prop) (h : (p3861 ↔ p3862)) : (¬ p3861) ∨ (p3862) := by
  classical
  tauto

theorem initial5726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3861)) ∨ (meaning t m 3862) := by
  have source := ElevenTheory.theory385 t (m.theta 4 10) (m.theta 4 7) (m.theta 7 10)
  exact rule5726 (meaning t m 3861) (meaning t m 3862) source

theorem rule5728 (p2070 p3871 : Prop) (h : ((¬ p2070) ↔ (¬ p3871))) : (p2070) ∨ (¬ p3871) := by
  classical
  tauto

theorem initial5728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2070) ∨ (¬ (meaning t m 3871)) := by
  have source := ElevenTheory.theory386 t (m.theta 3 9)
  exact rule5728 (meaning t m 2070) (meaning t m 3871) source

theorem rule5731 (p2192 p3486 p3872 : Prop) (h : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3872)) : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial5731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory388 (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule5731 (meaning t m 2192) (meaning t m 3486) (meaning t m 3872) source

theorem rule5733 (p2780 p2829 p3366 : Prop) (h : (¬ p2829) ∨ (¬ p2780) ∨ (¬ p3366)) : (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3366) := by
  classical
  tauto

theorem initial5733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3366)) := by
  have source := ElevenTheory.theory390 (m.theta 0 2) (m.theta 1 2) (m.theta 2 6)
  exact rule5733 (meaning t m 2780) (meaning t m 2829) (meaning t m 3366) source

theorem rule5734 (p3874 p3875 p3876 : Prop) (h : (¬ p3874) ∨ (¬ p3875) ∨ p3876) : (¬ p3874) ∨ (¬ p3875) ∨ (p3876) := by
  classical
  tauto

theorem initial5734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3875)) ∨ (meaning t m 3876) := by
  have source := ElevenTheory.theory391 (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule5734 (meaning t m 3874) (meaning t m 3875) (meaning t m 3876) source

theorem rule5736 (p2284 p2957 p3646 : Prop) (h : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p2284)) : (¬ p2284) ∨ (¬ p2957) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial5736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory393 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule5736 (meaning t m 2284) (meaning t m 2957) (meaning t m 3646) source

theorem rule5737 (p2811 p3166 p3877 : Prop) (h : (¬ p2811) ∨ (¬ p3877) ∨ (¬ p3166)) : (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial5737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory394 (m.theta 0 3) (m.theta 2 3) (m.theta 3 8)
  exact rule5737 (meaning t m 2811) (meaning t m 3166) (meaning t m 3877) source

theorem rule5738 (p2810 p3877 p3878 : Prop) (h : (¬ p2810) ∨ (¬ p3878) ∨ p3877) : (¬ p2810) ∨ (p3877) ∨ (¬ p3878) := by
  classical
  tauto

theorem initial5738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (meaning t m 3877) ∨ (¬ (meaning t m 3878)) := by
  have source := ElevenTheory.theory395 (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule5738 (meaning t m 2810) (meaning t m 3877) (meaning t m 3878) source

theorem rule5739 (p2427 p2563 p3872 : Prop) (h : (¬ p3872) ∨ (¬ p2563) ∨ p2427) : (p2427) ∨ (¬ p2563) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial5739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory396 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule5739 (meaning t m 2427) (meaning t m 2563) (meaning t m 3872) source

theorem rule5740 (p3156 p3879 p3880 : Prop) (h : (¬ p3156) ∨ (¬ p3879) ∨ (¬ p3880)) : (¬ p3156) ∨ (¬ p3879) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial5740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory397 (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule5740 (meaning t m 3156) (meaning t m 3879) (meaning t m 3880) source

theorem rule5741 (p1622 p1628 : Prop) : (¬ p1622) ∨ ((p1622 ∨ p1628)) := by
  classical
  tauto

theorem initial5741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1622)) ∨ (meaning t m 3881) := by
  exact rule5741 (meaning t m 1622) (meaning t m 1628)

theorem rule5742 (p1622 p1628 : Prop) : (¬ p1628) ∨ ((p1622 ∨ p1628)) := by
  classical
  tauto

theorem initial5742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1628)) ∨ (meaning t m 3881) := by
  exact rule5742 (meaning t m 1622) (meaning t m 1628)

theorem rule5759 (p3881 p3882 : Prop) (h : (p3881 ↔ p3882)) : (¬ p3881) ∨ (p3882) := by
  classical
  tauto

theorem initial5759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3881)) ∨ (meaning t m 3882) := by
  have source := ElevenTheory.theory398 t (m.theta 4 10) (m.theta 4 6) (m.theta 6 10)
  exact rule5759 (meaning t m 3881) (meaning t m 3882) source

theorem rule5764 (p1634 p1640 : Prop) : (¬ p1634) ∨ ((p1634 ∨ p1640)) := by
  classical
  tauto

theorem initial5764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1634)) ∨ (meaning t m 3894) := by
  exact rule5764 (meaning t m 1634) (meaning t m 1640)

theorem rule5765 (p1634 p1640 : Prop) : (¬ p1640) ∨ ((p1634 ∨ p1640)) := by
  classical
  tauto

theorem initial5765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1640)) ∨ (meaning t m 3894) := by
  exact rule5765 (meaning t m 1634) (meaning t m 1640)

theorem rule5782 (p3894 p3895 : Prop) (h : (p3894 ↔ p3895)) : (¬ p3894) ∨ (p3895) := by
  classical
  tauto

theorem initial5782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3894)) ∨ (meaning t m 3895) := by
  have source := ElevenTheory.theory401 t (m.theta 3 10) (m.theta 3 4) (m.theta 4 10)
  exact rule5782 (meaning t m 3894) (meaning t m 3895) source

theorem rule5784 (p2136 p3904 p3905 : Prop) (h : (¬ p3904) ∨ (¬ p3905) ∨ p2136) : (p2136) ∨ (¬ p3904) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial5784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2136) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory402 (m.theta 0 2) (m.theta 0 4) (m.theta 0 5)
  exact rule5784 (meaning t m 2136) (meaning t m 3904) (meaning t m 3905) source

theorem rule5785 (p3073 p3692 p3906 : Prop) (h : (¬ p3906) ∨ (¬ p3073) ∨ (¬ p3692)) : (¬ p3073) ∨ (¬ p3692) ∨ (¬ p3906) := by
  classical
  tauto

theorem initial5785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3906)) := by
  have source := ElevenTheory.theory403 (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule5785 (meaning t m 3073) (meaning t m 3692) (meaning t m 3906) source

theorem rule5786 (p2104 p3366 p3537 : Prop) (h : (¬ p2104) ∨ (¬ p3366) ∨ (¬ p3537)) : (¬ p2104) ∨ (¬ p3366) ∨ (¬ p3537) := by
  classical
  tauto

theorem initial5786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) := by
  have source := ElevenTheory.theory404 (m.theta 0 2) (m.theta 1 2) (m.theta 2 8)
  exact rule5786 (meaning t m 2104) (meaning t m 3366) (meaning t m 3537) source

theorem rule5787 (p1646 p1652 : Prop) : (¬ p1646) ∨ ((p1646 ∨ p1652)) := by
  classical
  tauto

theorem initial5787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1646)) ∨ (meaning t m 3907) := by
  exact rule5787 (meaning t m 1646) (meaning t m 1652)

theorem rule5788 (p1646 p1652 : Prop) : (¬ p1652) ∨ ((p1646 ∨ p1652)) := by
  classical
  tauto

theorem initial5788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1652)) ∨ (meaning t m 3907) := by
  exact rule5788 (meaning t m 1646) (meaning t m 1652)

theorem rule5805 (p3907 p3908 : Prop) (h : (p3907 ↔ p3908)) : (¬ p3907) ∨ (p3908) := by
  classical
  tauto

theorem initial5805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3907)) ∨ (meaning t m 3908) := by
  have source := ElevenTheory.theory405 t (m.theta 2 10) (m.theta 2 6) (m.theta 6 10)
  exact rule5805 (meaning t m 3907) (meaning t m 3908) source

theorem rule5807 (p3319 p3917 p3918 : Prop) (h : (¬ p3917) ∨ (¬ p3918) ∨ (¬ p3319)) : (¬ p3319) ∨ (¬ p3917) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial5807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory406 (m.theta 1 6) (m.theta 2 6) (m.theta 6 9)
  exact rule5807 (meaning t m 3319) (meaning t m 3917) (meaning t m 3918) source

theorem rule5808 (p3166 p3414 p3919 : Prop) (h : (¬ p3919) ∨ (¬ p3166) ∨ (¬ p3414)) : (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3919) := by
  classical
  tauto

theorem initial5808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3919)) := by
  have source := ElevenTheory.theory407 (m.theta 0 3) (m.theta 3 7) (m.theta 3 8)
  exact rule5808 (meaning t m 3166) (meaning t m 3414) (meaning t m 3919) source

theorem rule5809 (p2573 p3389 p3920 : Prop) (h : (¬ p2573) ∨ (¬ p3920) ∨ p3389) : (¬ p2573) ∨ (p3389) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial5809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (meaning t m 3389) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory408 (m.theta 0 4) (m.theta 4 6) (m.theta 4 7)
  exact rule5809 (meaning t m 2573) (meaning t m 3389) (meaning t m 3920) source

theorem rule5810 (p2505 p2928 p3309 p3921 : Prop) (h : (¬ p3921) ∨ (¬ p2928) ∨ (¬ p3309) ∨ (¬ p2505)) : (¬ p2505) ∨ (¬ p2928) ∨ (¬ p3309) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial5810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory409 (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 6 7)
  exact rule5810 (meaning t m 2505) (meaning t m 2928) (meaning t m 3309) (meaning t m 3921) source

theorem rule5811 (p2656 p3389 p3742 : Prop) (h : (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3742)) : (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial5811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory410 (m.theta 0 4) (m.theta 3 4) (m.theta 4 7)
  exact rule5811 (meaning t m 2656) (meaning t m 3389) (meaning t m 3742) source

theorem rule5812 (p2579 p2662 p3016 : Prop) (h : (¬ p2662) ∨ (¬ p3016) ∨ (¬ p2579)) : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial5812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory411 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6)
  exact rule5812 (meaning t m 2579) (meaning t m 2662) (meaning t m 3016) source

theorem rule5813 (p2668 p3922 p3923 : Prop) (h : (¬ p3922) ∨ (¬ p2668) ∨ (¬ p3923)) : (¬ p2668) ∨ (¬ p3922) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial5813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory412 (m.theta 1 6) (m.theta 3 6) (m.theta 6 8)
  exact rule5813 (meaning t m 2668) (meaning t m 3922) (meaning t m 3923) source

theorem rule5814 (p2498 p2504 : Prop) (h : p2498 ∨ p2504) : (p2498) ∨ (p2504) := by
  classical
  tauto

theorem initial5814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2498) ∨ (meaning t m 2504) := by
  have source := ElevenTheory.theory413 (m.theta 1 6) (m.theta 4 6)
  exact rule5814 (meaning t m 2498) (meaning t m 2504) source

theorem rule5815 (p1658 p1664 : Prop) : (¬ p1658) ∨ ((p1658 ∨ p1664)) := by
  classical
  tauto

theorem initial5815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1658)) ∨ (meaning t m 3924) := by
  exact rule5815 (meaning t m 1658) (meaning t m 1664)

theorem rule5816 (p1658 p1664 : Prop) : (¬ p1664) ∨ ((p1658 ∨ p1664)) := by
  classical
  tauto

theorem initial5816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1664)) ∨ (meaning t m 3924) := by
  exact rule5816 (meaning t m 1658) (meaning t m 1664)

theorem rule5833 (p3924 p3925 : Prop) (h : (p3924 ↔ p3925)) : (¬ p3924) ∨ (p3925) := by
  classical
  tauto

theorem initial5833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3924)) ∨ (meaning t m 3925) := by
  have source := ElevenTheory.theory414 t (m.theta 3 10) (m.theta 3 7) (m.theta 7 10)
  exact rule5833 (meaning t m 3924) (meaning t m 3925) source

theorem rule5835 (p1670 p1676 : Prop) : (¬ p1670) ∨ ((p1670 ∨ p1676)) := by
  classical
  tauto

theorem initial5835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1670)) ∨ (meaning t m 3934) := by
  exact rule5835 (meaning t m 1670) (meaning t m 1676)

theorem rule5836 (p1670 p1676 : Prop) : (¬ p1676) ∨ ((p1670 ∨ p1676)) := by
  classical
  tauto

theorem initial5836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1676)) ∨ (meaning t m 3934) := by
  exact rule5836 (meaning t m 1670) (meaning t m 1676)

theorem rule5853 (p3934 p3935 : Prop) (h : (p3934 ↔ p3935)) : (¬ p3934) ∨ (p3935) := by
  classical
  tauto

theorem initial5853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3934)) ∨ (meaning t m 3935) := by
  have source := ElevenTheory.theory415 t (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule5853 (meaning t m 3934) (meaning t m 3935) source

theorem rule5855 (p2072 p3944 : Prop) (h : ((¬ p2072) ↔ (¬ p3944))) : (p2072) ∨ (¬ p3944) := by
  classical
  tauto

theorem initial5855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2072) ∨ (¬ (meaning t m 3944)) := by
  have source := ElevenTheory.theory416 t (m.theta 7 10)
  exact rule5855 (meaning t m 2072) (meaning t m 3944) source

theorem rule5857 (p2476 p2518 p3347 : Prop) (h : (¬ p3347) ∨ (¬ p2476) ∨ (¬ p2518)) : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial5857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory417 (m.theta 0 4) (m.theta 1 4) (m.theta 4 8)
  exact rule5857 (meaning t m 2476) (meaning t m 2518) (meaning t m 3347) source

theorem rule5858 (p3319 p3323 p3922 : Prop) (h : (¬ p3323) ∨ (¬ p3922) ∨ p3319) : (p3319) ∨ (¬ p3323) ∨ (¬ p3922) := by
  classical
  tauto

theorem initial5858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3319) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3922)) := by
  have source := ElevenTheory.theory418 (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule5858 (meaning t m 3319) (meaning t m 3323) (meaning t m 3922) source

theorem rule5859 (p3527 p3817 p3945 : Prop) (h : (¬ p3527) ∨ (¬ p3945) ∨ (¬ p3817)) : (¬ p3527) ∨ (¬ p3817) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial5859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory419 (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule5859 (meaning t m 3527) (meaning t m 3817) (meaning t m 3945) source

theorem rule5860 (p2579 p2656 p3574 : Prop) (h : (¬ p3574) ∨ (¬ p2656) ∨ p2579) : (p2579) ∨ (¬ p2656) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial5860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2579) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory420 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6)
  exact rule5860 (meaning t m 2579) (meaning t m 2656) (meaning t m 3574) source

theorem rule5861 (p3204 p3319 p3946 : Prop) (h : (¬ p3319) ∨ (¬ p3204) ∨ (¬ p3946)) : (¬ p3204) ∨ (¬ p3319) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial5861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory421 (m.theta 0 6) (m.theta 1 6) (m.theta 6 9)
  exact rule5861 (meaning t m 3204) (meaning t m 3319) (meaning t m 3946) source

theorem rule5862 (p2417 p3579 p3947 : Prop) (h : (¬ p2417) ∨ (¬ p3947) ∨ (¬ p3579)) : (¬ p2417) ∨ (¬ p3579) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial5862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory422 (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule5862 (meaning t m 2417) (meaning t m 3579) (meaning t m 3947) source

theorem rule5863 (p3369 p3370 p3379 p3948 : Prop) (h : (¬ p3370) ∨ (¬ p3379) ∨ (¬ p3369) ∨ (¬ p3948)) : (¬ p3369) ∨ (¬ p3370) ∨ (¬ p3379) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial5863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory423 (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5)
  exact rule5863 (meaning t m 3369) (meaning t m 3370) (meaning t m 3379) (meaning t m 3948) source

theorem rule5864 (p3949 p3950 p3951 : Prop) (h : (¬ p3949) ∨ (¬ p3950) ∨ p3951) : (¬ p3949) ∨ (¬ p3950) ∨ (p3951) := by
  classical
  tauto

theorem initial5864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 3950)) ∨ (meaning t m 3951) := by
  have source := ElevenTheory.theory424 t (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule5864 (meaning t m 3949) (meaning t m 3950) (meaning t m 3951) source

theorem rule5865 (p2951 p3646 p3952 : Prop) (h : (¬ p2951) ∨ (¬ p3952) ∨ p3646) : (¬ p2951) ∨ (p3646) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial5865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (meaning t m 3646) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory425 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule5865 (meaning t m 2951) (meaning t m 3646) (meaning t m 3952) source

theorem rule5866 (p3093 p3953 p3954 : Prop) (h : (¬ p3953) ∨ (¬ p3093) ∨ (¬ p3954)) : (¬ p3093) ∨ (¬ p3953) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial5866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory426 (m.theta 0 1) (m.theta 1 2) (m.theta 1 6)
  exact rule5866 (meaning t m 3093) (meaning t m 3953) (meaning t m 3954) source

theorem rule5867 (p2657 p2952 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2952) ∨ p2657) : (p2657) ∨ (¬ p2952) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial5867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2657) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory427 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule5867 (meaning t m 2657) (meaning t m 2952) (meaning t m 3413) source

theorem rule5868 (p2598 p3759 p3905 : Prop) (h : (¬ p2598) ∨ (¬ p3905) ∨ (¬ p3759)) : (¬ p2598) ∨ (¬ p3759) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial5868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory428 (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule5868 (meaning t m 2598) (meaning t m 3759) (meaning t m 3905) source

theorem rule5869 (p2753 p2774 p3688 : Prop) (h : (¬ p2753) ∨ (¬ p3688) ∨ (¬ p2774)) : (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial5869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory429 (m.theta 0 2) (m.theta 1 2) (m.theta 2 6)
  exact rule5869 (meaning t m 2753) (meaning t m 2774) (meaning t m 3688) source

theorem rule5870 (p2588 p3955 p3956 : Prop) (h : (¬ p3955) ∨ (¬ p2588) ∨ p3956) : (¬ p2588) ∨ (¬ p3955) ∨ (p3956) := by
  classical
  tauto

theorem initial5870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3955)) ∨ (meaning t m 3956) := by
  have source := ElevenTheory.theory430 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule5870 (meaning t m 2588) (meaning t m 3955) (meaning t m 3956) source

theorem rule5871 (p2507 p3957 p3958 : Prop) (h : (¬ p3957) ∨ (¬ p3958) ∨ p2507) : (p2507) ∨ (¬ p3957) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial5871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2507) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory431 t (m.theta 1 6) (m.theta 4 6) (m.theta 5 6)
  exact rule5871 (meaning t m 2507) (meaning t m 3957) (meaning t m 3958) source

theorem rule5872 (p2717 p3959 p3960 p3961 : Prop) (h : (¬ p3959) ∨ (¬ p2717) ∨ (¬ p3960) ∨ (¬ p3961)) : (¬ p2717) ∨ (¬ p3959) ∨ (¬ p3960) ∨ (¬ p3961) := by
  classical
  tauto

theorem initial5872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3961)) := by
  have source := ElevenTheory.theory432 (m.theta 0 7) (m.theta 0 8) (m.theta 2 7) (m.theta 7 8)
  exact rule5872 (meaning t m 2717) (meaning t m 3959) (meaning t m 3960) (meaning t m 3961) source

theorem rule5873 (p1682 p1688 : Prop) : (¬ p1682) ∨ ((p1682 ∨ p1688)) := by
  classical
  tauto

theorem initial5873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1682)) ∨ (meaning t m 3962) := by
  exact rule5873 (meaning t m 1682) (meaning t m 1688)

theorem rule5874 (p1682 p1688 : Prop) : (¬ p1688) ∨ ((p1682 ∨ p1688)) := by
  classical
  tauto

theorem initial5874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1688)) ∨ (meaning t m 3962) := by
  exact rule5874 (meaning t m 1682) (meaning t m 1688)

theorem rule5891 (p3962 p3963 : Prop) (h : (p3962 ↔ p3963)) : (¬ p3962) ∨ (p3963) := by
  classical
  tauto

theorem initial5891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3962)) ∨ (meaning t m 3963) := by
  have source := ElevenTheory.theory433 t (m.theta 5 10) (m.theta 5 8) (m.theta 8 10)
  exact rule5891 (meaning t m 3962) (meaning t m 3963) source

theorem rule5893 (p1694 p1700 : Prop) : (¬ p1694) ∨ ((p1694 ∨ p1700)) := by
  classical
  tauto

theorem initial5893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1694)) ∨ (meaning t m 3972) := by
  exact rule5893 (meaning t m 1694) (meaning t m 1700)

theorem rule5894 (p1694 p1700 : Prop) : (¬ p1700) ∨ ((p1694 ∨ p1700)) := by
  classical
  tauto

theorem initial5894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1700)) ∨ (meaning t m 3972) := by
  exact rule5894 (meaning t m 1694) (meaning t m 1700)

theorem rule5911 (p3972 p3973 : Prop) (h : (p3972 ↔ p3973)) : (¬ p3972) ∨ (p3973) := by
  classical
  tauto

theorem initial5911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3972)) ∨ (meaning t m 3973) := by
  have source := ElevenTheory.theory434 t (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule5911 (meaning t m 3972) (meaning t m 3973) source

theorem rule5913 (p2073 p3982 : Prop) (h : ((¬ p2073) ↔ (¬ p3982))) : (p2073) ∨ (¬ p3982) := by
  classical
  tauto

theorem initial5913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2073) ∨ (¬ (meaning t m 3982)) := by
  have source := ElevenTheory.theory435 t (m.theta 8 10)
  exact rule5913 (meaning t m 2073) (meaning t m 3982) source

theorem rule5915 (p2331 p2578 p3983 p3984 : Prop) (h : (¬ p3983) ∨ (¬ p2578) ∨ (¬ p2331) ∨ (¬ p3984)) : (¬ p2331) ∨ (¬ p2578) ∨ (¬ p3983) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial5915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory436 (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 4 6)
  exact rule5915 (meaning t m 2331) (meaning t m 2578) (meaning t m 3983) (meaning t m 3984) source

theorem rule5916 (p2132 p2753 p3688 p3985 : Prop) (h : (¬ p3985) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3688)) : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial5916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory437 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule5916 (meaning t m 2132) (meaning t m 2753) (meaning t m 3688) (meaning t m 3985) source

theorem rule5917 (p2246 p2742 p2811 : Prop) (h : (¬ p2246) ∨ (¬ p2742) ∨ p2811) : (¬ p2246) ∨ (¬ p2742) ∨ (p2811) := by
  classical
  tauto

theorem initial5917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2742)) ∨ (meaning t m 2811) := by
  have source := ElevenTheory.theory438 (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule5917 (meaning t m 2246) (meaning t m 2742) (meaning t m 2811) source

theorem rule5920 (p2373 p2563 p3988 : Prop) (h : (¬ p2373) ∨ (¬ p3988) ∨ p2563) : (¬ p2373) ∨ (p2563) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial5920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (meaning t m 2563) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory441 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule5920 (meaning t m 2373) (meaning t m 2563) (meaning t m 3988) source

theorem rule5925 (p1706 p1712 : Prop) : (¬ p1706) ∨ ((p1706 ∨ p1712)) := by
  classical
  tauto

theorem initial5925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1706)) ∨ (meaning t m 3991) := by
  exact rule5925 (meaning t m 1706) (meaning t m 1712)

theorem rule5926 (p1706 p1712 : Prop) : (¬ p1712) ∨ ((p1706 ∨ p1712)) := by
  classical
  tauto

theorem initial5926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1712)) ∨ (meaning t m 3991) := by
  exact rule5926 (meaning t m 1706) (meaning t m 1712)

theorem rule5943 (p3991 p3992 : Prop) (h : (p3991 ↔ p3992)) : (¬ p3991) ∨ (p3992) := by
  classical
  tauto

theorem initial5943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3991)) ∨ (meaning t m 3992) := by
  have source := ElevenTheory.theory446 t (m.theta 0 10) (m.theta 0 8) (m.theta 8 10)
  exact rule5943 (meaning t m 3991) (meaning t m 3992) source

theorem rule5946 (p2406 p2497 p2498 p3660 : Prop) (h : (¬ p2406) ∨ (¬ p2498) ∨ (¬ p3660) ∨ (¬ p2497)) : (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial5946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory448 (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6)
  exact rule5946 (meaning t m 2406) (meaning t m 2497) (meaning t m 2498) (meaning t m 3660) source

theorem rule5947 (p3570 p3644 p4001 : Prop) (h : (¬ p3570) ∨ (¬ p4001) ∨ p3644) : (¬ p3570) ∨ (p3644) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial5947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3570)) ∨ (meaning t m 3644) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory449 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule5947 (meaning t m 3570) (meaning t m 3644) (meaning t m 4001) source

end SunPrize.SMT
