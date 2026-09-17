import SunPrize.Certificate.Derived044
import SunPrize.Certificate.Logic045
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived90199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2352) ∨ (¬ p 2590) ∨ (¬ p 4539) ∨ (¬ p 2156) :=
  ElevenRUP.step90199 (p 2156) (p 2187) (p 2352) (p 2590) (p 3956) (p 4539) (derived73500 p h) (derived62573 p h)

theorem derived90202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3564) ∨ (¬ p 4342) :=
  ElevenRUP.step90202 (p 3483) (p 3564) (p 4137) (p 4342) (derived73524 p h) (h 20441)

theorem derived90205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 4031) ∨ (p 3201) ∨ (¬ p 4375) ∨ (p 3654) ∨ (¬ p 4198) ∨ (¬ p 4644) :=
  ElevenRUP.step90205 (p 3201) (p 3483) (p 3654) (p 3876) (p 3946) (p 4031) (p 4198) (p 4375) (p 4644) (derived73486 p h) (derived73492 p h) (derived51244 p h)

theorem derived90206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 3564) ∨ (¬ p 3483) ∨ (¬ p 2352) ∨ (¬ p 4375) :=
  ElevenRUP.step90206 (p 2352) (p 2598) (p 3483) (p 3564) (p 4137) (p 4375) (derived73524 p h) (derived46419 p h)

theorem derived90207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3125) ∨ (¬ p 4428) :=
  ElevenRUP.step90207 (p 3125) (p 3483) (p 3744) (p 4428) (derived73454 p h) (h 39073)

theorem derived90210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3146) ∨ (p 2819) ∨ (¬ p 4460) ∨ (¬ p 5379) ∨ (¬ p 4433) :=
  ElevenRUP.step90210 (p 2819) (p 3146) (p 3483) (p 3692) (p 4358) (p 4433) (p 4460) (p 5379) (derived73448 p h) (derived73564 p h) (derived49110 p h)

theorem derived90211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2122) ∨ (p 3654) ∨ (p 2177) :=
  ElevenRUP.step90211 (p 2122) (p 2177) (p 2299) (p 3483) (p 3654) (p 3822) (p 3946) (derived73472 p h) (derived73492 p h) (derived73234 p h) (derived45150 p h)

theorem derived90215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 2829) ∨ (p 2459) ∨ (¬ p 2608) ∨ (¬ p 4330) ∨ (p 3389) ∨ (p 2911) ∨ (¬ p 5193) :=
  ElevenRUP.step90215 (p 2459) (p 2608) (p 2829) (p 2911) (p 3389) (p 3483) (p 3540) (p 3644) (p 4330) (p 4348) (p 5193) (derived73562 p h) (derived73402 p h) (derived73434 p h) (derived64053 p h)

theorem derived90218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 4025) ∨ (p 2122) :=
  ElevenRUP.step90218 (p 2122) (p 3483) (p 3822) (p 4025) (derived73472 p h) (h 31898)

theorem derived90219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3564) ∨ (¬ p 4108) ∨ (p 2573) ∨ (p 2122) :=
  ElevenRUP.step90219 (p 2122) (p 2573) (p 2579) (p 3483) (p 3564) (p 3822) (p 4108) (p 4137) (derived73524 p h) (derived73274 p h) (derived73472 p h) (derived56503 p h)

theorem derived90221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2122) ∨ (¬ p 2315) ∨ (p 3516) :=
  ElevenRUP.step90221 (p 2122) (p 2315) (p 3483) (p 3516) (p 3821) (p 3822) (derived73472 p h) (derived73470 p h) (derived66009 p h)

theorem derived90222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3654) ∨ (p 2819) ∨ (¬ p 4503) ∨ (¬ p 5015) ∨ (¬ p 2901) ∨ (¬ p 2248) ∨ (¬ p 2946) ∨ (¬ p 2881) :=
  ElevenRUP.step90222 (p 2248) (p 2819) (p 2881) (p 2901) (p 2946) (p 3483) (p 3654) (p 3946) (p 4358) (p 4503) (p 5015) (derived73492 p h) (derived73564 p h) (derived57361 p h)

theorem derived90226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5503) ∨ (¬ p 3483) ∨ (¬ p 3461) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2774) ∨ (p 2437) ∨ (¬ p 2753) ∨ (¬ p 4831) ∨ (p 2651) :=
  ElevenRUP.step90226 (p 2252) (p 2437) (p 2651) (p 2657) (p 2750) (p 2753) (p 2774) (p 3461) (p 3483) (p 3742) (p 4831) (p 5503) (derived73452 p h) (derived73288 p h) (derived50996 p h)

theorem derived90233 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3483) ∨ (¬ p 3461) ∨ (p 2819) :=
  ElevenRUP.step90233 (p 2819) (p 3266) (p 3461) (p 3483) (p 4358) (p 4444) (derived73580 p h) (derived73564 p h) (derived53458 p h)

theorem derived90234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3483) ∨ (¬ p 4345) ∨ (p 2819) ∨ (¬ p 5118) :=
  ElevenRUP.step90234 (p 2819) (p 3483) (p 4345) (p 4358) (p 5118) (p 5580) (derived73564 p h) (derived50994 p h)

theorem derived90235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3146) ∨ (¬ p 5193) ∨ (¬ p 2829) ∨ (p 2373) ∨ (¬ p 2608) ∨ (¬ p 4330) ∨ (p 2230) :=
  ElevenRUP.step90235 (p 2230) (p 2373) (p 2589) (p 2608) (p 2829) (p 3146) (p 3483) (p 3692) (p 3880) (p 4330) (p 5193) (derived73448 p h) (derived73490 p h) (derived73284 p h) (derived59221 p h)

theorem derived90236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 4623) ∨ (p 3516) ∨ (¬ p 2315) ∨ (p 2122) :=
  ElevenRUP.step90236 (p 2122) (p 2315) (p 3483) (p 3516) (p 3821) (p 3822) (p 4623) (derived73470 p h) (derived73472 p h) (derived48783 p h)

theorem derived90237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2641) ∨ (p 2819) ∨ (¬ p 2667) ∨ (p 3654) :=
  ElevenRUP.step90237 (p 2641) (p 2667) (p 2819) (p 3483) (p 3654) (p 3946) (p 4154) (p 4358) (derived73526 p h) (derived73564 p h) (derived73492 p h) (derived46614 p h)

theorem derived90242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2088) ∨ (¬ p 3858) ∨ (¬ p 4995) ∨ (¬ p 4345) ∨ (p 2819) :=
  ElevenRUP.step90242 (p 2088) (p 2819) (p 3483) (p 3857) (p 3858) (p 4345) (p 4358) (p 4995) (derived73480 p h) (derived73564 p h) (derived58817 p h)

theorem derived90243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3564) ∨ (p 2573) ∨ (¬ p 3905) ∨ (p 2819) :=
  ElevenRUP.step90243 (p 2573) (p 2579) (p 2819) (p 3483) (p 3564) (p 3905) (p 4137) (p 4358) (derived73524 p h) (derived73274 p h) (derived73564 p h) (derived54417 p h)

theorem derived90245 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3483) ∨ (p 2122) ∨ (¬ p 3461) :=
  ElevenRUP.step90245 (p 2122) (p 3461) (p 3483) (p 3707) (p 3822) (p 4321) (derived73554 p h) (derived73472 p h) (derived58594 p h)

theorem derived90246 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3483) ∨ (¬ p 3461) ∨ (p 2122) ∨ (¬ p 3440) :=
  ElevenRUP.step90246 (p 2122) (p 3440) (p 3461) (p 3483) (p 3707) (p 3822) (p 4321) (derived73554 p h) (derived73472 p h) (derived47524 p h)

theorem derived90247 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3483) ∨ (¬ p 2829) ∨ (¬ p 2187) :=
  ElevenRUP.step90247 (p 2187) (p 2829) (p 3125) (p 3483) (p 3744) (derived73454 p h) (derived58033 p h)

theorem derived90248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 3483) ∨ (¬ p 3093) ∨ (p 2819) :=
  ElevenRUP.step90248 (p 2819) (p 3063) (p 3093) (p 3483) (p 4358) (derived73564 p h) (derived43570 p h)

theorem derived90250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3323) ∨ (¬ p 3986) ∨ (p 2563) ∨ (p 2819) :=
  ElevenRUP.step90250 (p 2563) (p 2819) (p 3323) (p 3483) (p 3986) (p 4037) (p 4110) (p 4358) (derived73508 p h) (derived73516 p h) (derived73564 p h) (derived58008 p h)

theorem derived90251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5299) ∨ (¬ p 3483) ∨ (p 2122) ∨ (p 2449) ∨ (¬ p 5379) :=
  ElevenRUP.step90251 (p 2122) (p 2449) (p 3483) (p 3822) (p 3947) (p 5299) (p 5379) (derived73472 p h) (derived73494 p h) (derived71840 p h)

theorem derived90253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2122) ∨ (¬ p 2274) ∨ (¬ p 3461) :=
  ElevenRUP.step90253 (p 2122) (p 2274) (p 3461) (p 3483) (p 3822) (derived73472 p h) (derived44985 p h)

theorem derived90258 (p : Nat → Prop) (h : Inputs p) :
    (p 3343) ∨ (¬ p 3483) ∨ (¬ p 4022) ∨ (¬ p 3016) ∨ (¬ p 5225) :=
  ElevenRUP.step90258 (p 3016) (p 3343) (p 3359) (p 3483) (p 4022) (p 5225) (derived73388 p h) (derived55236 p h)

theorem derived90263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3619) ∨ (p 3156) ∨ (p 2598) ∨ (¬ p 3276) ∨ (¬ p 5164) ∨ (¬ p 5123) ∨ (¬ p 3361) ∨ (¬ p 4749) ∨ (p 2946) :=
  ElevenRUP.step90263 (p 2598) (p 2946) (p 2952) (p 3055) (p 3156) (p 3276) (p 3361) (p 3497) (p 3619) (p 4749) (p 5123) (p 5164) (p 5568) (derived73400 p h) (derived73350 p h) (derived73330 p h) (derived53369 p h)

theorem derived90265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 3379) ∨ (¬ p 3590) ∨ (¬ p 2737) ∨ (¬ p 4749) :=
  ElevenRUP.step90265 (p 2608) (p 2737) (p 3379) (p 3452) (p 3590) (p 4749) (derived73394 p h) (derived51216 p h)

theorem derived90269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 2406) ∨ (¬ p 4749) ∨ (¬ p 2230) ∨ (¬ p 4257) ∨ (¬ p 3759) :=
  ElevenRUP.step90269 (p 2230) (p 2406) (p 2737) (p 3238) (p 3759) (p 4257) (p 4749) (derived73374 p h) (derived48020 p h)

theorem derived90270 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 3516) ∨ (p 2598) ∨ (¬ p 4357) ∨ (¬ p 4749) ∨ (¬ p 3819) :=
  ElevenRUP.step90270 (p 2598) (p 3055) (p 3434) (p 3516) (p 3819) (p 4324) (p 4357) (p 4749) (derived73556 p h) (derived73350 p h) (derived54787 p h)

theorem derived90272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2668) ∨ (¬ p 4972) ∨ (p 2383) ∨ (¬ p 2630) ∨ (¬ p 2785) :=
  ElevenRUP.step90272 (p 2383) (p 2387) (p 2630) (p 2668) (p 2785) (p 4841) (p 4972) (derived73246 p h) (derived42143 p h)

theorem derived90277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 3319) ∨ (¬ p 4116) ∨ (¬ p 3136) ∨ (¬ p 2505) ∨ (¬ p 4841) :=
  ElevenRUP.step90277 (p 2505) (p 3136) (p 3319) (p 3917) (p 4116) (p 4704) (p 4841) (derived73046 p h) (derived52019 p h)

theorem derived90280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2668) ∨ (¬ p 4972) ∨ (p 2819) ∨ (¬ p 2630) :=
  ElevenRUP.step90280 (p 2630) (p 2668) (p 2819) (p 4358) (p 4841) (p 4972) (derived73564 p h) (derived52693 p h)

theorem derived90283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (p 2122) ∨ (¬ p 3567) ∨ (¬ p 4972) ∨ (¬ p 2307) ∨ (¬ p 2630) :=
  ElevenRUP.step90283 (p 2122) (p 2307) (p 2630) (p 3567) (p 3822) (p 4841) (p 4972) (derived73472 p h) (derived52981 p h)

theorem derived90285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2307) ∨ (¬ p 2630) ∨ (¬ p 2951) ∨ (p 2122) ∨ (¬ p 2962) :=
  ElevenRUP.step90285 (p 2122) (p 2307) (p 2630) (p 2951) (p 2962) (p 3822) (p 4841) (derived73472 p h) (derived69676 p h)

theorem derived90286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2668) ∨ (¬ p 2751) ∨ (¬ p 2246) ∨ (p 2819) ∨ (¬ p 2331) :=
  ElevenRUP.step90286 (p 2246) (p 2331) (p 2668) (p 2751) (p 2819) (p 4358) (p 4841) (derived73564 p h) (derived41901 p h)

theorem derived90289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2307) ∨ (p 2598) ∨ (¬ p 4749) ∨ (p 2122) ∨ (¬ p 2786) :=
  ElevenRUP.step90289 (p 2122) (p 2307) (p 2598) (p 2786) (p 3055) (p 3822) (p 4749) (p 4841) (derived73350 p h) (derived73472 p h) (derived51084 p h)

theorem derived90290 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 4841) ∨ (p 2132) ∨ (¬ p 2786) ∨ (¬ p 2307) :=
  ElevenRUP.step90290 (p 2122) (p 2132) (p 2138) (p 2307) (p 2786) (p 3822) (p 4841) (derived73472 p h) (derived73214 p h) (derived67288 p h)

theorem derived90293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 2295) ∨ (p 2122) ∨ (¬ p 4790) ∨ (¬ p 2331) :=
  ElevenRUP.step90293 (p 2122) (p 2295) (p 2331) (p 3822) (p 4790) (p 4841) (derived73472 p h) (derived53138 p h)

theorem derived90294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 4841) ∨ (¬ p 2641) ∨ (p 2819) ∨ (¬ p 2751) ∨ (¬ p 3567) :=
  ElevenRUP.step90294 (p 2383) (p 2641) (p 2751) (p 2819) (p 3567) (p 4358) (p 4841) (derived73564 p h) (derived42561 p h)

theorem derived90296 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 4841) ∨ (¬ p 2608) ∨ (¬ p 4869) ∨ (¬ p 3309) ∨ (¬ p 2630) :=
  ElevenRUP.step90296 (p 2122) (p 2608) (p 2630) (p 3309) (p 3822) (p 4841) (p 4869) (derived73472 p h) (derived45441 p h)

theorem derived90297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 4869) ∨ (¬ p 4841) ∨ (p 2819) ∨ (p 3367) ∨ (¬ p 4749) :=
  ElevenRUP.step90297 (p 2819) (p 3063) (p 3367) (p 3585) (p 4358) (p 4749) (p 4841) (p 4869) (derived73564 p h) (derived73428 p h) (derived42126 p h)

theorem derived90300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2881) ∨ (¬ p 4204) ∨ (¬ p 4401) ∨ (¬ p 2177) :=
  ElevenRUP.step90300 (p 2122) (p 2177) (p 2881) (p 3570) (p 4204) (p 4401) (derived73418 p h) (derived63893 p h)

theorem derived90302 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (p 2331) ∨ (¬ p 2122) ∨ (¬ p 4426) :=
  ElevenRUP.step90302 (p 2122) (p 2295) (p 2331) (p 2963) (p 3568) (p 4426) (derived73416 p h) (derived73338 p h) (derived71841 p h)

theorem derived90306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2573) ∨ (p 2553) ∨ (¬ p 4375) :=
  ElevenRUP.step90306 (p 2122) (p 2553) (p 2573) (p 2579) (p 2588) (p 4375) (derived73274 p h) (derived73282 p h) (derived71843 p h)

theorem derived90310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (¬ p 3564) ∨ (¬ p 2774) :=
  ElevenRUP.step90310 (p 2122) (p 2553) (p 2588) (p 2774) (p 3564) (derived73282 p h) (derived47424 p h)

theorem derived90314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3422) ∨ (p 2553) ∨ (p 2598) :=
  ElevenRUP.step90314 (p 2122) (p 2553) (p 2588) (p 2598) (p 3055) (p 3422) (p 3584) (derived73426 p h) (derived73282 p h) (derived73350 p h) (derived47616 p h)

theorem derived90316 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2782) ∨ (¬ p 2311) :=
  ElevenRUP.step90316 (p 2122) (p 2177) (p 2311) (p 2341) (p 2782) (p 3551) (derived73408 p h) (derived41852 p h)

theorem derived90318 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2122) ∨ (¬ p 2785) :=
  ElevenRUP.step90318 (p 2122) (p 2307) (p 2313) (p 2785) (derived73238 p h) (h 6273)

theorem derived90319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (¬ p 2352) ∨ (¬ p 2774) :=
  ElevenRUP.step90319 (p 2122) (p 2352) (p 2553) (p 2588) (p 2774) (derived73282 p h) (derived45001 p h)

theorem derived90326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2829) ∨ (p 2274) ∨ (¬ p 2187) :=
  ElevenRUP.step90326 (p 2122) (p 2187) (p 2274) (p 2829) (p 3097) (derived73352 p h) (derived58539 p h)

theorem derived90328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2187) ∨ (p 2274) :=
  ElevenRUP.step90328 (p 2122) (p 2187) (p 2274) (p 2774) (p 3097) (derived73352 p h) (derived45000 p h)

theorem derived90329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2331) ∨ (¬ p 2298) ∨ (p 2807) ∨ (¬ p 4846) :=
  ElevenRUP.step90329 (p 2122) (p 2298) (p 2331) (p 2807) (p 3414) (p 4846) (derived73392 p h) (derived42061 p h)

theorem derived90330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2122) ∨ (¬ p 4489) ∨ (p 2819) ∨ (p 2274) :=
  ElevenRUP.step90330 (p 2122) (p 2274) (p 2383) (p 2819) (p 3097) (p 4358) (p 4489) (derived73564 p h) (derived73352 p h) (derived50978 p h)

theorem derived90332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2241) ∨ (¬ p 2744) ∨ (¬ p 2518) ∨ (¬ p 4596) ∨ (¬ p 3366) ∨ (p 2307) ∨ (¬ p 2778) ∨ (p 2819) ∨ (¬ p 3379) :=
  ElevenRUP.step90332 (p 2122) (p 2241) (p 2247) (p 2307) (p 2313) (p 2518) (p 2744) (p 2778) (p 2819) (p 3366) (p 3379) (p 4358) (p 4596) (derived73226 p h) (derived73238 p h) (derived73564 p h) (derived52802 p h)

theorem derived90333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3093) ∨ (p 2819) ∨ (p 3309) :=
  ElevenRUP.step90333 (p 2122) (p 2819) (p 3093) (p 3309) (p 3549) (p 3591) (p 4358) (derived73432 p h) (derived73564 p h) (derived73406 p h) (derived46207 p h)

theorem derived90335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2459) ∨ (p 2307) ∨ (p 2819) ∨ (¬ p 4138) :=
  ElevenRUP.step90335 (p 2122) (p 2307) (p 2313) (p 2459) (p 2819) (p 4138) (p 4348) (p 4358) (derived73562 p h) (derived73238 p h) (derived73564 p h) (derived47631 p h)

theorem derived90337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2312) ∨ (¬ p 3016) ∨ (¬ p 4279) ∨ (p 2819) ∨ (p 2437) :=
  ElevenRUP.step90337 (p 2122) (p 2312) (p 2437) (p 2819) (p 3016) (p 3742) (p 4279) (p 4358) (derived73564 p h) (derived73452 p h) (derived47037 p h)

theorem derived90338 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2122) ∨ (p 2307) ∨ (¬ p 4419) ∨ (¬ p 3083) ∨ (¬ p 2230) ∨ (¬ p 2440) ∨ (¬ p 4596) ∨ (p 2819) :=
  ElevenRUP.step90338 (p 2122) (p 2230) (p 2307) (p 2313) (p 2440) (p 2778) (p 2819) (p 3083) (p 4358) (p 4419) (p 4596) (derived73238 p h) (derived73564 p h) (derived42334 p h)

theorem derived90339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 2122) ∨ (p 2819) ∨ (¬ p 3093) :=
  ElevenRUP.step90339 (p 2122) (p 2819) (p 3063) (p 3093) (p 4358) (derived73564 p h) (derived45613 p h)

theorem derived90340 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (p 2819) ∨ (¬ p 3083) ∨ (¬ p 5021) ∨ (¬ p 2727) ∨ (¬ p 4596) ∨ (¬ p 2241) ∨ (¬ p 2122) :=
  ElevenRUP.step90340 (p 2122) (p 2241) (p 2307) (p 2313) (p 2727) (p 2819) (p 3083) (p 4358) (p 4596) (p 5021) (derived73238 p h) (derived73564 p h) (derived63608 p h)

theorem derived90342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3379) ∨ (¬ p 4666) ∨ (¬ p 4733) ∨ (¬ p 2177) ∨ (p 2922) ∨ (¬ p 2774) ∨ (p 2417) :=
  ElevenRUP.step90342 (p 2122) (p 2177) (p 2417) (p 2774) (p 2922) (p 2928) (p 3379) (p 3452) (p 4278) (p 4666) (p 4733) (derived73394 p h) (derived73320 p h) (derived73546 p h) (derived51460 p h)

theorem derived90344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2383) ∨ (p 2307) ∨ (¬ p 2829) :=
  ElevenRUP.step90344 (p 2122) (p 2307) (p 2313) (p 2383) (p 2829) (derived73238 p h) (derived55042 p h)

theorem derived90346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (p 2307) ∨ (¬ p 3953) ∨ (¬ p 2663) ∨ (¬ p 2122) ∨ (¬ p 2744) ∨ (¬ p 3879) ∨ (¬ p 3204) ∨ (¬ p 2230) ∨ (¬ p 3917) ∨ (¬ p 4604) :=
  ElevenRUP.step90346 (p 2122) (p 2230) (p 2246) (p 2307) (p 2313) (p 2663) (p 2744) (p 3146) (p 3156) (p 3204) (p 3879) (p 3917) (p 3953) (p 4604) (derived73238 p h) (derived61320 p h)

theorem derived90348 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 2122) ∨ (¬ p 2352) ∨ (¬ p 4375) ∨ (p 2553) :=
  ElevenRUP.step90348 (p 2122) (p 2352) (p 2553) (p 2588) (p 3367) (p 4375) (derived73282 p h) (derived45031 p h)

theorem derived90349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2608) ∨ (¬ p 2829) ∨ (p 2274) :=
  ElevenRUP.step90349 (p 2122) (p 2274) (p 2608) (p 2829) (p 3097) (derived73352 p h) (derived42773 p h)

theorem derived90350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (¬ p 2608) ∨ (¬ p 2829) :=
  ElevenRUP.step90350 (p 2122) (p 2553) (p 2588) (p 2608) (p 2829) (derived73282 p h) (derived43780 p h)

theorem derived90351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2829) ∨ (¬ p 2608) ∨ (p 2563) ∨ (p 2187) ∨ (p 2230) ∨ (¬ p 5193) :=
  ElevenRUP.step90351 (p 2122) (p 2187) (p 2230) (p 2563) (p 2589) (p 2608) (p 2829) (p 3989) (p 4110) (p 5193) (derived73516 p h) (derived73502 p h) (derived73284 p h) (derived71844 p h)

theorem derived90353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2839) ∨ (p 2274) ∨ (¬ p 2122) :=
  ElevenRUP.step90353 (p 2122) (p 2274) (p 2829) (p 2839) (p 3097) (p 3583) (derived73424 p h) (derived73352 p h) (derived45947 p h)

theorem derived90354 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2761) ∨ (¬ p 2122) ∨ (¬ p 4733) ∨ (p 2982) ∨ (p 2406) ∨ (¬ p 2774) ∨ (¬ p 2396) :=
  ElevenRUP.step90354 (p 2122) (p 2396) (p 2406) (p 2761) (p 2774) (p 2982) (p 3238) (p 3379) (p 3452) (p 4733) (p 4948) (derived73394 p h) (derived73846 p h) (derived73374 p h) (derived51452 p h)

theorem derived90355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2307) ∨ (p 2284) ∨ (¬ p 5053) ∨ (¬ p 4356) ∨ (¬ p 3985) :=
  ElevenRUP.step90355 (p 2122) (p 2284) (p 2307) (p 2313) (p 3952) (p 3985) (p 4356) (p 5053) (derived73238 p h) (derived73496 p h) (derived62774 p h)

theorem derived90359 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2122) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (¬ p 2750) ∨ (p 2528) ∨ (p 3083) :=
  ElevenRUP.step90359 (p 2122) (p 2252) (p 2396) (p 2528) (p 2534) (p 2651) (p 2657) (p 2750) (p 2829) (p 3083) (p 3950) (p 4256) (derived73288 p h) (derived73268 p h) (derived73542 p h) (derived53852 p h)

theorem derived90362 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2122) ∨ (p 2307) ∨ (¬ p 2651) ∨ (¬ p 2373) ∨ (¬ p 4786) ∨ (p 2440) ∨ (¬ p 2778) ∨ (¬ p 4433) :=
  ElevenRUP.step90362 (p 2122) (p 2307) (p 2313) (p 2373) (p 2440) (p 2542) (p 2651) (p 2778) (p 2819) (p 4358) (p 4433) (p 4786) (derived73564 p h) (derived73238 p h) (derived73270 p h) (derived63614 p h)

theorem derived90363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (p 2598) ∨ (¬ p 2774) :=
  ElevenRUP.step90363 (p 2122) (p 2553) (p 2588) (p 2598) (p 2774) (p 3055) (derived73282 p h) (derived73350 p h) (derived52739 p h)

theorem derived90364 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2651) ∨ (¬ p 2774) ∨ (¬ p 4789) ∨ (p 2911) ∨ (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 4668) :=
  ElevenRUP.step90364 (p 2122) (p 2396) (p 2437) (p 2651) (p 2657) (p 2774) (p 2911) (p 3644) (p 3742) (p 4668) (p 4789) (derived73452 p h) (derived73288 p h) (derived73434 p h) (derived63211 p h)

theorem derived90365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3575) ∨ (¬ p 4712) ∨ (¬ p 2122) ∨ (¬ p 4138) ∨ (p 2819) :=
  ElevenRUP.step90365 (p 2122) (p 2341) (p 2819) (p 3575) (p 4138) (p 4358) (p 4712) (derived73564 p h) (derived40962 p h)

theorem derived90368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 2122) ∨ (¬ p 4138) ∨ (¬ p 4559) ∨ (p 2819) :=
  ElevenRUP.step90368 (p 2122) (p 2819) (p 2881) (p 4138) (p 4358) (p 4559) (derived73564 p h) (derived50991 p h)

theorem derived90369 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 2122) ∨ (¬ p 2088) ∨ (¬ p 4078) ∨ (¬ p 4170) :=
  ElevenRUP.step90369 (p 2088) (p 2122) (p 3609) (p 4078) (p 4170) (p 4340) (derived73558 p h) (derived71845 p h)

theorem derived90372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2122) ∨ (¬ p 3146) ∨ (¬ p 4604) ∨ (¬ p 2946) ∨ (p 2307) ∨ (¬ p 3917) ∨ (¬ p 3156) ∨ (¬ p 4786) :=
  ElevenRUP.step90372 (p 2122) (p 2307) (p 2313) (p 2778) (p 2946) (p 3146) (p 3156) (p 3917) (p 4604) (p 4786) (derived73238 p h) (derived59730 p h)

theorem derived90374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2307) ∨ (¬ p 2667) ∨ (¬ p 4975) ∨ (¬ p 4426) ∨ (p 2630) :=
  ElevenRUP.step90374 (p 2122) (p 2307) (p 2313) (p 2630) (p 2667) (p 2810) (p 4426) (p 4975) (derived73238 p h) (derived73316 p h) (derived50659 p h)

theorem derived90375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2122) ∨ (p 2307) ∨ (¬ p 2829) :=
  ElevenRUP.step90375 (p 2122) (p 2307) (p 2313) (p 2778) (p 2829) (p 4734) (derived73238 p h) (derived72735 p h) (derived49739 p h)

theorem derived90376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (p 2307) ∨ (¬ p 2122) ∨ (¬ p 4842) ∨ (¬ p 2696) :=
  ElevenRUP.step90376 (p 2122) (p 2307) (p 2313) (p 2696) (p 2778) (p 4842) (derived73238 p h) (derived42129 p h)

theorem derived90378 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2122) ∨ (p 3136) ∨ (¬ p 2662) ∨ (¬ p 4426) ∨ (¬ p 2577) :=
  ElevenRUP.step90378 (p 2122) (p 2307) (p 2313) (p 2577) (p 2662) (p 3136) (p 4315) (p 4426) (derived73238 p h) (derived73550 p h) (derived69677 p h)

theorem derived90379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2122) ∨ (p 2630) ∨ (p 2307) ∨ (¬ p 4426) :=
  ElevenRUP.step90379 (p 2122) (p 2307) (p 2313) (p 2383) (p 2630) (p 2810) (p 4426) (derived73316 p h) (derived73238 p h) (derived55526 p h)

theorem derived90381 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2437) ∨ (p 2417) ∨ (¬ p 2122) ∨ (¬ p 4666) ∨ (¬ p 2774) ∨ (¬ p 2177) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (¬ p 2750) :=
  ElevenRUP.step90381 (p 2122) (p 2177) (p 2252) (p 2417) (p 2437) (p 2651) (p 2657) (p 2750) (p 2753) (p 2774) (p 3742) (p 4278) (p 4666) (derived73288 p h) (derived73452 p h) (derived73546 p h) (derived42300 p h)

theorem derived90385 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2122) ∨ (p 2819) ∨ (¬ p 2778) ∨ (p 2307) :=
  ElevenRUP.step90385 (p 2122) (p 2307) (p 2313) (p 2363) (p 2778) (p 2819) (p 4347) (p 4358) (derived73560 p h) (derived73564 p h) (derived73238 p h) (derived55907 p h)

theorem derived90386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2819) ∨ (¬ p 2563) ∨ (p 2427) ∨ (¬ p 4275) :=
  ElevenRUP.step90386 (p 2122) (p 2427) (p 2563) (p 2819) (p 4235) (p 4275) (p 4358) (derived73564 p h) (derived73536 p h) (derived47045 p h)

theorem derived90387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2274) ∨ (¬ p 4885) ∨ (p 2563) :=
  ElevenRUP.step90387 (p 2122) (p 2274) (p 2563) (p 3097) (p 4110) (p 4885) (derived73352 p h) (derived73516 p h) (derived68235 p h)

theorem derived90389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2449) ∨ (¬ p 2312) ∨ (¬ p 2122) ∨ (¬ p 4846) ∨ (¬ p 4067) :=
  ElevenRUP.step90389 (p 2122) (p 2312) (p 2449) (p 3516) (p 3947) (p 4067) (p 4846) (derived73494 p h) (derived41716 p h)

theorem derived90391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3379) ∨ (p 2406) ∨ (¬ p 4733) ∨ (¬ p 2774) ∨ (¬ p 2761) ∨ (¬ p 2396) ∨ (p 2563) :=
  ElevenRUP.step90391 (p 2122) (p 2396) (p 2406) (p 2563) (p 2761) (p 2774) (p 3238) (p 3379) (p 3452) (p 4110) (p 4733) (derived73394 p h) (derived73374 p h) (derived73516 p h) (derived64211 p h)

theorem derived90392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2122) ∨ (¬ p 2651) ∨ (¬ p 3366) ∨ (¬ p 4604) ∨ (¬ p 3083) ∨ (¬ p 2528) ∨ (p 2307) ∨ (¬ p 2744) ∨ (¬ p 2246) ∨ (¬ p 3917) :=
  ElevenRUP.step90392 (p 2122) (p 2246) (p 2307) (p 2313) (p 2528) (p 2651) (p 2744) (p 2778) (p 3083) (p 3366) (p 3917) (p 4604) (derived73238 p h) (derived52873 p h)

theorem derived90394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3146) ∨ (¬ p 2177) ∨ (¬ p 3661) ∨ (p 3256) ∨ (¬ p 2245) ∨ (¬ p 4733) ∨ (p 2946) ∨ (¬ p 4905) :=
  ElevenRUP.step90394 (p 2122) (p 2177) (p 2245) (p 2774) (p 2946) (p 2952) (p 3146) (p 3256) (p 3661) (p 4118) (p 4733) (p 4905) (derived73520 p h) (derived73330 p h) (derived50341 p h)

theorem derived90395 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2396) ∨ (p 2230) ∨ (p 2373) ∨ (¬ p 3950) ∨ (¬ p 2122) ∨ (¬ p 4729) ∨ (¬ p 2774) :=
  ElevenRUP.step90395 (p 2122) (p 2230) (p 2373) (p 2396) (p 2589) (p 2774) (p 3146) (p 3692) (p 3880) (p 3950) (p 4729) (derived73448 p h) (derived73284 p h) (derived73490 p h) (derived56267 p h)

theorem derived90397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3791) ∨ (p 2230) ∨ (¬ p 4826) ∨ (p 2982) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 4729) :=
  ElevenRUP.step90397 (p 2122) (p 2230) (p 2589) (p 2774) (p 2982) (p 3791) (p 4322) (p 4729) (p 4826) (p 4948) (derived73284 p h) (derived73846 p h) (derived54923 p h)

theorem derived90401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2274) ∨ (¬ p 5043) ∨ (¬ p 2143) ∨ (¬ p 3985) ∨ (¬ p 4032) :=
  ElevenRUP.step90401 (p 2122) (p 2143) (p 2274) (p 3097) (p 3985) (p 4032) (p 5043) (derived73352 p h) (derived54773 p h)

theorem derived90404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 4375) ∨ (p 2553) ∨ (¬ p 4753) ∨ (p 3016) :=
  ElevenRUP.step90404 (p 2122) (p 2553) (p 2588) (p 3016) (p 3574) (p 4375) (p 4753) (derived73282 p h) (derived73422 p h) (derived55260 p h)

theorem derived90406 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3589) ∨ (¬ p 4718) ∨ (¬ p 3985) ∨ (p 2274) ∨ (¬ p 3083) ∨ (¬ p 5193) ∨ (p 2470) ∨ (p 3016) ∨ (¬ p 2132) :=
  ElevenRUP.step90406 (p 2122) (p 2132) (p 2274) (p 2470) (p 2476) (p 3016) (p 3083) (p 3097) (p 3574) (p 3589) (p 3985) (p 4718) (p 5193) (derived73352 p h) (derived73250 p h) (derived73422 p h) (derived54713 p h)

theorem derived90407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 2753) ∨ (p 3115) ∨ (¬ p 2122) ∨ (¬ p 2252) ∨ (p 2946) ∨ (¬ p 4322) ∨ (¬ p 4826) ∨ (¬ p 2750) ∨ (¬ p 2774) :=
  ElevenRUP.step90407 (p 2122) (p 2252) (p 2750) (p 2753) (p 2774) (p 2946) (p 2952) (p 3115) (p 3791) (p 4208) (p 4322) (p 4826) (derived73534 p h) (derived73330 p h) (derived64928 p h)

theorem derived90408 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3115) ∨ (¬ p 4316) ∨ (¬ p 4368) ∨ (¬ p 4842) ∨ (p 2839) ∨ (¬ p 2122) ∨ (¬ p 2753) ∨ (p 2553) ∨ (¬ p 2696) :=
  ElevenRUP.step90408 (p 2122) (p 2553) (p 2588) (p 2696) (p 2753) (p 2839) (p 3115) (p 3564) (p 3583) (p 4208) (p 4316) (p 4368) (p 4842) (derived73534 p h) (derived73424 p h) (derived73282 p h) (derived42123 p h)

theorem derived90410 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 4427) ∨ (¬ p 4867) ∨ (¬ p 3093) ∨ (¬ p 2122) :=
  ElevenRUP.step90410 (p 2122) (p 3093) (p 3399) (p 4366) (p 4427) (p 4867) (derived73570 p h) (derived48825 p h)

theorem derived90411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3032) ∨ (p 2449) ∨ (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (p 3399) ∨ (¬ p 2774) ∨ (¬ p 4666) :=
  ElevenRUP.step90411 (p 2122) (p 2177) (p 2241) (p 2449) (p 2750) (p 2753) (p 2774) (p 3032) (p 3399) (p 3947) (p 4366) (p 4666) (derived73494 p h) (derived73570 p h) (derived63241 p h)

theorem derived90412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 2122) ∨ (p 3399) ∨ (¬ p 2774) ∨ (¬ p 4666) ∨ (p 3631) ∨ (¬ p 3379) ∨ (¬ p 2177) :=
  ElevenRUP.step90412 (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 3399) (p 3631) (p 3817) (p 4366) (p 4666) (derived73570 p h) (derived73468 p h) (derived71846 p h)

theorem derived90414 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 3950) ∨ (¬ p 2774) ∨ (¬ p 2396) ∨ (¬ p 2241) ∨ (p 3449) ∨ (¬ p 2753) ∨ (¬ p 2122) ∨ (¬ p 2750) :=
  ElevenRUP.step90414 (p 2122) (p 2241) (p 2396) (p 2750) (p 2753) (p 2774) (p 3073) (p 3449) (p 3860) (p 3950) (p 4261) (derived73544 p h) (derived73482 p h) (derived63263 p h)

theorem derived90416 (p : Nat → Prop) (h : Inputs p) :
    (p 3309) ∨ (¬ p 2774) ∨ (¬ p 3063) ∨ (¬ p 2122) :=
  ElevenRUP.step90416 (p 2122) (p 2774) (p 3063) (p 3309) (p 3549) (derived73406 p h) (derived43488 p h)

theorem derived90418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2241) ∨ (¬ p 2774) ∨ (¬ p 4733) ∨ (p 3156) ∨ (¬ p 2177) ∨ (¬ p 4905) ∨ (p 2992) :=
  ElevenRUP.step90418 (p 2122) (p 2177) (p 2241) (p 2247) (p 2774) (p 2992) (p 3156) (p 3497) (p 3662) (p 4733) (p 4905) (derived73226 p h) (derived73400 p h) (derived73440 p h) (derived61963 p h)

theorem derived90420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2778) ∨ (p 2307) ∨ (p 2819) ∨ (¬ p 2122) :=
  ElevenRUP.step90420 (p 2122) (p 2307) (p 2313) (p 2778) (p 2819) (p 4358) (p 5580) (derived73238 p h) (derived73564 p h) (derived46935 p h)

theorem derived90422 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 2528) ∨ (¬ p 2252) ∨ (¬ p 3950) ∨ (¬ p 2774) ∨ (p 3083) ∨ (¬ p 2122) ∨ (p 2651) ∨ (¬ p 2396) ∨ (¬ p 2750) :=
  ElevenRUP.step90422 (p 2122) (p 2252) (p 2396) (p 2528) (p 2534) (p 2651) (p 2657) (p 2750) (p 2753) (p 2774) (p 3083) (p 3950) (p 4256) (derived73268 p h) (derived73542 p h) (derived73288 p h) (derived64521 p h)

theorem derived90424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3309) ∨ (¬ p 4375) ∨ (¬ p 3953) ∨ (¬ p 2598) :=
  ElevenRUP.step90424 (p 2122) (p 2598) (p 3309) (p 3549) (p 3953) (p 4375) (derived73406 p h) (derived71849 p h)

theorem derived90427 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 4866) :=
  ElevenRUP.step90427 (p 2829) (p 4865) (p 4866) (derived73798 p h) (h 8001)

theorem derived90428 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 4867) :=
  ElevenRUP.step90428 (p 2829) (p 4865) (p 4867) (derived73798 p h) (h 8002)

theorem derived90429 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 4889) :=
  ElevenRUP.step90429 (p 2829) (p 3688) (p 4889) (derived73444 p h) (derived45394 p h)

theorem derived90430 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 2274) ∨ (p 2122) :=
  ElevenRUP.step90430 (p 2122) (p 2274) (p 2608) (p 2829) (p 3688) (p 3822) (p 3954) (derived73444 p h) (derived73498 p h) (derived73472 p h) (derived61829 p h)

theorem derived90432 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2187) ∨ (¬ p 5190) ∨ (p 2608) ∨ (¬ p 2230) ∨ (¬ p 4405) ∨ (p 2829) ∨ (¬ p 2563) :=
  ElevenRUP.step90432 (p 2122) (p 2187) (p 2230) (p 2563) (p 2608) (p 2829) (p 3688) (p 3822) (p 3954) (p 4405) (p 5190) (derived73472 p h) (derived73498 p h) (derived73444 p h) (derived48159 p h)

theorem derived90437 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (p 2829) ∨ (¬ p 2177) ∨ (¬ p 2737) ∨ (¬ p 2785) ∨ (¬ p 2311) :=
  ElevenRUP.step90437 (p 2177) (p 2311) (p 2341) (p 2737) (p 2785) (p 2829) (p 3551) (p 3688) (derived73408 p h) (derived73444 p h) (derived45278 p h)

theorem derived90438 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (p 2829) ∨ (¬ p 2737) ∨ (¬ p 2785) ∨ (p 2177) :=
  ElevenRUP.step90438 (p 2177) (p 2299) (p 2307) (p 2313) (p 2737) (p 2785) (p 2829) (p 3688) (derived73238 p h) (derived73444 p h) (derived73234 p h) (derived55086 p h)

theorem derived90439 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2839) ∨ (¬ p 2774) ∨ (p 2598) :=
  ElevenRUP.step90439 (p 2598) (p 2774) (p 2829) (p 2839) (p 3055) (p 3688) (derived73444 p h) (derived73350 p h) (derived45271 p h)

theorem derived90443 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3367) ∨ (¬ p 4342) ∨ (¬ p 3016) ∨ (¬ p 4750) :=
  ElevenRUP.step90443 (p 2829) (p 3016) (p 3367) (p 3688) (p 4342) (p 4750) (derived73444 p h) (derived59243 p h)

theorem derived90444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4342) ∨ (p 2829) ∨ (¬ p 3367) ∨ (¬ p 2573) ∨ (¬ p 4730) :=
  ElevenRUP.step90444 (p 2573) (p 2829) (p 3367) (p 3688) (p 4342) (p 4730) (derived73444 p h) (derived41027 p h)

theorem derived90446 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2295) ∨ (p 2829) ∨ (¬ p 2737) ∨ (¬ p 2785) :=
  ElevenRUP.step90446 (p 2295) (p 2307) (p 2313) (p 2737) (p 2785) (p 2829) (p 3688) (derived73238 p h) (derived73444 p h) (derived56182 p h)

theorem derived90448 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2177) ∨ (¬ p 2785) ∨ (p 2829) ∨ (p 2307) :=
  ElevenRUP.step90448 (p 2177) (p 2299) (p 2307) (p 2313) (p 2459) (p 2785) (p 2829) (p 3688) (p 4348) (derived73562 p h) (derived73234 p h) (derived73444 p h) (derived73238 p h) (derived43869 p h)

theorem derived90450 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2785) ∨ (p 2177) ∨ (p 2307) ∨ (¬ p 3590) ∨ (¬ p 4902) ∨ (¬ p 2406) ∨ (p 2829) ∨ (¬ p 2598) :=
  ElevenRUP.step90450 (p 2177) (p 2299) (p 2307) (p 2313) (p 2373) (p 2406) (p 2598) (p 2785) (p 2829) (p 3590) (p 3688) (p 4902) (derived73234 p h) (derived73238 p h) (derived73444 p h) (derived71851 p h)

theorem derived90452 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3654) ∨ (¬ p 2785) ∨ (p 2829) ∨ (¬ p 2737) :=
  ElevenRUP.step90452 (p 2737) (p 2785) (p 2829) (p 3461) (p 3654) (p 3688) (p 3946) (p 4191) (derived73530 p h) (derived73492 p h) (derived73444 p h) (derived59180 p h)

theorem derived90454 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 3917) ∨ (¬ p 2248) ∨ (¬ p 2264) ∨ (¬ p 4604) ∨ (¬ p 2459) ∨ (¬ p 2807) :=
  ElevenRUP.step90454 (p 2248) (p 2264) (p 2459) (p 2608) (p 2807) (p 2829) (p 3688) (p 3917) (p 3954) (p 4604) (derived73444 p h) (derived73498 p h) (derived48846 p h)

theorem derived90455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2829) ∨ (¬ p 2341) ∨ (p 2608) ∨ (¬ p 4521) ∨ (p 2881) ∨ (¬ p 4625) ∨ (¬ p 4988) ∨ (¬ p 3917) :=
  ElevenRUP.step90455 (p 2341) (p 2608) (p 2829) (p 2881) (p 3246) (p 3570) (p 3688) (p 3917) (p 3954) (p 4521) (p 4625) (p 4988) (derived73444 p h) (derived73498 p h) (derived73418 p h) (derived42419 p h)

theorem derived90458 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2122) ∨ (p 2177) ∨ (¬ p 2737) :=
  ElevenRUP.step90458 (p 2122) (p 2177) (p 2299) (p 2737) (p 2829) (p 3688) (p 3822) (derived73444 p h) (derived73472 p h) (derived73234 p h) (derived55085 p h)

theorem derived90459 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (p 2122) ∨ (p 2177) :=
  ElevenRUP.step90459 (p 2122) (p 2177) (p 2299) (p 2608) (p 2829) (p 3688) (p 3822) (p 3954) (derived73444 p h) (derived73498 p h) (derived73472 p h) (derived73234 p h) (derived45136 p h)

theorem derived90460 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (¬ p 4475) ∨ (p 2352) ∨ (¬ p 4342) :=
  ElevenRUP.step90460 (p 2352) (p 2707) (p 2829) (p 3688) (p 3956) (p 4342) (p 4475) (derived73444 p h) (derived73500 p h) (derived71853 p h)

theorem derived90461 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2363) ∨ (¬ p 2785) ∨ (p 2383) ∨ (p 3266) :=
  ElevenRUP.step90461 (p 2363) (p 2383) (p 2387) (p 2785) (p 2829) (p 3266) (p 3688) (p 4347) (p 4444) (derived73444 p h) (derived73560 p h) (derived73246 p h) (derived73580 p h) (derived42942 p h)

theorem derived90463 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2383) ∨ (¬ p 2459) ∨ (p 2829) ∨ (¬ p 2785) :=
  ElevenRUP.step90463 (p 2363) (p 2383) (p 2387) (p 2459) (p 2785) (p 2829) (p 3688) (p 4347) (derived73560 p h) (derived73246 p h) (derived73444 p h) (derived43317 p h)

theorem derived90464 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2829) ∨ (¬ p 2785) ∨ (p 2383) ∨ (¬ p 2737) :=
  ElevenRUP.step90464 (p 2363) (p 2383) (p 2387) (p 2737) (p 2785) (p 2829) (p 3688) (p 4347) (derived73560 p h) (derived73444 p h) (derived73246 p h) (derived58533 p h)

theorem derived90467 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4337) ∨ (p 2363) ∨ (p 2829) ∨ (p 2668) ∨ (¬ p 2737) :=
  ElevenRUP.step90467 (p 2363) (p 2668) (p 2737) (p 2829) (p 3324) (p 3688) (p 4337) (p 4347) (derived73560 p h) (derived73444 p h) (derived73386 p h) (derived57281 p h)

theorem derived90468 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2829) ∨ (p 2668) ∨ (¬ p 2737) ∨ (¬ p 2785) ∨ (¬ p 3567) :=
  ElevenRUP.step90468 (p 2363) (p 2668) (p 2737) (p 2785) (p 2829) (p 3324) (p 3567) (p 3688) (p 4347) (derived73560 p h) (derived73444 p h) (derived73386 p h) (derived42797 p h)

theorem derived90469 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 2331) ∨ (¬ p 4337) ∨ (¬ p 2248) :=
  ElevenRUP.step90469 (p 2248) (p 2331) (p 2608) (p 2829) (p 3688) (p 3954) (p 4337) (derived73444 p h) (derived73498 p h) (derived51450 p h)

theorem derived90470 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2819) ∨ (¬ p 2651) ∨ (p 2608) ∨ (¬ p 2911) ∨ (¬ p 4503) ∨ (¬ p 2248) ∨ (¬ p 2437) :=
  ElevenRUP.step90470 (p 2248) (p 2437) (p 2608) (p 2651) (p 2819) (p 2829) (p 2911) (p 3688) (p 3954) (p 4358) (p 4503) (derived73444 p h) (derived73564 p h) (derived73498 p h) (derived61558 p h)

theorem derived90471 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2651) ∨ (¬ p 2248) ∨ (¬ p 3016) ∨ (¬ p 4405) ∨ (p 2829) ∨ (p 2608) ∨ (¬ p 2352) :=
  ElevenRUP.step90471 (p 2122) (p 2248) (p 2352) (p 2608) (p 2651) (p 2829) (p 3016) (p 3688) (p 3822) (p 3954) (p 4405) (derived73472 p h) (derived73444 p h) (derived73498 p h) (derived62552 p h)

theorem derived90472 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3589) ∨ (p 2241) ∨ (¬ p 2774) ∨ (¬ p 2744) :=
  ElevenRUP.step90472 (p 2241) (p 2247) (p 2744) (p 2774) (p 2829) (p 3589) (p 3688) (derived73444 p h) (derived73226 p h) (derived52716 p h)

theorem derived90476 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2946) ∨ (¬ p 4842) ∨ (¬ p 3361) ∨ (¬ p 2749) ∨ (p 2829) :=
  ElevenRUP.step90476 (p 2749) (p 2829) (p 2946) (p 2952) (p 2992) (p 3361) (p 3688) (p 4842) (derived73330 p h) (derived73444 p h) (derived41472 p h)

theorem derived90477 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2829) ∨ (¬ p 2748) ∨ (¬ p 4842) ∨ (¬ p 2241) :=
  ElevenRUP.step90477 (p 2241) (p 2608) (p 2748) (p 2829) (p 3688) (p 3954) (p 4842) (derived73498 p h) (derived73444 p h) (derived49201 p h)

theorem derived90481 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3364) ∨ (¬ p 2406) ∨ (¬ p 2774) ∨ (¬ p 3541) ∨ (p 2850) :=
  ElevenRUP.step90481 (p 2406) (p 2774) (p 2829) (p 2850) (p 3364) (p 3541) (p 3684) (p 3688) (derived73444 p h) (derived73442 p h) (derived56631 p h)

theorem derived90483 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3367) ∨ (p 2396) ∨ (¬ p 2785) ∨ (p 2307) :=
  ElevenRUP.step90483 (p 2307) (p 2313) (p 2396) (p 2785) (p 2829) (p 3367) (p 3688) (p 4107) (derived73444 p h) (derived73514 p h) (derived73238 p h) (derived45325 p h)

theorem derived90484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3654) ∨ (p 2829) ∨ (¬ p 2785) ∨ (¬ p 2737) :=
  ElevenRUP.step90484 (p 2737) (p 2785) (p 2829) (p 3323) (p 3654) (p 3688) (p 3946) (derived73492 p h) (derived73444 p h) (derived56175 p h)

theorem derived90487 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3917) ∨ (¬ p 3389) ∨ (p 2608) ∨ (¬ p 5190) ∨ (¬ p 2459) ∨ (¬ p 4604) ∨ (¬ p 2911) :=
  ElevenRUP.step90487 (p 2459) (p 2608) (p 2829) (p 2911) (p 3389) (p 3688) (p 3917) (p 3954) (p 4604) (p 5190) (derived73444 p h) (derived73498 p h) (derived42234 p h)

theorem derived90492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (p 2341) ∨ (¬ p 2311) ∨ (¬ p 2406) ∨ (¬ p 2598) ∨ (¬ p 3590) ∨ (¬ p 2427) ∨ (p 2829) ∨ (¬ p 4556) ∨ (¬ p 2177) :=
  ElevenRUP.step90492 (p 2177) (p 2311) (p 2341) (p 2406) (p 2427) (p 2598) (p 2785) (p 2829) (p 3551) (p 3590) (p 3688) (p 4556) (derived73408 p h) (derived73444 p h) (derived71856 p h)

theorem derived90493 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (p 2829) ∨ (¬ p 2311) ∨ (¬ p 2785) ∨ (¬ p 2177) ∨ (p 2396) :=
  ElevenRUP.step90493 (p 2177) (p 2311) (p 2341) (p 2396) (p 2785) (p 2829) (p 3551) (p 3688) (p 4107) (derived73408 p h) (derived73444 p h) (derived73514 p h) (derived54910 p h)

theorem derived90497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2230) ∨ (p 2819) ∨ (p 2608) ∨ (¬ p 2881) ∨ (¬ p 5190) ∨ (¬ p 4503) ∨ (p 2829) :=
  ElevenRUP.step90497 (p 2230) (p 2427) (p 2608) (p 2819) (p 2829) (p 2881) (p 3688) (p 3954) (p 4358) (p 4503) (p 5190) (derived73564 p h) (derived73498 p h) (derived73444 p h) (derived55910 p h)

theorem derived90502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4329) ∨ (¬ p 2449) ∨ (¬ p 2248) ∨ (¬ p 2761) ∨ (p 2608) ∨ (¬ p 5254) ∨ (p 2829) ∨ (¬ p 2807) :=
  ElevenRUP.step90502 (p 2248) (p 2449) (p 2608) (p 2761) (p 2807) (p 2829) (p 3688) (p 3954) (p 4329) (p 5254) (derived73498 p h) (derived73444 p h) (derived48847 p h)

theorem derived90503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 2608) ∨ (¬ p 4556) ∨ (¬ p 2248) ∨ (¬ p 2807) ∨ (p 3246) ∨ (p 2829) ∨ (p 2122) :=
  ElevenRUP.step90503 (p 2122) (p 2248) (p 2449) (p 2608) (p 2807) (p 2829) (p 3246) (p 3688) (p 3690) (p 3822) (p 3954) (p 4556) (derived73498 p h) (derived73446 p h) (derived73444 p h) (derived73472 p h) (derived57790 p h)

theorem derived90505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 2881) ∨ (p 2829) ∨ (p 2122) ∨ (¬ p 2807) ∨ (¬ p 2248) ∨ (p 2608) ∨ (¬ p 4556) :=
  ElevenRUP.step90505 (p 2122) (p 2248) (p 2264) (p 2608) (p 2807) (p 2829) (p 2881) (p 3570) (p 3688) (p 3822) (p 3954) (p 4556) (derived73418 p h) (derived73444 p h) (derived73472 p h) (derived73498 p h) (derived63777 p h)

theorem derived90506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2829) ∨ (¬ p 4902) ∨ (¬ p 2742) ∨ (p 2307) ∨ (¬ p 3156) ∨ (p 2177) ∨ (¬ p 2696) ∨ (¬ p 2785) :=
  ElevenRUP.step90506 (p 2177) (p 2299) (p 2307) (p 2313) (p 2696) (p 2742) (p 2785) (p 2829) (p 2992) (p 3156) (p 3688) (p 4902) (derived73444 p h) (derived73238 p h) (derived73234 p h) (derived71857 p h)

theorem derived90511 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2829) ∨ (¬ p 2737) ∨ (¬ p 2363) ∨ (¬ p 4078) :=
  ElevenRUP.step90511 (p 2363) (p 2737) (p 2829) (p 3609) (p 3688) (p 4078) (p 4340) (derived73558 p h) (derived73444 p h) (derived61940 p h)

theorem derived90512 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 4503) ∨ (¬ p 4078) ∨ (p 3609) ∨ (¬ p 2363) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3740) ∨ (¬ p 2264) :=
  ElevenRUP.step90512 (p 2264) (p 2363) (p 2598) (p 2829) (p 3201) (p 3609) (p 3688) (p 3740) (p 4078) (p 4340) (p 4503) (derived73444 p h) (derived73558 p h) (derived71859 p h)

theorem derived90513 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (¬ p 3589) ∨ (¬ p 2774) ∨ (p 2807) ∨ (¬ p 4895) ∨ (p 2264) ∨ (¬ p 2254) ∨ (¬ p 2881) :=
  ElevenRUP.step90513 (p 2254) (p 2264) (p 2707) (p 2774) (p 2807) (p 2829) (p 2881) (p 3414) (p 3553) (p 3589) (p 3688) (p 4895) (derived73444 p h) (derived73392 p h) (derived73410 p h) (derived57326 p h)

theorem derived90518 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2819) ∨ (p 2829) ∨ (p 2608) :=
  ElevenRUP.step90518 (p 2363) (p 2608) (p 2819) (p 2829) (p 3688) (p 3954) (p 4347) (p 4358) (derived73560 p h) (derived73564 p h) (derived73444 p h) (derived73498 p h) (derived45745 p h)

theorem derived90520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2187) ∨ (p 2829) ∨ (p 2819) :=
  ElevenRUP.step90520 (p 2187) (p 2737) (p 2819) (p 2829) (p 3688) (p 4358) (derived73444 p h) (derived73564 p h) (derived46806 p h)

theorem derived90521 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3125) ∨ (¬ p 3367) ∨ (¬ p 2785) ∨ (p 2829) :=
  ElevenRUP.step90521 (p 2785) (p 2829) (p 3125) (p 3367) (p 3654) (p 3688) (p 3946) (derived73492 p h) (derived73444 p h) (derived62153 p h)

theorem derived90522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4337) ∨ (p 2295) ∨ (p 2829) ∨ (¬ p 2737) ∨ (¬ p 2274) :=
  ElevenRUP.step90522 (p 2274) (p 2295) (p 2737) (p 2829) (p 3568) (p 3688) (p 4337) (derived73416 p h) (derived73444 p h) (derived45314 p h)

theorem derived90523 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3246) ∨ (¬ p 2901) ∨ (¬ p 4625) ∨ (¬ p 3917) ∨ (¬ p 2248) ∨ (¬ p 2946) ∨ (p 2608) :=
  ElevenRUP.step90523 (p 2248) (p 2608) (p 2829) (p 2901) (p 2946) (p 3246) (p 3688) (p 3917) (p 3954) (p 4625) (derived73444 p h) (derived73498 p h) (derived48891 p h)

theorem derived90524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2819) ∨ (p 2829) ∨ (p 2608) :=
  ElevenRUP.step90524 (p 2352) (p 2608) (p 2819) (p 2829) (p 3688) (p 3954) (p 4358) (derived73564 p h) (derived73444 p h) (derived73498 p h) (derived48680 p h)

theorem derived90525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 2829) ∨ (¬ p 2352) ∨ (p 2819) :=
  ElevenRUP.step90525 (p 2352) (p 2819) (p 2829) (p 3367) (p 3688) (p 4358) (derived73444 p h) (derived73564 p h) (derived43129 p h)

theorem derived90526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2829) ∨ (p 2819) ∨ (¬ p 2737) :=
  ElevenRUP.step90526 (p 2668) (p 2737) (p 2819) (p 2829) (p 3688) (p 4358) (derived73444 p h) (derived73564 p h) (derived46604 p h)

theorem derived90527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2737) ∨ (p 2829) :=
  ElevenRUP.step90527 (p 2383) (p 2737) (p 2819) (p 2829) (p 3688) (p 4358) (derived73564 p h) (derived73444 p h) (derived54551 p h)

theorem derived90528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4337) ∨ (p 2696) ∨ (¬ p 2737) ∨ (¬ p 3873) ∨ (p 2829) ∨ (p 2295) :=
  ElevenRUP.step90528 (p 2295) (p 2696) (p 2737) (p 2829) (p 3365) (p 3568) (p 3688) (p 3873) (p 4337) (derived73390 p h) (derived73444 p h) (derived73416 p h) (derived46353 p h)

theorem derived90529 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (p 2696) ∨ (¬ p 4752) ∨ (¬ p 3367) :=
  ElevenRUP.step90529 (p 2696) (p 2774) (p 2829) (p 3365) (p 3367) (p 3688) (p 4752) (derived73444 p h) (derived73390 p h) (derived41411 p h)

theorem derived90530 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (¬ p 3367) ∨ (p 2696) :=
  ElevenRUP.step90530 (p 2696) (p 2774) (p 2829) (p 3365) (p 3367) (p 3688) (derived73444 p h) (derived73390 p h) (derived58527 p h)

theorem derived90533 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3266) ∨ (p 2819) ∨ (p 2829) ∨ (¬ p 3322) :=
  ElevenRUP.step90533 (p 2819) (p 2829) (p 3266) (p 3322) (p 3461) (p 3688) (p 4191) (p 4358) (derived73530 p h) (derived73564 p h) (derived73444 p h) (derived42938 p h)

theorem derived90534 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (p 3461) ∨ (¬ p 3917) :=
  ElevenRUP.step90534 (p 2608) (p 2829) (p 3461) (p 3688) (p 3917) (p 3954) (p 4191) (derived73444 p h) (derived73498 p h) (derived73530 p h) (derived57451 p h)

theorem derived90537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 2829) ∨ (¬ p 5119) ∨ (p 3461) ∨ (¬ p 2744) ∨ (¬ p 3449) ∨ (p 2241) ∨ (¬ p 3917) :=
  ElevenRUP.step90537 (p 2241) (p 2247) (p 2744) (p 2829) (p 3449) (p 3461) (p 3688) (p 3917) (p 4181) (p 4191) (p 5119) (derived73444 p h) (derived73530 p h) (derived73226 p h) (derived52553 p h)

theorem derived90538 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2248) ∨ (p 2819) ∨ (p 2459) ∨ (¬ p 4503) ∨ (p 2608) ∨ (¬ p 4044) ∨ (¬ p 2807) ∨ (¬ p 3256) :=
  ElevenRUP.step90538 (p 2248) (p 2459) (p 2608) (p 2807) (p 2819) (p 2829) (p 3256) (p 3688) (p 3954) (p 4044) (p 4348) (p 4358) (p 4503) (derived73444 p h) (derived73564 p h) (derived73562 p h) (derived73498 p h) (derived55626 p h)

theorem derived90542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (p 2363) ∨ (p 2241) ∨ (p 2819) ∨ (¬ p 4288) ∨ (p 2829) ∨ (¬ p 3449) ∨ (¬ p 5122) ∨ (¬ p 2744) :=
  ElevenRUP.step90542 (p 2241) (p 2247) (p 2363) (p 2744) (p 2819) (p 2829) (p 3449) (p 3688) (p 4009) (p 4288) (p 4347) (p 4358) (p 5122) (derived73560 p h) (derived73226 p h) (derived73564 p h) (derived73444 p h) (derived52555 p h)

theorem derived90544 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2753) ∨ (¬ p 2774) :=
  ElevenRUP.step90544 (p 2753) (p 2774) (p 2829) (p 3688) (derived73444 p h) (h 5869)

theorem derived90545 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 4326) ∨ (¬ p 2098) ∨ (¬ p 4405) ∨ (p 2122) ∨ (¬ p 2753) :=
  ElevenRUP.step90545 (p 2098) (p 2122) (p 2753) (p 2829) (p 3688) (p 3822) (p 4326) (p 4405) (derived73444 p h) (derived73472 p h) (derived41859 p h)

theorem derived90548 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2829) ∨ (¬ p 4030) ∨ (¬ p 5221) ∨ (¬ p 3379) :=
  ElevenRUP.step90548 (p 2608) (p 2829) (p 3379) (p 3688) (p 3954) (p 4030) (p 5221) (derived73498 p h) (derived73444 p h) (derived48001 p h)

theorem derived90550 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3367) ∨ (p 2122) ∨ (p 2598) :=
  ElevenRUP.step90550 (p 2122) (p 2598) (p 2829) (p 3055) (p 3367) (p 3688) (p 3822) (derived73444 p h) (derived73472 p h) (derived73350 p h) (derived57432 p h)

theorem derived90551 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2307) ∨ (¬ p 2785) ∨ (¬ p 3367) ∨ (p 2177) :=
  ElevenRUP.step90551 (p 2177) (p 2299) (p 2307) (p 2313) (p 2785) (p 2829) (p 3367) (p 3688) (derived73444 p h) (derived73238 p h) (derived73234 p h) (derived45360 p h)

theorem derived90552 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 2311) ∨ (¬ p 2785) ∨ (¬ p 3367) ∨ (¬ p 2396) ∨ (p 2829) :=
  ElevenRUP.step90552 (p 2311) (p 2396) (p 2785) (p 2829) (p 3367) (p 3516) (p 3688) (p 3821) (derived73470 p h) (derived73444 p h) (derived48813 p h)

theorem derived90555 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2578) ∨ (¬ p 3367) ∨ (p 2352) ∨ (p 2829) ∨ (¬ p 2785) :=
  ElevenRUP.step90555 (p 2352) (p 2363) (p 2578) (p 2785) (p 2829) (p 3367) (p 3688) (p 3956) (p 4347) (derived73560 p h) (derived73500 p h) (derived73444 p h) (derived45358 p h)

theorem derived90558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2829) ∨ (¬ p 3367) ∨ (¬ p 2774) :=
  ElevenRUP.step90558 (p 2774) (p 2829) (p 3367) (p 3425) (p 3688) (derived73444 p h) (derived52413 p h)

theorem derived90559 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2307) ∨ (¬ p 2785) ∨ (¬ p 3367) ∨ (¬ p 2553) :=
  ElevenRUP.step90559 (p 2307) (p 2313) (p 2553) (p 2785) (p 2829) (p 3367) (p 3688) (derived73444 p h) (derived73238 p h) (derived43976 p h)

theorem derived90562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2829) ∨ (¬ p 4604) ∨ (¬ p 3917) ∨ (p 2608) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 2248) :=
  ElevenRUP.step90562 (p 2248) (p 2528) (p 2608) (p 2651) (p 2829) (p 3083) (p 3688) (p 3917) (p 3954) (p 4604) (derived73444 p h) (derived73498 p h) (derived61615 p h)

theorem derived90568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2829) ∨ (p 2819) ∨ (¬ p 3873) ∨ (¬ p 3425) :=
  ElevenRUP.step90568 (p 2707) (p 2819) (p 2829) (p 3425) (p 3688) (p 3873) (p 4358) (derived73444 p h) (derived73564 p h) (derived63653 p h)

theorem derived90570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4503) ∨ (¬ p 3146) ∨ (p 2819) ∨ (p 2829) ∨ (p 2459) ∨ (¬ p 4521) ∨ (¬ p 2220) ∨ (p 2608) :=
  ElevenRUP.step90570 (p 2220) (p 2459) (p 2608) (p 2819) (p 2829) (p 3146) (p 3688) (p 3954) (p 4348) (p 4358) (p 4503) (p 4521) (derived73564 p h) (derived73444 p h) (derived73562 p h) (derived73498 p h) (derived54462 p h)

theorem derived90572 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2248) ∨ (¬ p 2187) ∨ (¬ p 4405) ∨ (p 2829) ∨ (¬ p 2284) ∨ (¬ p 2946) ∨ (p 2608) :=
  ElevenRUP.step90572 (p 2122) (p 2187) (p 2248) (p 2284) (p 2608) (p 2829) (p 2946) (p 3688) (p 3822) (p 3954) (p 4405) (derived73472 p h) (derived73444 p h) (derived73498 p h) (derived49142 p h)

theorem derived90577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4114) ∨ (¬ p 5017) ∨ (p 2608) ∨ (p 2829) ∨ (¬ p 4113) ∨ (p 2819) :=
  ElevenRUP.step90577 (p 2608) (p 2819) (p 2829) (p 3688) (p 3954) (p 4113) (p 4114) (p 4358) (p 5017) (derived73498 p h) (derived73444 p h) (derived73564 p h) (derived46734 p h)

theorem derived90578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 2352) ∨ (p 2383) ∨ (p 2829) ∨ (p 2553) :=
  ElevenRUP.step90578 (p 2352) (p 2383) (p 2387) (p 2553) (p 2588) (p 2785) (p 2829) (p 3688) (derived73246 p h) (derived73444 p h) (derived73282 p h) (derived43016 p h)

theorem derived90582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2786) ∨ (p 2132) ∨ (p 2829) :=
  ElevenRUP.step90582 (p 2132) (p 2138) (p 2383) (p 2786) (p 2819) (p 2829) (p 3688) (p 4358) (derived73564 p h) (derived73214 p h) (derived73444 p h) (derived43470 p h)

theorem derived90583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2962) ∨ (¬ p 2144) ∨ (p 2829) :=
  ElevenRUP.step90583 (p 2144) (p 2383) (p 2819) (p 2829) (p 2962) (p 3688) (p 4358) (derived73564 p h) (derived73444 p h) (derived71862 p h)

theorem derived90585 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (p 2553) ∨ (¬ p 5225) ∨ (¬ p 4475) :=
  ElevenRUP.step90585 (p 2553) (p 2588) (p 2707) (p 2829) (p 3688) (p 4475) (p 5225) (derived73444 p h) (derived73282 p h) (derived48335 p h)

theorem derived90586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4475) ∨ (p 2829) ∨ (¬ p 2707) ∨ (¬ p 4401) ∨ (p 2274) :=
  ElevenRUP.step90586 (p 2274) (p 2707) (p 2829) (p 3097) (p 3688) (p 4401) (p 4475) (derived73444 p h) (derived73352 p h) (derived53794 p h)

theorem derived90587 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2829) ∨ (¬ p 4117) ∨ (¬ p 3987) ∨ (¬ p 2307) :=
  ElevenRUP.step90587 (p 2122) (p 2307) (p 2829) (p 3688) (p 3822) (p 3987) (p 4117) (derived73472 p h) (derived73444 p h) (derived71863 p h)

theorem derived90589 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2122) ∨ (p 2608) ∨ (¬ p 3309) :=
  ElevenRUP.step90589 (p 2122) (p 2608) (p 2829) (p 3309) (p 3688) (p 3822) (p 3954) (derived73444 p h) (derived73472 p h) (derived73498 p h) (derived47436 p h)

theorem derived90590 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 2553) ∨ (p 2122) ∨ (¬ p 3660) :=
  ElevenRUP.step90590 (p 2122) (p 2553) (p 2608) (p 2829) (p 3660) (p 3688) (p 3822) (p 3954) (derived73444 p h) (derived73498 p h) (derived73472 p h) (derived57259 p h)

theorem derived90592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2860) ∨ (p 2427) ∨ (¬ p 4885) ∨ (p 2156) :=
  ElevenRUP.step90592 (p 2156) (p 2427) (p 2860) (p 3051) (p 3646) (p 4235) (p 4885) (derived73536 p h) (derived73436 p h) (derived49013 p h)

theorem derived90593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2590) ∨ (¬ p 2274) ∨ (¬ p 4885) ∨ (p 2553) :=
  ElevenRUP.step90593 (p 2274) (p 2553) (p 2588) (p 2590) (p 2860) (p 4885) (derived73282 p h) (derived41068 p h)

theorem derived90597 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2440) ∨ (¬ p 3743) ∨ (¬ p 2386) ∨ (¬ p 4885) ∨ (¬ p 2860) :=
  ElevenRUP.step90597 (p 2386) (p 2440) (p 2542) (p 2860) (p 3016) (p 3574) (p 3743) (p 4885) (derived73422 p h) (derived73270 p h) (derived42203 p h)

theorem derived90598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2619) ∨ (¬ p 4885) ∨ (p 2220) ∨ (p 2427) :=
  ElevenRUP.step90598 (p 2220) (p 2427) (p 2619) (p 3051) (p 4120) (p 4235) (p 4885) (derived73522 p h) (derived73536 p h) (derived54726 p h)

theorem derived90601 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2437) ∨ (¬ p 4885) ∨ (¬ p 4001) ∨ (p 2440) :=
  ElevenRUP.step90601 (p 2437) (p 2440) (p 2542) (p 2870) (p 3742) (p 4001) (p 4885) (derived73452 p h) (derived73270 p h) (derived51317 p h)

theorem derived90603 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3083) ∨ (p 2440) ∨ (¬ p 4885) :=
  ElevenRUP.step90603 (p 2440) (p 2542) (p 2619) (p 3083) (p 4885) (p 5007) (derived73872 p h) (derived73270 p h) (derived65955 p h)

theorem derived90607 (p : Nat → Prop) (h : Inputs p) :
    (p 3590) ∨ (p 3367) :=
  ElevenRUP.step90607 (p 3367) (p 3590) (p 6046) (derived74385 p h) (h 13275)

theorem derived90608 (p : Nat → Prop) (h : Inputs p) :
    (p 4257) ∨ (p 3367) :=
  ElevenRUP.step90608 (p 3367) (p 4257) (p 6046) (derived74385 p h) (h 13276)

theorem derived90612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2860) ∨ (¬ p 2132) ∨ (p 2563) :=
  ElevenRUP.step90612 (p 2132) (p 2427) (p 2563) (p 2860) (p 4110) (derived73516 p h) (derived55352 p h)

theorem derived90615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (p 2563) ∨ (p 2598) :=
  ElevenRUP.step90615 (p 2132) (p 2563) (p 2598) (p 2860) (p 3055) (p 4110) (derived73516 p h) (derived73350 p h) (derived47352 p h)

theorem derived90617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2132) ∨ (p 2427) ∨ (¬ p 2373) :=
  ElevenRUP.step90617 (p 2132) (p 2373) (p 2427) (p 2870) (p 4235) (derived73536 p h) (derived46493 p h)

theorem derived90619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 2284) ∨ (¬ p 2132) ∨ (¬ p 2860) :=
  ElevenRUP.step90619 (p 2132) (p 2284) (p 2860) (p 2901) (p 3952) (derived73496 p h) (derived43062 p h)

theorem derived90623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 2753) ∨ (p 3564) ∨ (p 3461) ∨ (¬ p 3347) ∨ (¬ p 2132) ∨ (¬ p 4826) ∨ (p 2573) ∨ (¬ p 2870) :=
  ElevenRUP.step90623 (p 2132) (p 2573) (p 2579) (p 2753) (p 2870) (p 3347) (p 3461) (p 3564) (p 4129) (p 4137) (p 4191) (p 4826) (derived73524 p h) (derived73530 p h) (derived73274 p h) (derived71867 p h)

theorem derived90624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2132) ∨ (¬ p 4874) ∨ (p 2192) :=
  ElevenRUP.step90624 (p 2132) (p 2192) (p 2860) (p 4173) (p 4874) (derived73528 p h) (derived71868 p h)

theorem derived90625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2132) ∨ (¬ p 4874) ∨ (p 2891) :=
  ElevenRUP.step90625 (p 2132) (p 2870) (p 2891) (p 3486) (p 4874) (derived73398 p h) (derived71869 p h)

theorem derived90626 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4793) ∨ (p 3399) ∨ (¬ p 2132) ∨ (¬ p 3589) ∨ (p 2839) :=
  ElevenRUP.step90626 (p 2132) (p 2839) (p 3399) (p 3583) (p 3589) (p 4366) (p 4793) (derived73570 p h) (derived73424 p h) (derived41213 p h)

theorem derived90627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2797) ∨ (¬ p 2749) ∨ (¬ p 2132) ∨ (p 2839) :=
  ElevenRUP.step90627 (p 2132) (p 2641) (p 2749) (p 2797) (p 2839) (p 3583) (p 4195) (derived73532 p h) (derived73424 p h) (derived45227 p h)

theorem derived90632 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (p 2737) ∨ (¬ p 3361) ∨ (¬ p 2132) ∨ (¬ p 2891) ∨ (¬ p 4418) ∨ (p 3256) ∨ (¬ p 3246) ∨ (¬ p 3950) :=
  ElevenRUP.step90632 (p 2132) (p 2737) (p 2743) (p 2891) (p 3166) (p 3172) (p 3246) (p 3256) (p 3361) (p 3950) (p 4118) (p 4418) (derived73356 p h) (derived73298 p h) (derived73520 p h) (derived71871 p h)

theorem derived90633 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 3016) ∨ (p 2850) ∨ (¬ p 3698) ∨ (¬ p 2132) ∨ (¬ p 3363) ∨ (p 2839) ∨ (p 3201) ∨ (¬ p 3362) :=
  ElevenRUP.step90633 (p 2132) (p 2440) (p 2542) (p 2839) (p 2850) (p 3016) (p 3201) (p 3362) (p 3363) (p 3574) (p 3583) (p 3684) (p 3698) (p 3876) (derived73270 p h) (derived73422 p h) (derived73442 p h) (derived73424 p h) (derived73486 p h) (derived66701 p h)

theorem derived90634 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 3379) ∨ (¬ p 4376) ∨ (¬ p 3589) ∨ (¬ p 2132) :=
  ElevenRUP.step90634 (p 2132) (p 2839) (p 3379) (p 3452) (p 3583) (p 3589) (p 4376) (derived73424 p h) (derived73394 p h) (derived49038 p h)

theorem derived90635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4337) ∨ (¬ p 3745) ∨ (¬ p 2132) ∨ (¬ p 2619) ∨ (p 2774) ∨ (¬ p 4509) :=
  ElevenRUP.step90635 (p 2132) (p 2619) (p 2774) (p 2780) (p 3745) (p 4337) (p 4509) (derived73308 p h) (derived53804 p h)

theorem derived90637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2274) ∨ (p 2598) ∨ (¬ p 4418) ∨ (¬ p 2192) :=
  ElevenRUP.step90637 (p 2132) (p 2192) (p 2274) (p 2598) (p 3055) (p 4418) (derived73350 p h) (derived58969 p h)

theorem derived90638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 4620) ∨ (¬ p 2132) ∨ (p 2737) ∨ (¬ p 4418) ∨ (p 2331) ∨ (p 3323) ∨ (¬ p 3361) ∨ (¬ p 2192) :=
  ElevenRUP.step90638 (p 2132) (p 2192) (p 2274) (p 2331) (p 2737) (p 2743) (p 2963) (p 3323) (p 3361) (p 4037) (p 4418) (p 4620) (derived73298 p h) (derived73338 p h) (derived73508 p h) (derived71872 p h)

theorem derived90639 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 2274) ∨ (¬ p 2192) ∨ (¬ p 3361) ∨ (¬ p 2132) ∨ (p 2331) ∨ (¬ p 4418) ∨ (p 2668) :=
  ElevenRUP.step90639 (p 2132) (p 2192) (p 2274) (p 2331) (p 2668) (p 2737) (p 2743) (p 2963) (p 3324) (p 3361) (p 4418) (derived73298 p h) (derived73338 p h) (derived73386 p h) (derived71873 p h)

theorem derived90642 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2427) ∨ (¬ p 2132) ∨ (¬ p 2563) :=
  ElevenRUP.step90642 (p 2132) (p 2427) (p 2563) (p 2870) (p 4235) (derived73536 p h) (derived52015 p h)

theorem derived90645 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 3115) ∨ (¬ p 2284) ∨ (¬ p 2132) :=
  ElevenRUP.step90645 (p 2132) (p 2284) (p 3105) (p 3115) (p 4208) (derived73534 p h) (derived45704 p h)

theorem derived90648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 4473) ∨ (¬ p 2177) ∨ (¬ p 2254) ∨ (p 2807) ∨ (¬ p 2132) ∨ (p 2264) ∨ (¬ p 3589) ∨ (p 2839) :=
  ElevenRUP.step90648 (p 2132) (p 2177) (p 2254) (p 2264) (p 2707) (p 2807) (p 2839) (p 3414) (p 3553) (p 3583) (p 3589) (p 4473) (derived73392 p h) (derived73410 p h) (derived73424 p h) (derived57598 p h)

theorem derived90652 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (¬ p 2254) ∨ (p 2459) ∨ (¬ p 3105) ∨ (p 2264) ∨ (¬ p 3589) ∨ (¬ p 2563) ∨ (¬ p 2132) ∨ (p 2807) :=
  ElevenRUP.step90652 (p 2132) (p 2254) (p 2264) (p 2459) (p 2563) (p 2807) (p 2982) (p 3105) (p 3414) (p 3553) (p 3589) (p 4348) (p 4948) (derived73846 p h) (derived73562 p h) (derived73410 p h) (derived73392 p h) (derived58201 p h)

theorem derived90653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 4621) ∨ (¬ p 5197) ∨ (¬ p 2860) ∨ (¬ p 2132) ∨ (¬ p 4729) ∨ (p 2417) ∨ (p 2341) ∨ (¬ p 3125) :=
  ElevenRUP.step90653 (p 2132) (p 2341) (p 2417) (p 2860) (p 2911) (p 3125) (p 3551) (p 4278) (p 4621) (p 4729) (p 5197) (derived73546 p h) (derived73408 p h) (derived50772 p h)

theorem derived90655 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2870) ∨ (p 2437) ∨ (p 2651) ∨ (¬ p 2881) ∨ (¬ p 4789) ∨ (¬ p 2132) ∨ (¬ p 4666) :=
  ElevenRUP.step90655 (p 2132) (p 2417) (p 2437) (p 2651) (p 2657) (p 2870) (p 2881) (p 3742) (p 4278) (p 4666) (p 4789) (derived73546 p h) (derived73452 p h) (derived73288 p h) (derived41668 p h)

theorem derived90656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (p 2417) ∨ (¬ p 4789) ∨ (¬ p 2619) ∨ (¬ p 4669) ∨ (p 2651) ∨ (p 2437) ∨ (¬ p 2132) :=
  ElevenRUP.step90656 (p 2132) (p 2417) (p 2437) (p 2619) (p 2651) (p 2657) (p 3146) (p 3742) (p 4278) (p 4669) (p 4789) (derived73546 p h) (derived73288 p h) (derived73452 p h) (derived55441 p h)

theorem derived90659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2911) ∨ (¬ p 2927) ∨ (p 3399) ∨ (¬ p 3379) ∨ (¬ p 2753) ∨ (¬ p 4133) ∨ (¬ p 2187) ∨ (¬ p 2860) :=
  ElevenRUP.step90659 (p 2132) (p 2187) (p 2753) (p 2860) (p 2911) (p 2927) (p 3379) (p 3399) (p 3644) (p 4133) (p 4366) (derived73434 p h) (derived73570 p h) (derived71875 p h)

theorem derived90660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3093) ∨ (¬ p 3246) ∨ (¬ p 2753) ∨ (¬ p 4625) ∨ (p 3319) ∨ (¬ p 2132) ∨ (¬ p 2750) ∨ (¬ p 2870) :=
  ElevenRUP.step90660 (p 2132) (p 2241) (p 2750) (p 2753) (p 2870) (p 3093) (p 3246) (p 3319) (p 3591) (p 4026) (p 4625) (derived73432 p h) (derived73504 p h) (derived55772 p h)

theorem derived90663 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3093) ∨ (¬ p 2132) ∨ (p 2363) ∨ (¬ p 3950) ∨ (¬ p 3923) ∨ (¬ p 2870) ∨ (¬ p 4733) :=
  ElevenRUP.step90663 (p 2132) (p 2363) (p 2870) (p 3093) (p 3246) (p 3591) (p 3923) (p 3950) (p 4347) (p 4733) (derived73432 p h) (derived73560 p h) (derived50721 p h)

theorem derived90664 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2528) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 4789) ∨ (p 2651) ∨ (¬ p 3950) ∨ (¬ p 3246) :=
  ElevenRUP.step90664 (p 2132) (p 2528) (p 2534) (p 2651) (p 2657) (p 2870) (p 3083) (p 3246) (p 3950) (p 4256) (p 4789) (derived73542 p h) (derived73268 p h) (derived73288 p h) (derived55339 p h)

theorem derived90665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2363) ∨ (p 2352) ∨ (¬ p 4729) ∨ (¬ p 3950) ∨ (¬ p 2132) ∨ (p 2573) ∨ (¬ p 2870) :=
  ElevenRUP.step90665 (p 2132) (p 2352) (p 2363) (p 2573) (p 2579) (p 2870) (p 3246) (p 3950) (p 3956) (p 4347) (p 4729) (derived73560 p h) (derived73500 p h) (derived73274 p h) (derived62892 p h)

theorem derived90666 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (p 3256) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 4789) ∨ (¬ p 2132) ∨ (¬ p 2528) ∨ (¬ p 4438) :=
  ElevenRUP.step90666 (p 2132) (p 2528) (p 2870) (p 2881) (p 3166) (p 3172) (p 3256) (p 4118) (p 4438) (p 4789) (derived73356 p h) (derived73520 p h) (derived42259 p h)

theorem derived90669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3950) ∨ (p 2528) ∨ (¬ p 2252) ∨ (¬ p 2870) ∨ (¬ p 2753) ∨ (¬ p 3246) ∨ (p 3083) ∨ (¬ p 2132) ∨ (p 2651) ∨ (¬ p 2750) :=
  ElevenRUP.step90669 (p 2132) (p 2252) (p 2528) (p 2534) (p 2651) (p 2657) (p 2750) (p 2753) (p 2870) (p 3083) (p 3246) (p 3950) (p 4256) (derived73268 p h) (derived73542 p h) (derived73288 p h) (derived64513 p h)

theorem derived90670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2363) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3950) ∨ (p 2331) ∨ (p 2668) ∨ (¬ p 2245) ∨ (¬ p 4733) :=
  ElevenRUP.step90670 (p 2132) (p 2245) (p 2331) (p 2363) (p 2668) (p 2870) (p 2963) (p 3246) (p 3324) (p 3950) (p 4347) (p 4733) (derived73560 p h) (derived73338 p h) (derived73386 p h) (derived56657 p h)

theorem derived90671 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 2363) ∨ (p 3449) ∨ (¬ p 4993) ∨ (¬ p 2753) ∨ (¬ p 4870) ∨ (¬ p 2619) ∨ (¬ p 3093) ∨ (¬ p 5122) ∨ (¬ p 2132) :=
  ElevenRUP.step90671 (p 2132) (p 2363) (p 2619) (p 2753) (p 3093) (p 3449) (p 3860) (p 3969) (p 4347) (p 4870) (p 4993) (p 5122) (derived73560 p h) (derived73482 p h) (derived62894 p h)

theorem derived90673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 4418) ∨ (¬ p 2891) ∨ (¬ p 2881) ∨ (p 2177) :=
  ElevenRUP.step90673 (p 2132) (p 2177) (p 2299) (p 2881) (p 2891) (p 4418) (derived73234 p h) (derived45713 p h)

theorem derived90674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3146) ∨ (p 2459) ∨ (¬ p 2132) :=
  ElevenRUP.step90674 (p 2132) (p 2459) (p 2619) (p 3146) (p 4348) (derived73562 p h) (derived44673 p h)

theorem derived90681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4030) ∨ (¬ p 3695) ∨ (¬ p 4715) ∨ (¬ p 2132) ∨ (p 2493) ∨ (p 2598) :=
  ElevenRUP.step90681 (p 2132) (p 2493) (p 2499) (p 2598) (p 3055) (p 3695) (p 4030) (p 4715) (derived73260 p h) (derived73350 p h) (derived51486 p h)

theorem derived90682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2839) ∨ (¬ p 4473) ∨ (¬ p 2254) ∨ (p 2651) ∨ (¬ p 2132) ∨ (p 3016) ∨ (p 2553) ∨ (¬ p 3589) :=
  ElevenRUP.step90682 (p 2132) (p 2254) (p 2553) (p 2588) (p 2651) (p 2657) (p 2707) (p 2839) (p 3016) (p 3574) (p 3583) (p 3589) (p 4473) (derived73424 p h) (derived73288 p h) (derived73422 p h) (derived73282 p h) (derived56111 p h)

theorem derived90683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2352) ∨ (¬ p 4625) ∨ (¬ p 2753) ∨ (p 3564) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 3923) ∨ (¬ p 4870) :=
  ElevenRUP.step90683 (p 2132) (p 2352) (p 2753) (p 2870) (p 3246) (p 3564) (p 3923) (p 4137) (p 4625) (p 4870) (derived73524 p h) (derived49148 p h)

theorem derived90688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5123) ∨ (¬ p 2132) ∨ (¬ p 3347) ∨ (¬ p 3680) ∨ (¬ p 3105) ∨ (p 2352) ∨ (p 2573) ∨ (¬ p 2753) :=
  ElevenRUP.step90688 (p 2132) (p 2352) (p 2573) (p 2579) (p 2753) (p 3105) (p 3347) (p 3680) (p 3956) (p 5123) (p 5580) (derived73500 p h) (derived73274 p h) (derived71880 p h)

theorem derived90689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2396) ∨ (¬ p 2870) ∨ (¬ p 2132) :=
  ElevenRUP.step90689 (p 2132) (p 2396) (p 2870) (p 3246) (p 4107) (derived73514 p h) (derived46802 p h)

theorem derived90691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5558) ∨ (p 3399) ∨ (p 3527) ∨ (¬ p 4733) ∨ (¬ p 5123) ∨ (¬ p 3680) ∨ (¬ p 2132) ∨ (¬ p 3105) :=
  ElevenRUP.step90691 (p 2132) (p 3105) (p 3399) (p 3527) (p 3548) (p 3680) (p 4366) (p 4733) (p 5123) (p 5558) (derived73570 p h) (derived73404 p h) (derived62679 p h)

theorem derived90692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 4186) ∨ (¬ p 2860) ∨ (¬ p 4729) ∨ (p 2528) ∨ (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 4133) ∨ (p 3389) :=
  ElevenRUP.step90692 (p 2132) (p 2187) (p 2459) (p 2528) (p 2534) (p 2860) (p 3389) (p 3540) (p 4133) (p 4186) (p 4729) (derived73268 p h) (derived73402 p h) (derived58086 p h)

theorem derived90694 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2132) ∨ (p 2274) ∨ (p 2839) ∨ (¬ p 4428) :=
  ElevenRUP.step90694 (p 2132) (p 2274) (p 2774) (p 2780) (p 2839) (p 3097) (p 3583) (p 4428) (derived73308 p h) (derived73352 p h) (derived73424 p h) (derived50293 p h)

theorem derived90695 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2132) ∨ (p 2839) ∨ (¬ p 4428) ∨ (p 2187) :=
  ElevenRUP.step90695 (p 2132) (p 2187) (p 2774) (p 2780) (p 2839) (p 3583) (p 3989) (p 4428) (derived73308 p h) (derived73424 p h) (derived73502 p h) (derived55933 p h)

theorem derived90696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 2829) ∨ (¬ p 2132) ∨ (¬ p 3985) :=
  ElevenRUP.step90696 (p 2132) (p 2753) (p 2829) (p 3688) (p 3985) (derived73444 p h) (h 5916)

theorem derived90698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4744) ∨ (p 2098) ∨ (¬ p 2132) :=
  ElevenRUP.step90698 (p 2098) (p 2104) (p 2132) (p 4744) (derived73204 p h) (h 19765)

theorem derived90700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3246) ∨ (¬ p 4344) ∨ (¬ p 3589) ∨ (¬ p 2132) ∨ (p 2839) :=
  ElevenRUP.step90700 (p 2132) (p 2707) (p 2839) (p 3246) (p 3583) (p 3589) (p 4344) (derived73424 p h) (derived43618 p h)

theorem derived90703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2696) ∨ (¬ p 2132) ∨ (p 2427) :=
  ElevenRUP.step90703 (p 2132) (p 2427) (p 2696) (p 2870) (p 3365) (p 4235) (derived73390 p h) (derived73536 p h) (derived52712 p h)

theorem derived90704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2427) ∨ (p 3367) ∨ (¬ p 2753) ∨ (¬ p 2132) :=
  ElevenRUP.step90704 (p 2132) (p 2427) (p 2753) (p 2870) (p 3367) (p 3585) (p 4235) (derived73536 p h) (derived73428 p h) (derived46727 p h)

theorem derived90706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2696) ∨ (p 2901) ∨ (¬ p 2132) :=
  ElevenRUP.step90706 (p 2132) (p 2696) (p 2870) (p 2901) (p 3365) (p 4320) (derived73390 p h) (derived73552 p h) (derived43785 p h)

theorem derived90707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 4625) ∨ (¬ p 4022) ∨ (¬ p 2132) ∨ (¬ p 2655) ∨ (¬ p 3016) ∨ (¬ p 2870) ∨ (¬ p 2750) ∨ (¬ p 2252) ∨ (p 2573) ∨ (p 3343) ∨ (¬ p 3246) :=
  ElevenRUP.step90707 (p 2132) (p 2252) (p 2573) (p 2579) (p 2655) (p 2750) (p 2753) (p 2870) (p 3016) (p 3246) (p 3343) (p 3359) (p 4022) (p 4625) (derived73274 p h) (derived73388 p h) (derived64549 p h)

theorem derived90708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2696) ∨ (¬ p 2132) ∨ (¬ p 2881) :=
  ElevenRUP.step90708 (p 2132) (p 2696) (p 2870) (p 2881) (p 3365) (derived73390 p h) (derived47432 p h)

theorem derived90709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3905) ∨ (p 3389) ∨ (¬ p 4647) ∨ (¬ p 2132) ∨ (¬ p 2870) :=
  ElevenRUP.step90709 (p 2132) (p 2870) (p 3389) (p 3540) (p 3905) (p 4647) (derived73402 p h) (derived62176 p h)

theorem derived90710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2839) ∨ (¬ p 2132) ∨ (¬ p 2829) ∨ (¬ p 4185) :=
  ElevenRUP.step90710 (p 2132) (p 2829) (p 2839) (p 3125) (p 3583) (p 4185) (derived73424 p h) (derived57966 p h)

theorem derived90711 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 3422) ∨ (¬ p 2132) ∨ (¬ p 3541) ∨ (¬ p 2493) :=
  ElevenRUP.step90711 (p 2132) (p 2493) (p 2839) (p 3422) (p 3541) (p 3583) (p 3584) (derived73424 p h) (derived73426 p h) (derived45836 p h)

theorem derived90712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2839) ∨ (¬ p 2717) ∨ (¬ p 3589) ∨ (¬ p 2132) :=
  ElevenRUP.step90712 (p 2132) (p 2707) (p 2717) (p 2839) (p 3583) (p 3589) (derived73424 p h) (derived45841 p h)

theorem derived90714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (p 2839) ∨ (¬ p 2132) ∨ (¬ p 2737) :=
  ElevenRUP.step90714 (p 2132) (p 2737) (p 2797) (p 2839) (p 3583) (derived73424 p h) (derived45228 p h)

theorem derived90715 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3820) ∨ (p 2341) ∨ (¬ p 2881) ∨ (¬ p 2132) ∨ (p 2839) :=
  ElevenRUP.step90715 (p 2132) (p 2341) (p 2839) (p 2881) (p 3551) (p 3583) (p 3820) (derived73408 p h) (derived73424 p h) (derived43856 p h)

theorem derived90717 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2753) ∨ (¬ p 2132) :=
  ElevenRUP.step90717 (p 2132) (p 2753) (p 2839) (p 3583) (derived73424 p h) (h 5391)

theorem derived90718 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3096) ∨ (¬ p 4558) ∨ (¬ p 4342) :=
  ElevenRUP.step90718 (p 2132) (p 2774) (p 2780) (p 2870) (p 3096) (p 4342) (p 4558) (derived73308 p h) (derived50609 p h)

theorem derived90719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3054) ∨ (¬ p 2132) ∨ (p 2598) :=
  ElevenRUP.step90719 (p 2132) (p 2598) (p 3054) (p 3055) (derived73350 p h) (h 4235)

theorem derived90721 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2132) ∨ (¬ p 3695) ∨ (p 2598) ∨ (¬ p 4644) :=
  ElevenRUP.step90721 (p 2132) (p 2598) (p 3055) (p 3201) (p 3695) (p 3876) (p 4644) (derived73486 p h) (derived73350 p h) (derived51333 p h)

theorem derived90722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 3641) ∨ (p 2598) ∨ (¬ p 3695) ∨ (¬ p 4608) :=
  ElevenRUP.step90722 (p 2132) (p 2598) (p 3055) (p 3641) (p 3695) (p 3874) (p 4608) (derived73484 p h) (derived73350 p h) (derived48365 p h)

theorem derived90723 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3950) ∨ (p 3641) ∨ (¬ p 2870) ∨ (¬ p 2132) ∨ (¬ p 3246) ∨ (p 3367) :=
  ElevenRUP.step90723 (p 2132) (p 2528) (p 2534) (p 2870) (p 3246) (p 3367) (p 3585) (p 3641) (p 3874) (p 3950) (derived73268 p h) (derived73484 p h) (derived73428 p h) (derived71881 p h)

theorem derived90726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2427) ∨ (¬ p 2245) ∨ (¬ p 4705) ∨ (¬ p 4733) ∨ (p 2996) ∨ (p 2992) ∨ (p 2807) ∨ (¬ p 2132) :=
  ElevenRUP.step90726 (p 2132) (p 2245) (p 2427) (p 2807) (p 2870) (p 2992) (p 2996) (p 3027) (p 3414) (p 3662) (p 4235) (p 4705) (p 4733) (derived73536 p h) (derived73340 p h) (derived73440 p h) (derived73392 p h) (derived50920 p h)

theorem derived90728 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3146) ∨ (p 2737) ∨ (¬ p 2132) ∨ (¬ p 2619) :=
  ElevenRUP.step90728 (p 2132) (p 2619) (p 2737) (p 2743) (p 2753) (p 3146) (derived73298 p h) (derived54457 p h)

theorem derived90731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 2417) ∨ (p 2651) ∨ (p 2437) ∨ (¬ p 2860) ∨ (¬ p 2132) ∨ (¬ p 3125) ∨ (¬ p 2750) ∨ (¬ p 4621) ∨ (¬ p 2252) :=
  ElevenRUP.step90731 (p 2132) (p 2252) (p 2417) (p 2437) (p 2651) (p 2657) (p 2750) (p 2753) (p 2860) (p 3125) (p 3742) (p 4278) (p 4621) (derived73546 p h) (derived73288 p h) (derived73452 p h) (derived63167 p h)

theorem derived90732 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 3343) ∨ (¬ p 2750) ∨ (¬ p 2252) ∨ (¬ p 4826) ∨ (¬ p 4129) ∨ (¬ p 2870) ∨ (p 2651) ∨ (¬ p 2753) ∨ (¬ p 2132) :=
  ElevenRUP.step90732 (p 2132) (p 2252) (p 2651) (p 2657) (p 2750) (p 2753) (p 2870) (p 3276) (p 3343) (p 3359) (p 4129) (p 4425) (p 4826) (derived73578 p h) (derived73388 p h) (derived73288 p h) (derived64511 p h)

theorem derived90735 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (p 3189) ∨ (¬ p 2881) ∨ (¬ p 4733) ∨ (¬ p 2727) ∨ (¬ p 4041) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (p 2651) :=
  ElevenRUP.step90735 (p 2132) (p 2245) (p 2651) (p 2657) (p 2727) (p 2870) (p 2881) (p 3189) (p 4041) (p 4360) (p 4733) (derived73566 p h) (derived73288 p h) (derived50011 p h)

theorem derived90736 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 3367) ∨ (¬ p 2132) ∨ (p 2696) :=
  ElevenRUP.step90736 (p 2132) (p 2696) (p 2839) (p 3365) (p 3367) (p 3583) (derived73424 p h) (derived73390 p h) (derived45344 p h)

theorem derived90737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 3189) ∨ (¬ p 2881) ∨ (¬ p 2870) ∨ (¬ p 4769) ∨ (¬ p 4733) ∨ (¬ p 4503) ∨ (¬ p 2245) ∨ (¬ p 2132) ∨ (p 2331) :=
  ElevenRUP.step90737 (p 2132) (p 2245) (p 2331) (p 2641) (p 2870) (p 2881) (p 2963) (p 3189) (p 4360) (p 4503) (p 4733) (p 4769) (derived73566 p h) (derived73338 p h) (derived62501 p h)

theorem derived90740 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 4503) ∨ (¬ p 4733) ∨ (p 2668) ∨ (p 2241) ∨ (¬ p 2132) ∨ (p 2641) :=
  ElevenRUP.step90740 (p 2132) (p 2241) (p 2247) (p 2641) (p 2668) (p 2870) (p 2881) (p 3324) (p 4154) (p 4503) (p 4733) (derived73386 p h) (derived73226 p h) (derived73526 p h) (derived64716 p h)

theorem derived90755 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 4733) ∨ (¬ p 2870) ∨ (¬ p 2132) ∨ (p 2528) ∨ (¬ p 3950) ∨ (¬ p 3246) ∨ (¬ p 2509) :=
  ElevenRUP.step90755 (p 2132) (p 2509) (p 2528) (p 2534) (p 2870) (p 3246) (p 3379) (p 3452) (p 3950) (p 4733) (derived73394 p h) (derived73268 p h) (derived51335 p h)

theorem derived90764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4733) ∨ (¬ p 3125) ∨ (p 2528) ∨ (¬ p 4330) ∨ (¬ p 2509) ∨ (p 3379) ∨ (¬ p 2860) ∨ (¬ p 2132) :=
  ElevenRUP.step90764 (p 2132) (p 2509) (p 2528) (p 2534) (p 2860) (p 3125) (p 3379) (p 3452) (p 4330) (p 4733) (derived73268 p h) (derived73394 p h) (derived57567 p h)

theorem derived90765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (p 3276) ∨ (¬ p 4129) ∨ (¬ p 4826) ∨ (¬ p 2870) ∨ (p 3379) ∨ (¬ p 4733) ∨ (¬ p 2132) :=
  ElevenRUP.step90765 (p 2132) (p 2870) (p 3193) (p 3276) (p 3379) (p 3452) (p 4129) (p 4425) (p 4733) (p 4826) (derived73578 p h) (derived73394 p h) (derived52626 p h)

theorem derived90766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2132) ∨ (¬ p 5214) ∨ (p 2598) ∨ (p 2406) :=
  ElevenRUP.step90766 (p 2132) (p 2406) (p 2598) (p 3055) (p 3238) (p 3695) (p 5214) (derived73350 p h) (derived73374 p h) (derived41137 p h)

theorem derived90770 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2241) ∨ (¬ p 4405) ∨ (¬ p 2187) ∨ (¬ p 2750) ∨ (¬ p 2860) ∨ (¬ p 2132) ∨ (p 3309) ∨ (¬ p 2753) :=
  ElevenRUP.step90770 (p 2132) (p 2187) (p 2241) (p 2750) (p 2753) (p 2860) (p 3093) (p 3309) (p 3549) (p 3591) (p 4405) (derived73432 p h) (derived73406 p h) (derived56541 p h)

theorem derived90771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 3449) ∨ (¬ p 4733) ∨ (¬ p 4133) ∨ (¬ p 2459) ∨ (p 3073) ∨ (¬ p 2860) ∨ (¬ p 2187) :=
  ElevenRUP.step90771 (p 2132) (p 2187) (p 2459) (p 2860) (p 3073) (p 3449) (p 3860) (p 4133) (p 4261) (p 4733) (derived73482 p h) (derived73544 p h) (derived51485 p h)

theorem derived90773 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 4733) ∨ (¬ p 2870) ∨ (¬ p 2132) ∨ (p 3379) ∨ (¬ p 3453) ∨ (¬ p 4438) ∨ (¬ p 2528) ∨ (¬ p 2881) :=
  ElevenRUP.step90773 (p 2132) (p 2528) (p 2870) (p 2881) (p 3073) (p 3379) (p 3452) (p 3453) (p 4261) (p 4438) (p 4733) (derived73544 p h) (derived73394 p h) (derived55056 p h)

theorem derived90775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (¬ p 4140) ∨ (¬ p 2177) ∨ (p 2241) ∨ (¬ p 4733) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (p 2449) ∨ (¬ p 4666) :=
  ElevenRUP.step90775 (p 2132) (p 2177) (p 2241) (p 2247) (p 2449) (p 2870) (p 2996) (p 3947) (p 4140) (p 4666) (p 4733) (derived73226 p h) (derived73494 p h) (derived61981 p h)

theorem derived90776 (p : Nat → Prop) (h : Inputs p) :
    (p 2663) ∨ (p 2737) ∨ (¬ p 3361) ∨ (¬ p 2132) ∨ (p 2264) ∨ (¬ p 2891) ∨ (¬ p 4418) ∨ (¬ p 3246) ∨ (p 3389) ∨ (¬ p 3579) ∨ (¬ p 4668) :=
  ElevenRUP.step90776 (p 2132) (p 2264) (p 2663) (p 2737) (p 2743) (p 2891) (p 3246) (p 3361) (p 3389) (p 3540) (p 3553) (p 3579) (p 4418) (p 4668) (derived73298 p h) (derived73410 p h) (derived73402 p h) (derived71885 p h)

theorem derived90779 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3256) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (p 2241) ∨ (¬ p 4733) ∨ (¬ p 3950) ∨ (¬ p 2132) :=
  ElevenRUP.step90779 (p 2132) (p 2241) (p 2247) (p 2870) (p 3189) (p 3246) (p 3256) (p 3950) (p 4118) (p 4360) (p 4733) (derived73566 p h) (derived73520 p h) (derived73226 p h) (derived50461 p h)

theorem derived90781 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 2241) ∨ (¬ p 3125) ∨ (¬ p 4330) ∨ (¬ p 2132) ∨ (p 3189) ∨ (¬ p 4733) ∨ (¬ p 2860) :=
  ElevenRUP.step90781 (p 2132) (p 2241) (p 2247) (p 2860) (p 3125) (p 3189) (p 3256) (p 4118) (p 4330) (p 4360) (p 4733) (derived73520 p h) (derived73226 p h) (derived73566 p h) (derived49254 p h)

theorem derived90785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4963) ∨ (p 2098) ∨ (¬ p 2860) ∨ (¬ p 2132) ∨ (¬ p 4312) :=
  ElevenRUP.step90785 (p 2098) (p 2104) (p 2132) (p 2860) (p 4312) (p 4963) (derived73204 p h) (derived69522 p h)

theorem derived90786 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (p 3156) ∨ (p 2696) :=
  ElevenRUP.step90786 (p 2132) (p 2619) (p 2696) (p 3156) (p 3365) (p 3497) (derived73400 p h) (derived73390 p h) (derived60974 p h)

theorem derived90789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2839) ∨ (¬ p 3589) ∨ (¬ p 2274) ∨ (¬ p 2132) ∨ (¬ p 4185) :=
  ElevenRUP.step90789 (p 2132) (p 2274) (p 2829) (p 2839) (p 3583) (p 3589) (p 4185) (derived73424 p h) (derived42800 p h)

theorem derived90791 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3680) ∨ (¬ p 2132) ∨ (¬ p 3105) :=
  ElevenRUP.step90791 (p 2132) (p 3105) (p 3266) (p 3680) (p 4444) (derived73580 p h) (derived65096 p h)

theorem derived90792 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 4418) ∨ (¬ p 3680) ∨ (¬ p 2166) ∨ (¬ p 2132) ∨ (¬ p 2533) :=
  ElevenRUP.step90792 (p 2132) (p 2166) (p 2533) (p 3266) (p 3680) (p 4418) (p 4444) (derived73580 p h) (derived63391 p h)

theorem derived90793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 2753) ∨ (p 3256) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (p 3266) ∨ (¬ p 2870) ∨ (¬ p 2132) ∨ (¬ p 4826) ∨ (p 3166) :=
  ElevenRUP.step90793 (p 2132) (p 2252) (p 2750) (p 2753) (p 2870) (p 3166) (p 3172) (p 3256) (p 3266) (p 4118) (p 4129) (p 4444) (p 4826) (derived73520 p h) (derived73580 p h) (derived73356 p h) (derived64528 p h)

theorem derived90797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2839) ∨ (¬ p 2132) ∨ (¬ p 2122) ∨ (¬ p 3589) :=
  ElevenRUP.step90797 (p 2122) (p 2132) (p 2829) (p 2839) (p 3583) (p 3589) (derived73424 p h) (derived45834 p h)

theorem derived90798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3820) ∨ (¬ p 3038) ∨ (¬ p 5052) ∨ (¬ p 2742) ∨ (p 2341) ∨ (¬ p 2132) :=
  ElevenRUP.step90798 (p 2132) (p 2341) (p 2742) (p 3038) (p 3527) (p 3551) (p 3820) (p 5052) (derived73408 p h) (derived56991 p h)

theorem derived90800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4869) ∨ (p 2839) ∨ (p 2122) ∨ (¬ p 2132) ∨ (¬ p 3589) :=
  ElevenRUP.step90800 (p 2122) (p 2132) (p 2839) (p 3309) (p 3583) (p 3589) (p 3822) (p 4869) (derived73424 p h) (derived73472 p h) (derived45843 p h)

theorem derived90801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2742) ∨ (¬ p 5052) ∨ (¬ p 4759) ∨ (¬ p 2778) ∨ (p 2307) ∨ (¬ p 2132) :=
  ElevenRUP.step90801 (p 2132) (p 2307) (p 2313) (p 2742) (p 2778) (p 3309) (p 4759) (p 5052) (derived73238 p h) (derived51296 p h)

theorem derived90802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2132) ∨ (p 2166) ∨ (¬ p 4874) :=
  ElevenRUP.step90802 (p 2132) (p 2166) (p 2191) (p 2619) (p 4874) (derived73222 p h) (derived71887 p h)

theorem derived90804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2860) ∨ (¬ p 2187) ∨ (p 3367) :=
  ElevenRUP.step90804 (p 2132) (p 2187) (p 2753) (p 2860) (p 3367) (p 3585) (derived73428 p h) (derived45779 p h)

theorem derived90806 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 5051) ∨ (¬ p 2166) ∨ (¬ p 2132) ∨ (¬ p 4740) ∨ (¬ p 4960) :=
  ElevenRUP.step90806 (p 2098) (p 2104) (p 2132) (p 2166) (p 4740) (p 4960) (p 5051) (derived73204 p h) (derived48086 p h)

theorem derived90807 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3146) ∨ (p 2839) ∨ (¬ p 4740) ∨ (¬ p 2132) :=
  ElevenRUP.step90807 (p 2098) (p 2104) (p 2132) (p 2839) (p 3146) (p 3583) (p 3692) (p 4740) (derived73204 p h) (derived73448 p h) (derived73424 p h) (derived43163 p h)

theorem derived90808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (p 2307) ∨ (¬ p 5052) ∨ (¬ p 2122) ∨ (¬ p 2132) ∨ (¬ p 4426) :=
  ElevenRUP.step90808 (p 2122) (p 2132) (p 2307) (p 2313) (p 2778) (p 4426) (p 5052) (derived73238 p h) (derived59057 p h)

theorem derived90810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 2132) ∨ (¬ p 3950) ∨ (¬ p 3985) ∨ (p 3449) ∨ (p 3073) ∨ (¬ p 3379) ∨ (¬ p 2753) :=
  ElevenRUP.step90810 (p 2122) (p 2132) (p 2396) (p 2753) (p 3073) (p 3379) (p 3449) (p 3860) (p 3950) (p 3985) (p 4261) (derived73482 p h) (derived73544 p h) (derived71889 p h)

theorem derived90812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4317) ∨ (¬ p 3073) ∨ (p 3425) ∨ (¬ p 3918) ∨ (¬ p 3985) ∨ (¬ p 2102) ∨ (¬ p 4782) ∨ (p 2088) ∨ (¬ p 4313) :=
  ElevenRUP.step90812 (p 2088) (p 2102) (p 3073) (p 3425) (p 3471) (p 3857) (p 3918) (p 3985) (p 4313) (p 4317) (p 4782) (derived73396 p h) (derived73480 p h) (derived55924 p h)

theorem derived90822 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 2383) ∨ (¬ p 4621) ∨ (p 2668) ∨ (¬ p 3987) ∨ (¬ p 2246) ∨ (p 3246) ∨ (¬ p 2744) ∨ (p 2230) ∨ (¬ p 3366) ∨ (p 2870) ∨ (¬ p 3695) ∨ (¬ p 3905) :=
  ElevenRUP.step90822 (p 2230) (p 2246) (p 2383) (p 2589) (p 2668) (p 2744) (p 2870) (p 3246) (p 3323) (p 3324) (p 3366) (p 3690) (p 3695) (p 3905) (p 3987) (p 4244) (p 4621) (derived73386 p h) (derived73446 p h) (derived73284 p h) (derived73540 p h) (derived59421 p h)

theorem derived90825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 4156) ∨ (p 2177) ∨ (¬ p 4581) ∨ (p 2307) :=
  ElevenRUP.step90825 (p 2177) (p 2264) (p 2299) (p 2307) (p 2313) (p 4156) (p 4581) (derived73234 p h) (derived73238 p h) (derived49216 p h)

theorem derived90826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4156) ∨ (¬ p 2331) ∨ (p 2807) :=
  ElevenRUP.step90826 (p 2331) (p 2807) (p 2963) (p 3414) (p 4156) (derived73337 p h) (derived73392 p h) (h 6677)

theorem derived90832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4156) ∨ (¬ p 4140) ∨ (¬ p 2264) ∨ (p 2881) ∨ (p 3323) ∨ (¬ p 4620) :=
  ElevenRUP.step90832 (p 2264) (p 2881) (p 3323) (p 3570) (p 4037) (p 4140) (p 4156) (p 4620) (derived73418 p h) (derived73508 p h) (derived41122 p h)

theorem derived90833 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 3931) ∨ (p 2668) ∨ (¬ p 4156) :=
  ElevenRUP.step90833 (p 2668) (p 3324) (p 3931) (p 4156) (p 4260) (derived73386 p h) (derived71890 p h)

theorem derived90836 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2641) ∨ (p 2177) ∨ (¬ p 4156) ∨ (¬ p 2241) :=
  ElevenRUP.step90836 (p 2177) (p 2241) (p 2264) (p 2299) (p 2641) (p 4156) (derived73234 p h) (derived43427 p h)

theorem derived90839 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 4156) ∨ (p 2668) ∨ (p 2396) :=
  ElevenRUP.step90839 (p 2396) (p 2449) (p 2668) (p 3324) (p 4107) (p 4156) (derived73386 p h) (derived73514 p h) (derived71891 p h)

theorem derived90849 (p : Nat → Prop) (h : Inputs p) :
    (p 4275) ∨ (p 2274) :=
  ElevenRUP.step90849 (p 2274) (p 4275) (p 5818) (derived74101 p h) (h 11905)

theorem derived90850 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (p 4647) :=
  ElevenRUP.step90850 (p 2427) (p 4235) (p 4647) (derived73536 p h) (derived42697 p h)

theorem derived90851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2427) ∨ (¬ p 2210) ∨ (¬ p 2563) :=
  ElevenRUP.step90851 (p 2210) (p 2427) (p 2563) (p 2891) (p 4235) (derived73536 p h) (derived45246 p h)

theorem derived90852 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (p 2284) ∨ (¬ p 4275) ∨ (¬ p 2563) ∨ (p 2177) :=
  ElevenRUP.step90852 (p 2177) (p 2284) (p 2299) (p 2427) (p 2563) (p 3952) (p 4235) (p 4275) (derived73536 p h) (derived73496 p h) (derived73234 p h) (derived48545 p h)

theorem derived90853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2427) ∨ (¬ p 2563) ∨ (¬ p 4275) :=
  ElevenRUP.step90853 (p 2295) (p 2427) (p 2563) (p 4235) (p 4275) (p 4560) (derived73536 p h) (derived72955 p h) (derived62626 p h)

theorem derived90854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4399) ∨ (p 2427) ∨ (¬ p 2563) ∨ (p 2470) :=
  ElevenRUP.step90854 (p 2427) (p 2470) (p 2476) (p 2563) (p 3051) (p 4235) (p 4399) (derived73536 p h) (derived73250 p h) (derived50921 p h)

theorem derived90855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2220) ∨ (¬ p 2563) ∨ (p 2427) :=
  ElevenRUP.step90855 (p 2220) (p 2427) (p 2563) (p 3051) (p 4120) (p 4235) (derived73522 p h) (derived73536 p h) (derived69523 p h)

theorem derived90856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2144) ∨ (¬ p 2563) ∨ (p 2598) ∨ (p 2427) :=
  ElevenRUP.step90856 (p 2144) (p 2427) (p 2563) (p 2598) (p 3051) (p 3055) (p 4235) (derived73350 p h) (derived73536 p h) (derived46761 p h)

theorem derived90860 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 3051) ∨ (p 2427) ∨ (¬ p 2563) :=
  ElevenRUP.step90860 (p 2427) (p 2563) (p 3051) (p 3125) (p 4235) (derived73536 p h) (derived46567 p h)

theorem derived90861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3323) ∨ (p 2427) ∨ (¬ p 2563) :=
  ElevenRUP.step90861 (p 2427) (p 2563) (p 3125) (p 3323) (p 4037) (p 4235) (derived73508 p h) (derived73536 p h) (derived55090 p h)

theorem derived90865 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2946) ∨ (¬ p 2563) ∨ (¬ p 2901) :=
  ElevenRUP.step90865 (p 2427) (p 2563) (p 2901) (p 2946) (p 4235) (derived73536 p h) (derived46560 p h)

theorem derived90869 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 3872) ∨ (¬ p 2563) :=
  ElevenRUP.step90869 (p 2427) (p 2563) (p 3872) (p 4235) (derived73536 p h) (h 20497)

theorem derived90871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 3609) ∨ (¬ p 4433) ∨ (¬ p 2363) ∨ (p 2427) ∨ (p 2098) ∨ (¬ p 2139) ∨ (¬ p 2373) :=
  ElevenRUP.step90871 (p 2098) (p 2104) (p 2139) (p 2363) (p 2373) (p 2427) (p 3051) (p 3609) (p 4235) (p 4340) (p 4433) (derived73558 p h) (derived73536 p h) (derived73204 p h) (derived62681 p h)

theorem derived90874 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2563) ∨ (¬ p 3051) ∨ (¬ p 2187) :=
  ElevenRUP.step90874 (p 2187) (p 2427) (p 2563) (p 3051) (p 4235) (derived73536 p h) (derived46760 p h)

theorem derived90876 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2957) ∨ (¬ p 2563) ∨ (p 2992) ∨ (p 2156) :=
  ElevenRUP.step90876 (p 2156) (p 2427) (p 2563) (p 2957) (p 2992) (p 3646) (p 3662) (p 4235) (derived73536 p h) (derived73440 p h) (derived73436 p h) (derived60365 p h)

theorem derived90879 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2427) ∨ (p 2881) ∨ (¬ p 3879) ∨ (¬ p 2651) :=
  ElevenRUP.step90879 (p 2427) (p 2651) (p 2881) (p 2946) (p 2952) (p 3570) (p 3879) (p 4235) (derived73330 p h) (derived73536 p h) (derived73418 p h) (derived60186 p h)

theorem derived90880 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3879) ∨ (¬ p 2651) ∨ (p 2427) ∨ (p 2630) :=
  ElevenRUP.step90880 (p 2427) (p 2630) (p 2651) (p 2810) (p 2946) (p 2952) (p 3879) (p 4235) (derived73330 p h) (derived73536 p h) (derived73316 p h) (derived42669 p h)

theorem derived90883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (p 2427) ∨ (¬ p 4109) ∨ (¬ p 3872) :=
  ElevenRUP.step90883 (p 2156) (p 2427) (p 3872) (p 4109) (p 4235) (derived73536 p h) (h 30491)

theorem derived90885 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2427) ∨ (¬ p 2177) ∨ (p 2406) :=
  ElevenRUP.step90885 (p 2177) (p 2406) (p 2427) (p 2881) (p 3238) (p 3570) (p 4235) (derived73418 p h) (derived73536 p h) (derived73374 p h) (derived43954 p h)

theorem derived90886 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2307) ∨ (¬ p 4275) ∨ (¬ p 2563) ∨ (¬ p 4489) :=
  ElevenRUP.step90886 (p 2307) (p 2427) (p 2563) (p 4235) (p 4275) (p 4489) (derived73536 p h) (derived49388 p h)

theorem derived90893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2427) ∨ (¬ p 2440) ∨ (p 2156) :=
  ElevenRUP.step90893 (p 2156) (p 2427) (p 2440) (p 3051) (p 3646) (p 4235) (derived73536 p h) (derived73436 p h) (derived42962 p h)

theorem derived90894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2284) ∨ (p 2427) ∨ (¬ p 4705) ∨ (p 2156) :=
  ElevenRUP.step90894 (p 2156) (p 2284) (p 2427) (p 3051) (p 3646) (p 4235) (p 4705) (derived73536 p h) (derived73436 p h) (derived58881 p h)

theorem derived90896 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2662) ∨ (¬ p 3904) ∨ (p 2156) ∨ (¬ p 2563) ∨ (p 2630) :=
  ElevenRUP.step90896 (p 2156) (p 2427) (p 2563) (p 2630) (p 2662) (p 2810) (p 3646) (p 3904) (p 4235) (derived73536 p h) (derived73436 p h) (derived73316 p h) (derived46005 p h)

theorem derived90898 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 3146) ∨ (p 2427) ∨ (¬ p 4705) ∨ (¬ p 4119) ∨ (¬ p 4237) :=
  ElevenRUP.step90898 (p 2427) (p 3146) (p 3256) (p 3692) (p 4119) (p 4235) (p 4237) (p 4705) (derived73448 p h) (derived73536 p h) (derived62314 p h)

theorem derived90900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 4905) ∨ (p 2427) ∨ (¬ p 3146) ∨ (p 2459) :=
  ElevenRUP.step90900 (p 2427) (p 2459) (p 2982) (p 3146) (p 4235) (p 4348) (p 4905) (p 5057) (derived73536 p h) (derived73898 p h) (derived73562 p h) (derived67084 p h)

theorem derived90904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 2911) ∨ (¬ p 4705) ∨ (¬ p 2881) :=
  ElevenRUP.step90904 (p 2881) (p 2901) (p 2911) (p 3644) (p 4705) (derived73434 p h) (derived66806 p h)

theorem derived90905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3654) ∨ (¬ p 4705) ∨ (¬ p 4356) ∨ (¬ p 4336) ∨ (p 2563) :=
  ElevenRUP.step90905 (p 2563) (p 3323) (p 3654) (p 3946) (p 4110) (p 4336) (p 4356) (p 4705) (derived73492 p h) (derived73516 p h) (derived42038 p h)

theorem derived90909 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3246) ∨ (¬ p 2901) ∨ (¬ p 4705) ∨ (¬ p 2441) :=
  ElevenRUP.step90909 (p 2417) (p 2441) (p 2901) (p 3246) (p 4278) (p 4705) (derived73546 p h) (derived54204 p h)

theorem derived90910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2352) ∨ (¬ p 2284) ∨ (¬ p 4705) ∨ (¬ p 2590) :=
  ElevenRUP.step90910 (p 2187) (p 2284) (p 2352) (p 2590) (p 3956) (p 4705) (derived73500 p h) (derived62327 p h)

theorem derived90911 (p : Nat → Prop) (h : Inputs p) :
    (p 4337) ∨ (p 2797) :=
  ElevenRUP.step90911 (p 2797) (p 4337) (p 4840) (derived73786 p h) (h 7946)

theorem derived90912 (p : Nat → Prop) (h : Inputs p) :
    (p 4337) ∨ (p 2797) :=
  ElevenRUP.step90912 (p 2797) (p 4337) (p 5917) (derived74229 p h) (h 12485)

theorem derived90915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 5257) :=
  ElevenRUP.step90915 (p 3425) (p 5256) (p 5257) (derived73980 p h) (h 8946)

theorem derived90918 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3564) ∨ (¬ p 2274) ∨ (p 2307) :=
  ElevenRUP.step90918 (p 2274) (p 2307) (p 2313) (p 3564) (p 3654) (p 4137) (derived73524 p h) (derived73238 p h) (derived43356 p h)

theorem derived90921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2307) ∨ (¬ p 4025) :=
  ElevenRUP.step90921 (p 2307) (p 2313) (p 3654) (p 4025) (derived73238 p h) (h 22149)

theorem derived90923 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2307) ∨ (p 2177) ∨ (p 3323) :=
  ElevenRUP.step90923 (p 2177) (p 2299) (p 2307) (p 2313) (p 3323) (p 3654) (p 4037) (derived73238 p h) (derived73234 p h) (derived73508 p h) (derived44366 p h)

theorem derived90926 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 2187) ∨ (p 2383) ∨ (p 3564) :=
  ElevenRUP.step90926 (p 2187) (p 2383) (p 2387) (p 3564) (p 3654) (p 4137) (derived73246 p h) (derived73524 p h) (derived43152 p h)

theorem derived90927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 4503) ∨ (¬ p 4345) ∨ (p 2383) ∨ (p 2459) :=
  ElevenRUP.step90927 (p 2383) (p 2387) (p 2459) (p 3654) (p 4345) (p 4348) (p 4503) (derived73246 p h) (derived73562 p h) (derived54038 p h)

theorem derived90928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4623) ∨ (p 2307) ∨ (¬ p 3654) ∨ (p 3246) ∨ (¬ p 4556) :=
  ElevenRUP.step90928 (p 2307) (p 2313) (p 3246) (p 3654) (p 3690) (p 4556) (p 4623) (derived73238 p h) (derived73446 p h) (derived49436 p h)

theorem derived90929 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3146) ∨ (¬ p 4433) ∨ (¬ p 4345) ∨ (p 2383) :=
  ElevenRUP.step90929 (p 2383) (p 2387) (p 3146) (p 3654) (p 3692) (p 4345) (p 4433) (derived73448 p h) (derived73246 p h) (derived41181 p h)

theorem derived90930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3323) ∨ (¬ p 4156) ∨ (p 2177) ∨ (¬ p 2264) ∨ (¬ p 2962) :=
  ElevenRUP.step90930 (p 2177) (p 2264) (p 2299) (p 2962) (p 3323) (p 3654) (p 4037) (p 4156) (derived73508 p h) (derived73234 p h) (derived45733 p h)

theorem derived90931 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4623) ∨ (p 2307) ∨ (p 2417) ∨ (¬ p 3654) ∨ (¬ p 4276) :=
  ElevenRUP.step90931 (p 2307) (p 2313) (p 2417) (p 3654) (p 4276) (p 4278) (p 4623) (derived73238 p h) (derived73546 p h) (derived41216 p h)

theorem derived90936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2307) ∨ (¬ p 4623) ∨ (¬ p 2553) ∨ (¬ p 2761) :=
  ElevenRUP.step90936 (p 2307) (p 2313) (p 2553) (p 2761) (p 3654) (p 4623) (derived73238 p h) (derived52428 p h)

theorem derived90944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2786) ∨ (p 2696) ∨ (¬ p 4845) :=
  ElevenRUP.step90944 (p 2383) (p 2696) (p 2786) (p 2819) (p 3365) (p 4358) (p 4845) (derived73564 p h) (derived73390 p h) (derived42028 p h)

theorem derived90947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2122) ∨ (p 2598) ∨ (¬ p 2786) ∨ (¬ p 3923) ∨ (¬ p 4024) :=
  ElevenRUP.step90947 (p 2122) (p 2383) (p 2598) (p 2786) (p 3055) (p 3923) (p 4024) (derived73350 p h) (derived46907 p h)

theorem derived90952 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2406) ∨ (¬ p 2177) ∨ (p 2922) :=
  ElevenRUP.step90952 (p 2177) (p 2406) (p 2911) (p 2922) (p 2928) (p 3644) (derived73434 p h) (derived73320 p h) (derived63845 p h)

theorem derived90953 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2406) ∨ (p 2922) ∨ (¬ p 2881) :=
  ElevenRUP.step90953 (p 2406) (p 2881) (p 2911) (p 2922) (p 2928) (p 3644) (derived73434 p h) (derived73320 p h) (derived52381 p h)

theorem derived90955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 2406) ∨ (p 2230) ∨ (p 2493) ∨ (¬ p 4711) :=
  ElevenRUP.step90955 (p 2230) (p 2406) (p 2493) (p 2499) (p 2589) (p 3389) (p 4711) (derived73284 p h) (derived73260 p h) (derived55288 p h)

theorem derived90956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3323) ∨ (p 3564) ∨ (p 2493) :=
  ElevenRUP.step90956 (p 2406) (p 2493) (p 2499) (p 3323) (p 3564) (p 4137) (derived73524 p h) (derived73260 p h) (derived45252 p h)

theorem derived90958 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3590) ∨ (¬ p 2785) ∨ (¬ p 2982) ∨ (¬ p 2406) ∨ (p 2829) ∨ (p 2383) ∨ (¬ p 4450) ∨ (¬ p 2598) :=
  ElevenRUP.step90958 (p 2363) (p 2383) (p 2387) (p 2406) (p 2598) (p 2785) (p 2829) (p 2982) (p 3590) (p 3688) (p 4347) (p 4450) (derived73560 p h) (derived73444 p h) (derived73246 p h) (derived71898 p h)

theorem derived90960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2284) ∨ (¬ p 4705) ∨ (¬ p 3743) ∨ (p 2493) ∨ (¬ p 2386) :=
  ElevenRUP.step90960 (p 2284) (p 2386) (p 2406) (p 2493) (p 2499) (p 3743) (p 4705) (derived73260 p h) (derived54371 p h)

theorem derived90962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2274) ∨ (¬ p 2386) ∨ (p 2493) ∨ (p 2307) :=
  ElevenRUP.step90962 (p 2274) (p 2307) (p 2313) (p 2386) (p 2406) (p 2493) (p 2499) (derived73260 p h) (derived73238 p h) (derived45966 p h)

theorem derived90965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (¬ p 2373) ∨ (¬ p 2573) :=
  ElevenRUP.step90965 (p 2373) (p 2406) (p 2493) (p 2499) (p 2573) (derived73260 p h) (derived57764 p h)

theorem derived90968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (p 2230) :=
  ElevenRUP.step90968 (p 2230) (p 2406) (p 2553) (p 2573) (p 2589) (derived73284 p h) (derived64011 p h)

theorem derived90969 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3125) ∨ (¬ p 2406) ∨ (p 2187) ∨ (¬ p 4022) ∨ (¬ p 4138) :=
  ElevenRUP.step90969 (p 2187) (p 2406) (p 3125) (p 3193) (p 3989) (p 4022) (p 4138) (derived73502 p h) (derived46072 p h)

theorem derived90971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2295) ∨ (p 2553) ∨ (p 2493) :=
  ElevenRUP.step90971 (p 2295) (p 2406) (p 2493) (p 2499) (p 2553) (p 2588) (derived73282 p h) (derived73260 p h) (derived56388 p h)

theorem derived90972 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2373) ∨ (¬ p 3379) ∨ (¬ p 2254) ∨ (¬ p 2406) ∨ (p 2295) ∨ (p 2177) ∨ (¬ p 4902) :=
  ElevenRUP.step90972 (p 2177) (p 2254) (p 2295) (p 2299) (p 2331) (p 2373) (p 2406) (p 2963) (p 3379) (p 3568) (p 4902) (derived73338 p h) (derived73416 p h) (derived73234 p h) (derived51069 p h)

theorem derived90974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2406) ∨ (¬ p 4705) ∨ (¬ p 4001) ∨ (p 2922) :=
  ElevenRUP.step90974 (p 2406) (p 2901) (p 2922) (p 2928) (p 4001) (p 4705) (derived73320 p h) (derived41940 p h)

theorem derived90976 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2406) ∨ (¬ p 4555) ∨ (¬ p 4001) ∨ (¬ p 2563) :=
  ElevenRUP.step90976 (p 2406) (p 2563) (p 2922) (p 2928) (p 4001) (p 4555) (derived73320 p h) (derived52919 p h)

theorem derived90979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (¬ p 3096) ∨ (¬ p 4885) ∨ (¬ p 2860) :=
  ElevenRUP.step90979 (p 2406) (p 2493) (p 2499) (p 2860) (p 3096) (p 4885) (derived73260 p h) (derived60030 p h)

theorem derived90985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 2891) ∨ (¬ p 2406) ∨ (¬ p 3379) :=
  ElevenRUP.step90985 (p 2406) (p 2427) (p 2891) (p 3379) (p 3486) (derived73398 p h) (derived57476 p h)

theorem derived90987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2427) ∨ (¬ p 3096) ∨ (¬ p 4558) ∨ (p 2493) :=
  ElevenRUP.step90987 (p 2406) (p 2427) (p 2493) (p 2499) (p 3096) (p 4558) (derived73260 p h) (derived60756 p h)

theorem derived90989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 4736) ∨ (¬ p 3698) ∨ (p 2132) ∨ (¬ p 3379) :=
  ElevenRUP.step90989 (p 2132) (p 2138) (p 2406) (p 3379) (p 3698) (p 4736) (derived73214 p h) (derived63254 p h)

theorem derived90993 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2122) ∨ (p 2307) ∨ (p 2819) ∨ (¬ p 5021) ∨ (¬ p 2373) ∨ (¬ p 4433) ∨ (¬ p 3379) :=
  ElevenRUP.step90993 (p 2122) (p 2307) (p 2313) (p 2373) (p 2406) (p 2819) (p 3379) (p 4358) (p 4433) (p 5021) (derived73238 p h) (derived73564 p h) (derived49171 p h)

theorem derived90995 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3125) ∨ (¬ p 2274) ∨ (¬ p 2962) ∨ (¬ p 2406) ∨ (¬ p 4109) :=
  ElevenRUP.step90995 (p 2274) (p 2406) (p 2962) (p 3125) (p 3654) (p 3744) (p 4109) (derived73454 p h) (derived46137 p h)

theorem derived90997 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2406) ∨ (¬ p 3422) ∨ (¬ p 3379) :=
  ElevenRUP.step90997 (p 2406) (p 2850) (p 3379) (p 3422) (p 3684) (derived73442 p h) (derived45212 p h)

theorem derived90998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2573) ∨ (¬ p 4814) ∨ (p 3016) ∨ (p 2230) :=
  ElevenRUP.step90998 (p 2230) (p 2406) (p 2573) (p 2589) (p 3016) (p 3574) (p 4814) (derived73422 p h) (derived73284 p h) (derived51130 p h)

theorem derived91005 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2406) ∨ (p 2922) ∨ (¬ p 3246) :=
  ElevenRUP.step91005 (p 2406) (p 2417) (p 2922) (p 2928) (p 3246) (p 4278) (derived73546 p h) (derived73320 p h) (derived55575 p h)

theorem derived91006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (p 3266) ∨ (¬ p 2406) ∨ (¬ p 2761) ∨ (¬ p 3516) ∨ (¬ p 4109) :=
  ElevenRUP.step91006 (p 2406) (p 2761) (p 3266) (p 3516) (p 4109) (p 4444) (p 4988) (derived73580 p h) (derived47362 p h)

theorem derived91007 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2406) ∨ (¬ p 2563) ∨ (¬ p 3379) :=
  ElevenRUP.step91007 (p 2406) (p 2563) (p 2608) (p 3379) (p 3954) (derived73498 p h) (derived64887 p h)

theorem derived91013 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3083) ∨ (¬ p 2509) ∨ (p 2850) :=
  ElevenRUP.step91013 (p 2406) (p 2509) (p 2850) (p 3083) (p 3684) (derived73442 p h) (derived46517 p h)

theorem derived91014 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (¬ p 4750) ∨ (p 2850) ∨ (¬ p 3016) :=
  ElevenRUP.step91014 (p 2406) (p 2493) (p 2499) (p 2850) (p 3016) (p 3684) (p 4750) (derived73260 p h) (derived73442 p h) (derived63145 p h)

theorem derived91015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4116) ∨ (¬ p 2406) ∨ (¬ p 2440) :=
  ElevenRUP.step91015 (p 2406) (p 2440) (p 2542) (p 4116) (derived73269 p h) (h 6867)

theorem derived91018 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2982) ∨ (p 2493) ∨ (¬ p 3096) ∨ (¬ p 5046) :=
  ElevenRUP.step91018 (p 2406) (p 2493) (p 2499) (p 2982) (p 3096) (p 5046) (derived73260 p h) (derived49804 p h)

theorem derived91023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2406) ∨ (¬ p 5191) ∨ (¬ p 3904) ∨ (p 3051) :=
  ElevenRUP.step91023 (p 2406) (p 2427) (p 3051) (p 3556) (p 3904) (p 5191) (derived73414 p h) (derived53151 p h)

theorem derived91024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2406) ∨ (¬ p 3948) ∨ (¬ p 4376) ∨ (¬ p 4210) ∨ (p 2230) :=
  ElevenRUP.step91024 (p 2230) (p 2406) (p 2589) (p 2608) (p 3948) (p 4210) (p 4376) (derived73284 p h) (derived67005 p h)

theorem derived91025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2641) ∨ (¬ p 2662) ∨ (¬ p 4972) ∨ (p 2230) ∨ (¬ p 4281) :=
  ElevenRUP.step91025 (p 2230) (p 2406) (p 2589) (p 2641) (p 2662) (p 4154) (p 4281) (p 4972) (derived73526 p h) (derived73284 p h) (derived41929 p h)

theorem derived91033 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2406) ∨ (p 2922) ∨ (¬ p 4108) ∨ (p 2230) :=
  ElevenRUP.step91033 (p 2230) (p 2406) (p 2417) (p 2589) (p 2922) (p 2928) (p 4108) (p 4278) (derived73546 p h) (derived73320 p h) (derived73284 p h) (derived43546 p h)

theorem derived91034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2177) ∨ (¬ p 4438) ∨ (¬ p 4108) ∨ (¬ p 4733) ∨ (p 2230) ∨ (¬ p 2406) ∨ (¬ p 2509) :=
  ElevenRUP.step91034 (p 2122) (p 2177) (p 2230) (p 2406) (p 2509) (p 2589) (p 2774) (p 4108) (p 4438) (p 4733) (derived73284 p h) (derived64054 p h)

theorem derived91036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (p 2187) ∨ (p 2230) ∨ (¬ p 3096) :=
  ElevenRUP.step91036 (p 2187) (p 2230) (p 2406) (p 2493) (p 2499) (p 2589) (p 3096) (p 3989) (derived73260 p h) (derived73502 p h) (derived73284 p h) (derived44149 p h)

theorem derived91039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4355) ∨ (¬ p 2406) ∨ (p 2493) ∨ (¬ p 3573) :=
  ElevenRUP.step91039 (p 2406) (p 2493) (p 2499) (p 3573) (p 4355) (derived73260 p h) (h 31296)

theorem derived91042 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2406) ∨ (¬ p 2373) ∨ (¬ p 4001) ∨ (¬ p 4904) :=
  ElevenRUP.step91042 (p 2373) (p 2406) (p 2922) (p 2928) (p 4001) (p 4904) (derived73320 p h) (derived55300 p h)

theorem derived91043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2220) ∨ (¬ p 3904) ∨ (¬ p 5191) ∨ (¬ p 2406) :=
  ElevenRUP.step91043 (p 2220) (p 2373) (p 2406) (p 3904) (p 4120) (p 5191) (derived73522 p h) (derived41409 p h)

theorem derived91044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 4902) ∨ (¬ p 3379) ∨ (p 2383) ∨ (p 2363) ∨ (¬ p 2459) ∨ (¬ p 5021) :=
  ElevenRUP.step91044 (p 2363) (p 2373) (p 2383) (p 2387) (p 2406) (p 2459) (p 3379) (p 4347) (p 4902) (p 5021) (derived73246 p h) (derived73560 p h) (derived48066 p h)

theorem derived91047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2608) ∨ (p 2850) ∨ (¬ p 3379) :=
  ElevenRUP.step91047 (p 2406) (p 2608) (p 2850) (p 3379) (p 3684) (p 3954) (derived73498 p h) (derived73442 p h) (derived43900 p h)

theorem derived91048 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 3032) ∨ (¬ p 3740) ∨ (¬ p 3379) ∨ (¬ p 2406) ∨ (¬ p 4644) :=
  ElevenRUP.step91048 (p 2406) (p 3032) (p 3379) (p 3399) (p 3740) (p 4366) (p 4644) (derived73570 p h) (derived50237 p h)

theorem derived91049 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (p 2437) ∨ (p 2493) ∨ (¬ p 4644) ∨ (¬ p 2406) :=
  ElevenRUP.step91049 (p 2406) (p 2437) (p 2493) (p 2499) (p 3016) (p 3742) (p 4644) (derived73452 p h) (derived73260 p h) (derived55168 p h)

theorem derived91050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2946) ∨ (¬ p 4814) ∨ (¬ p 2651) ∨ (¬ p 3879) :=
  ElevenRUP.step91050 (p 2406) (p 2651) (p 2946) (p 2952) (p 3879) (p 4814) (derived73330 p h) (derived53969 p h)

theorem derived91051 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2406) ∨ (¬ p 2440) ∨ (p 2922) :=
  ElevenRUP.step91051 (p 2406) (p 2440) (p 2911) (p 2922) (p 2928) (p 3644) (derived73434 p h) (derived73320 p h) (derived47331 p h)

theorem derived91054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2249) ∨ (¬ p 2440) ∨ (p 2651) ∨ (¬ p 4281) :=
  ElevenRUP.step91054 (p 2249) (p 2406) (p 2440) (p 2651) (p 2657) (p 4281) (derived73288 p h) (derived51765 p h)

theorem derived91056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2630) ∨ (¬ p 2751) ∨ (¬ p 4281) ∨ (¬ p 2440) :=
  ElevenRUP.step91056 (p 2406) (p 2440) (p 2630) (p 2751) (p 2810) (p 4281) (derived73316 p h) (derived62992 p h)

theorem derived91057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2440) ∨ (p 2493) ∨ (p 2553) :=
  ElevenRUP.step91057 (p 2406) (p 2440) (p 2493) (p 2499) (p 2553) (p 2588) (derived73260 p h) (derived73282 p h) (derived45355 p h)

theorem derived91059 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2797) ∨ (p 2850) ∨ (¬ p 3364) ∨ (¬ p 3379) :=
  ElevenRUP.step91059 (p 2406) (p 2797) (p 2850) (p 3364) (p 3379) (p 3684) (derived73442 p h) (derived55730 p h)

theorem derived91060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2307) ∨ (¬ p 2497) ∨ (p 3309) ∨ (¬ p 2578) ∨ (¬ p 4715) :=
  ElevenRUP.step91060 (p 2307) (p 2406) (p 2497) (p 2578) (p 3309) (p 3549) (p 4715) (derived73406 p h) (derived60021 p h)

theorem derived91061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2274) ∨ (p 2573) ∨ (p 2553) ∨ (¬ p 3347) :=
  ElevenRUP.step91061 (p 2274) (p 2406) (p 2553) (p 2573) (p 2579) (p 2588) (p 3347) (derived73274 p h) (derived73282 p h) (derived45464 p h)

theorem derived91063 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3016) ∨ (p 2573) ∨ (¬ p 3347) ∨ (p 2850) :=
  ElevenRUP.step91063 (p 2406) (p 2573) (p 2579) (p 2850) (p 3016) (p 3347) (p 3684) (derived73274 p h) (derived73442 p h) (derived57986 p h)

theorem derived91066 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 4949) :=
  ElevenRUP.step91066 (p 2406) (p 3379) (p 3830) (p 3834) (p 4949) (derived73474 p h) (derived67178 p h)

theorem derived91067 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 2563) :=
  ElevenRUP.step91067 (p 2241) (p 2247) (p 2406) (p 2563) (p 3379) (derived73226 p h) (derived45079 p h)

theorem derived91068 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 2440) :=
  ElevenRUP.step91068 (p 2406) (p 2440) (p 2608) (p 3379) (p 3954) (derived73498 p h) (derived44567 p h)

theorem derived91069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2406) ∨ (p 3083) ∨ (p 2922) :=
  ElevenRUP.step91069 (p 2406) (p 2437) (p 2922) (p 2928) (p 3083) (p 4256) (derived73542 p h) (derived73320 p h) (derived46502 p h)

theorem derived91070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2996) ∨ (¬ p 2662) ∨ (¬ p 4650) ∨ (p 2230) ∨ (¬ p 4281) :=
  ElevenRUP.step91070 (p 2230) (p 2406) (p 2589) (p 2662) (p 2996) (p 4281) (p 4650) (derived73284 p h) (derived41289 p h)

theorem derived91073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (¬ p 4539) ∨ (¬ p 2156) ∨ (¬ p 3096) :=
  ElevenRUP.step91073 (p 2156) (p 2406) (p 2493) (p 2499) (p 3096) (p 4539) (derived73260 p h) (derived50822 p h)

theorem derived91076 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2406) ∨ (p 2230) ∨ (p 2493) ∨ (¬ p 4108) :=
  ElevenRUP.step91076 (p 2230) (p 2241) (p 2406) (p 2493) (p 2499) (p 2589) (p 4108) (derived73284 p h) (derived73260 p h) (derived55409 p h)

theorem derived91078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 2363) ∨ (¬ p 4450) ∨ (p 2331) ∨ (¬ p 3379) ∨ (¬ p 2254) ∨ (¬ p 2406) ∨ (p 2668) :=
  ElevenRUP.step91078 (p 2254) (p 2331) (p 2363) (p 2406) (p 2668) (p 2963) (p 2982) (p 3324) (p 3379) (p 4347) (p 4450) (derived73560 p h) (derived73338 p h) (derived73386 p h) (derived49080 p h)

theorem derived91081 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2177) ∨ (¬ p 3379) ∨ (¬ p 2982) ∨ (¬ p 2406) ∨ (p 2307) ∨ (¬ p 5021) ∨ (¬ p 4450) :=
  ElevenRUP.step91081 (p 2177) (p 2299) (p 2307) (p 2313) (p 2406) (p 2459) (p 2982) (p 3379) (p 4348) (p 4450) (p 5021) (derived73562 p h) (derived73234 p h) (derived73238 p h) (derived54386 p h)

theorem derived91086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 4870) ∨ (¬ p 4108) ∨ (p 2230) ∨ (¬ p 3541) ∨ (¬ p 2406) :=
  ElevenRUP.step91086 (p 2230) (p 2406) (p 2589) (p 3093) (p 3541) (p 4108) (p 4870) (derived73284 p h) (derived48770 p h)

theorem derived91087 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 2406) ∨ (¬ p 2363) ∨ (¬ p 3573) ∨ (p 2493) ∨ (¬ p 4371) ∨ (¬ p 4608) :=
  ElevenRUP.step91087 (p 2363) (p 2406) (p 2493) (p 2496) (p 3073) (p 3573) (p 4261) (p 4371) (p 4608) (derived73544 p h) (derived73258 p h) (derived66669 p h)

theorem derived91091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 2528) ∨ (¬ p 2406) ∨ (¬ p 2363) :=
  ElevenRUP.step91091 (p 2363) (p 2406) (p 2509) (p 2528) (p 2534) (derived73268 p h) (derived57873 p h)

theorem derived91092 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 4108) ∨ (p 2230) ∨ (¬ p 2406) ∨ (¬ p 2509) :=
  ElevenRUP.step91092 (p 2230) (p 2406) (p 2509) (p 2528) (p 2534) (p 2589) (p 4108) (derived73268 p h) (derived73284 p h) (derived52370 p h)

theorem derived91094 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 3256) ∨ (¬ p 4736) ∨ (¬ p 4450) ∨ (¬ p 2982) ∨ (p 2696) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step91094 (p 2406) (p 2696) (p 2982) (p 3005) (p 3256) (p 3365) (p 3379) (p 3877) (p 4118) (p 4450) (p 4736) (derived73488 p h) (derived73520 p h) (derived73390 p h) (derived50416 p h)

theorem derived91097 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3266) ∨ (¬ p 2982) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 4450) ∨ (¬ p 5021) ∨ (¬ p 3322) ∨ (p 2383) :=
  ElevenRUP.step91097 (p 2383) (p 2387) (p 2406) (p 2982) (p 3266) (p 3322) (p 3379) (p 3461) (p 4191) (p 4450) (p 5021) (derived73530 p h) (derived73246 p h) (derived48235 p h)

theorem derived91101 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (p 3286) ∨ (¬ p 5171) ∨ (¬ p 3379) ∨ (¬ p 4949) ∨ (¬ p 2406) :=
  ElevenRUP.step91101 (p 2245) (p 2406) (p 3286) (p 3292) (p 3379) (p 4949) (p 5171) (derived73378 p h) (derived42148 p h)

theorem derived91102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 2341) ∨ (¬ p 2177) ∨ (¬ p 2406) ∨ (¬ p 5210) ∨ (¬ p 4395) ∨ (¬ p 3379) ∨ (p 2396) :=
  ElevenRUP.step91102 (p 2177) (p 2341) (p 2396) (p 2406) (p 2982) (p 3379) (p 3551) (p 4107) (p 4395) (p 5210) (derived73408 p h) (derived73514 p h) (derived63305 p h)

theorem derived91104 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 2406) ∨ (p 2098) ∨ (¬ p 4736) ∨ (¬ p 2373) ∨ (¬ p 2459) ∨ (¬ p 4902) ∨ (¬ p 3379) :=
  ElevenRUP.step91104 (p 2098) (p 2104) (p 2373) (p 2406) (p 2459) (p 3379) (p 3609) (p 4340) (p 4736) (p 4902) (derived73558 p h) (derived73204 p h) (derived53382 p h)

theorem derived91110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2406) ∨ (¬ p 4001) ∨ (¬ p 4885) ∨ (p 2922) :=
  ElevenRUP.step91110 (p 2406) (p 2870) (p 2922) (p 2928) (p 4001) (p 4885) (derived73320 p h) (derived49072 p h)

theorem derived91111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2528) ∨ (¬ p 4608) ∨ (¬ p 2474) ∨ (p 2088) ∨ (¬ p 3347) :=
  ElevenRUP.step91111 (p 2088) (p 2406) (p 2474) (p 2528) (p 3347) (p 3857) (p 4608) (derived73480 p h) (derived41322 p h)

theorem derived91113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 4116) ∨ (p 3016) ∨ (¬ p 3660) :=
  ElevenRUP.step91113 (p 2406) (p 3016) (p 3574) (p 3660) (p 4116) (derived73422 p h) (h 20004)

theorem derived91116 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2406) ∨ (p 2352) ∨ (¬ p 2187) :=
  ElevenRUP.step91116 (p 2187) (p 2352) (p 2406) (p 2493) (p 2499) (p 3956) (derived73260 p h) (derived73500 p h) (derived46901 p h)

theorem derived91125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 2406) ∨ (p 3319) ∨ (¬ p 4715) ∨ (¬ p 2497) :=
  ElevenRUP.step91125 (p 2406) (p 2497) (p 3319) (p 3564) (p 4026) (p 4715) (derived73504 p h) (derived49643 p h)

theorem derived91128 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2982) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step91128 (p 2406) (p 2608) (p 2982) (p 3379) (p 3954) (derived73498 p h) (derived43925 p h)

theorem derived91129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 3461) ∨ (¬ p 2406) ∨ (¬ p 2982) :=
  ElevenRUP.step91129 (p 2406) (p 2982) (p 3461) (p 3680) (p 4191) (derived73530 p h) (derived56500 p h)

theorem derived91130 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 2761) ∨ (¬ p 3379) ∨ (p 3654) ∨ (¬ p 2982) ∨ (¬ p 2406) ∨ (¬ p 5021) ∨ (¬ p 4395) :=
  ElevenRUP.step91130 (p 2406) (p 2761) (p 2982) (p 3379) (p 3461) (p 3654) (p 3946) (p 4191) (p 4395) (p 5021) (derived73530 p h) (derived73492 p h) (derived42526 p h)

theorem derived91131 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 2440) :=
  ElevenRUP.step91131 (p 2241) (p 2247) (p 2406) (p 2440) (p 3379) (derived73226 p h) (derived54220 p h)

theorem derived91138 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2911) ∨ (¬ p 4644) ∨ (¬ p 2406) ∨ (¬ p 2926) :=
  ElevenRUP.step91138 (p 2406) (p 2911) (p 2926) (p 3527) (p 3548) (p 4644) (derived73404 p h) (derived49592 p h)

theorem derived91149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2437) ∨ (p 2922) ∨ (¬ p 4750) ∨ (p 2850) :=
  ElevenRUP.step91149 (p 2406) (p 2437) (p 2850) (p 2922) (p 2928) (p 3684) (p 4750) (derived73320 p h) (derived73442 p h) (derived50808 p h)

theorem derived91150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2406) ∨ (p 2922) ∨ (¬ p 2373) :=
  ElevenRUP.step91150 (p 2373) (p 2406) (p 2437) (p 2922) (p 2928) (derived73320 p h) (derived45676 p h)

theorem derived91157 (p : Nat → Prop) (h : Inputs p) :
    (p 4025) ∨ (p 2396) :=
  ElevenRUP.step91157 (p 2396) (p 4025) (p 5845) (derived74137 p h) (h 12066)

theorem derived91159 (p : Nat → Prop) (h : Inputs p) :
    (p 4623) ∨ (¬ p 2396) :=
  ElevenRUP.step91159 (p 2396) (p 4623) (p 5846) (derived74139 p h) (h 12070)

theorem derived91160 (p : Nat → Prop) (h : Inputs p) :
    (p 4187) ∨ (¬ p 2396) :=
  ElevenRUP.step91160 (p 2396) (p 4187) (p 5846) (derived74139 p h) (h 12071)

theorem derived91164 (p : Nat → Prop) (h : Inputs p) :
    (p 4343) ∨ (p 2630) :=
  ElevenRUP.step91164 (p 2630) (p 4343) (p 5890) (derived74193 p h) (h 12325)

theorem derived91165 (p : Nat → Prop) (h : Inputs p) :
    (p 2811) ∨ (p 2696) :=
  ElevenRUP.step91165 (p 2696) (p 2811) (p 5902) (derived74209 p h) (h 12394)

theorem derived91166 (p : Nat → Prop) (h : Inputs p) :
    (p 4236) ∨ (p 2696) :=
  ElevenRUP.step91166 (p 2696) (p 4236) (p 5902) (derived74209 p h) (h 12397)

theorem derived91169 (p : Nat → Prop) (h : Inputs p) :
    (p 4186) ∨ (p 2911) :=
  ElevenRUP.step91169 (p 2911) (p 4186) (p 5950) (derived74273 p h) (h 12683)

theorem derived91178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 4204) ∨ (¬ p 2143) ∨ (p 2156) :=
  ElevenRUP.step91178 (p 2143) (p 2156) (p 2870) (p 3646) (p 4204) (derived73436 p h) (h 20402)

theorem derived91181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 2839) ∨ (¬ p 2427) ∨ (p 3051) ∨ (¬ p 2143) :=
  ElevenRUP.step91181 (p 2143) (p 2427) (p 2839) (p 3051) (p 3367) (p 3556) (p 3583) (derived73424 p h) (derived73414 p h) (derived45323 p h)

theorem derived91182 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2737) ∨ (¬ p 2143) ∨ (p 2839) ∨ (p 2881) :=
  ElevenRUP.step91182 (p 2143) (p 2737) (p 2839) (p 2881) (p 3051) (p 3556) (p 3570) (p 3583) (derived73414 p h) (derived73424 p h) (derived73418 p h) (derived63259 p h)

theorem derived91190 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 4198) ∨ (¬ p 2143) ∨ (¬ p 2274) ∨ (p 2839) ∨ (p 2187) :=
  ElevenRUP.step91190 (p 2143) (p 2187) (p 2274) (p 2307) (p 2313) (p 2839) (p 3583) (p 3989) (p 4198) (derived73238 p h) (derived73424 p h) (derived73502 p h) (derived54346 p h)

theorem derived91197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2742) ∨ (p 3246) ∨ (¬ p 2264) ∨ (p 3051) ∨ (p 2996) ∨ (¬ p 2696) ∨ (¬ p 4666) ∨ (¬ p 2143) ∨ (p 2839) :=
  ElevenRUP.step91197 (p 2143) (p 2264) (p 2696) (p 2742) (p 2839) (p 2996) (p 3027) (p 3051) (p 3246) (p 3556) (p 3583) (p 3690) (p 4666) (derived73446 p h) (derived73414 p h) (derived73340 p h) (derived73424 p h) (derived71907 p h)

theorem derived91198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2839) ∨ (p 2156) ∨ (¬ p 2143) ∨ (¬ p 4344) ∨ (¬ p 4558) :=
  ElevenRUP.step91198 (p 2143) (p 2156) (p 2707) (p 2839) (p 3583) (p 3646) (p 4344) (p 4558) (derived73424 p h) (derived73436 p h) (derived49314 p h)

theorem derived91199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 3051) ∨ (p 2881) ∨ (¬ p 3919) ∨ (¬ p 4668) ∨ (p 2839) ∨ (¬ p 3005) ∨ (¬ p 2143) ∨ (¬ p 2696) :=
  ElevenRUP.step91199 (p 2143) (p 2449) (p 2696) (p 2839) (p 2881) (p 3005) (p 3051) (p 3556) (p 3570) (p 3583) (p 3919) (p 4668) (derived73414 p h) (derived73418 p h) (derived73424 p h) (derived71908 p h)

theorem derived91203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (p 2156) ∨ (¬ p 2143) ∨ (p 3125) ∨ (p 2839) ∨ (¬ p 4604) ∨ (¬ p 2742) ∨ (¬ p 3256) ∨ (¬ p 2696) :=
  ElevenRUP.step91203 (p 2143) (p 2156) (p 2696) (p 2742) (p 2839) (p 3125) (p 3189) (p 3256) (p 3583) (p 3646) (p 3744) (p 4604) (derived73436 p h) (derived73454 p h) (derived73424 p h) (derived71910 p h)

theorem derived91210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 2274) ∨ (¬ p 2143) ∨ (p 2284) ∨ (p 2839) ∨ (¬ p 2951) :=
  ElevenRUP.step91210 (p 2143) (p 2274) (p 2284) (p 2737) (p 2839) (p 2951) (p 3097) (p 3583) (p 3952) (derived73352 p h) (derived73496 p h) (derived73424 p h) (derived46504 p h)

theorem derived91212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3695) ∨ (p 3516) ∨ (¬ p 2934) ∨ (¬ p 4984) ∨ (p 2493) ∨ (¬ p 2143) ∨ (¬ p 4715) :=
  ElevenRUP.step91212 (p 2143) (p 2493) (p 2499) (p 2934) (p 3516) (p 3631) (p 3695) (p 3821) (p 4715) (p 4984) (derived73470 p h) (derived73260 p h) (derived51527 p h)

theorem derived91213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2143) ∨ (p 2839) ∨ (p 2563) ∨ (p 2220) :=
  ElevenRUP.step91213 (p 2143) (p 2220) (p 2373) (p 2563) (p 2839) (p 3583) (p 4110) (p 4120) (derived73424 p h) (derived73516 p h) (derived73522 p h) (derived43971 p h)

theorem derived91216 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2839) ∨ (¬ p 2143) ∨ (p 3051) ∨ (¬ p 2177) :=
  ElevenRUP.step91216 (p 2143) (p 2177) (p 2839) (p 2881) (p 3051) (p 3556) (p 3570) (p 3583) (derived73418 p h) (derived73424 p h) (derived73414 p h) (derived46621 p h)

theorem derived91218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3461) ∨ (¬ p 2143) ∨ (¬ p 4032) ∨ (p 2839) :=
  ElevenRUP.step91218 (p 2143) (p 2839) (p 3461) (p 3583) (p 4032) (p 4322) (derived73424 p h) (derived56873 p h)

theorem derived91220 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3366) ∨ (¬ p 5052) ∨ (¬ p 2819) ∨ (¬ p 4133) ∨ (¬ p 4119) ∨ (¬ p 2143) ∨ (¬ p 2459) ∨ (¬ p 2829) ∨ (p 2696) ∨ (p 3051) :=
  ElevenRUP.step91220 (p 2143) (p 2459) (p 2696) (p 2819) (p 2829) (p 3051) (p 3146) (p 3365) (p 3366) (p 3556) (p 3692) (p 4119) (p 4133) (p 5052) (derived73448 p h) (derived73390 p h) (derived73414 p h) (derived63689 p h)

theorem derived91222 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3564) ∨ (p 2220) ∨ (¬ p 2598) ∨ (¬ p 2143) ∨ (¬ p 2493) ∨ (¬ p 4330) ∨ (¬ p 3590) ∨ (p 2839) :=
  ElevenRUP.step91222 (p 2143) (p 2220) (p 2493) (p 2598) (p 2839) (p 3146) (p 3564) (p 3583) (p 3590) (p 3692) (p 4120) (p 4330) (derived73448 p h) (derived73522 p h) (derived73424 p h) (derived71914 p h)

theorem derived91230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2737) ∨ (¬ p 2143) ∨ (p 2156) :=
  ElevenRUP.step91230 (p 2143) (p 2156) (p 2192) (p 2737) (p 3646) (p 4515) (derived73612 p h) (derived73436 p h) (derived66780 p h)

theorem derived91231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 3146) ∨ (p 2220) ∨ (p 2839) ∨ (¬ p 2143) :=
  ElevenRUP.step91231 (p 2143) (p 2220) (p 2737) (p 2839) (p 3146) (p 3583) (p 3692) (p 4120) (derived73448 p h) (derived73522 p h) (derived73424 p h) (derived46871 p h)

theorem derived91232 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2839) ∨ (¬ p 2143) ∨ (p 3266) ∨ (p 2220) :=
  ElevenRUP.step91232 (p 2143) (p 2220) (p 2839) (p 3146) (p 3266) (p 3583) (p 3692) (p 4120) (p 4444) (derived73448 p h) (derived73424 p h) (derived73580 p h) (derived73522 p h) (derived45549 p h)

theorem derived91239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4428) ∨ (¬ p 3918) ∨ (p 3093) ∨ (¬ p 2210) ∨ (¬ p 4509) ∨ (¬ p 2166) :=
  ElevenRUP.step91239 (p 2166) (p 2210) (p 3093) (p 3591) (p 3918) (p 4428) (p 4509) (derived73432 p h) (derived64915 p h)

theorem derived91243 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 3918) ∨ (¬ p 2210) ∨ (¬ p 4428) ∨ (¬ p 2373) ∨ (¬ p 4509) ∨ (¬ p 4210) :=
  ElevenRUP.step91243 (p 2210) (p 2373) (p 3093) (p 3591) (p 3918) (p 4210) (p 4428) (p 4509) (derived73432 p h) (derived64932 p h)

theorem derived91249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 2449) ∨ (¬ p 3156) ∨ (¬ p 4386) ∨ (¬ p 4509) ∨ (¬ p 4428) ∨ (¬ p 3426) :=
  ElevenRUP.step91249 (p 2449) (p 3156) (p 3426) (p 3434) (p 3947) (p 4386) (p 4428) (p 4509) (derived73494 p h) (derived64474 p h)

theorem derived91251 (p : Nat → Prop) (h : Inputs p) :
    (p 4346) ∨ (¬ p 3083) :=
  ElevenRUP.step91251 (p 3083) (p 4346) (p 5978) (derived74307 p h) (h 12858)

theorem derived91252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2797) ∨ (¬ p 5051) ∨ (¬ p 4972) ∨ (p 2696) ∨ (¬ p 4700) :=
  ElevenRUP.step91252 (p 2132) (p 2696) (p 2797) (p 3365) (p 4195) (p 4700) (p 4972) (p 5051) (derived73532 p h) (derived73390 p h) (derived56869 p h)

theorem derived91255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 4984) ∨ (¬ p 2881) ∨ (p 2341) ∨ (¬ p 2870) :=
  ElevenRUP.step91255 (p 2140) (p 2341) (p 2870) (p 2881) (p 3551) (p 4984) (derived73408 p h) (derived50647 p h)

theorem derived91258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2284) ∨ (¬ p 3985) ∨ (¬ p 5053) ∨ (p 3125) :=
  ElevenRUP.step91258 (p 2284) (p 3125) (p 3483) (p 3744) (p 3952) (p 3985) (p 5053) (derived73496 p h) (derived73454 p h) (derived56492 p h)

theorem derived91259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 3699) ∨ (¬ p 5053) ∨ (¬ p 2946) ∨ (p 2807) :=
  ElevenRUP.step91259 (p 2807) (p 2870) (p 2946) (p 3414) (p 3699) (p 5053) (derived73392 p h) (derived56425 p h)

theorem derived91261 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2122) ∨ (¬ p 4717) ∨ (p 2850) ∨ (¬ p 2386) ∨ (¬ p 4375) :=
  ElevenRUP.step91261 (p 2122) (p 2307) (p 2313) (p 2386) (p 2850) (p 3684) (p 4375) (p 4717) (derived73238 p h) (derived73442 p h) (derived42485 p h)

theorem derived91264 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 4375) ∨ (¬ p 3367) ∨ (¬ p 3366) :=
  ElevenRUP.step91264 (p 2774) (p 2780) (p 3366) (p 3367) (p 4375) (derived73308 p h) (h 20303)

theorem derived91265 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 3434) ∨ (¬ p 4375) ∨ (p 2437) ∨ (¬ p 3426) ∨ (¬ p 4279) ∨ (¬ p 4753) :=
  ElevenRUP.step91265 (p 2437) (p 3426) (p 3434) (p 3516) (p 3742) (p 3821) (p 4279) (p 4375) (p 4753) (derived73470 p h) (derived73452 p h) (derived42359 p h)

theorem derived91266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 3201) ∨ (p 2352) ∨ (¬ p 2437) ∨ (¬ p 4375) :=
  ElevenRUP.step91266 (p 2352) (p 2437) (p 2819) (p 3201) (p 3876) (p 3956) (p 4375) (derived73486 p h) (derived73500 p h) (derived62593 p h)

theorem derived91269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2383) ∨ (¬ p 2785) :=
  ElevenRUP.step91269 (p 2383) (p 2387) (p 2785) (p 2819) (derived73246 p h) (h 6268)

theorem derived91273 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (p 2829) ∨ (¬ p 2785) ∨ (¬ p 2553) ∨ (¬ p 2737) :=
  ElevenRUP.step91273 (p 2307) (p 2313) (p 2553) (p 2737) (p 2785) (p 2829) (p 3688) (derived73238 p h) (derived73444 p h) (derived62188 p h)

theorem derived91275 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (¬ p 4475) ∨ (p 3654) ∨ (¬ p 4620) ∨ (¬ p 2785) :=
  ElevenRUP.step91275 (p 2707) (p 2785) (p 2829) (p 3654) (p 3688) (p 3946) (p 4475) (p 4620) (derived73444 p h) (derived73492 p h) (derived59437 p h)

theorem derived91278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (¬ p 2553) ∨ (¬ p 2737) ∨ (p 2295) ∨ (p 2829) ∨ (¬ p 2785) :=
  ElevenRUP.step91278 (p 2295) (p 2553) (p 2737) (p 2785) (p 2829) (p 3567) (p 3568) (p 3688) (derived73416 p h) (derived73444 p h) (derived62187 p h)

theorem derived91280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3654) ∨ (p 3156) ∨ (¬ p 5045) ∨ (¬ p 2122) ∨ (¬ p 2785) :=
  ElevenRUP.step91280 (p 2122) (p 2785) (p 3115) (p 3156) (p 3497) (p 3654) (p 3946) (p 5045) (derived73492 p h) (derived73400 p h) (derived46909 p h)

theorem derived91284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 3322) ∨ (¬ p 3923) :=
  ElevenRUP.step91284 (p 3319) (p 3322) (p 3923) (p 4026) (derived73503 p h) (h 37641)

theorem derived91287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 4623) ∨ (¬ p 4668) ∨ (p 2177) ∨ (p 2553) :=
  ElevenRUP.step91287 (p 2177) (p 2299) (p 2553) (p 2588) (p 3564) (p 4623) (p 4668) (derived73234 p h) (derived73282 p h) (derived57898 p h)

theorem derived91291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2417) ∨ (¬ p 2274) ∨ (¬ p 3581) ∨ (¬ p 3958) :=
  ElevenRUP.step91291 (p 2274) (p 2396) (p 2417) (p 3581) (p 3958) (p 4278) (derived73546 p h) (derived51860 p h)

theorem derived91293 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2352) ∨ (¬ p 3581) ∨ (¬ p 3550) :=
  ElevenRUP.step91293 (p 2352) (p 2911) (p 3550) (p 3581) (p 3644) (p 3956) (derived73434 p h) (derived73499 p h) (h 33448)

theorem derived91294 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2274) ∨ (¬ p 2177) ∨ (¬ p 3958) ∨ (¬ p 3581) :=
  ElevenRUP.step91294 (p 2177) (p 2274) (p 2911) (p 3581) (p 3644) (p 3958) (derived73434 p h) (derived60360 p h)

theorem derived91295 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2449) ∨ (p 3156) ∨ (¬ p 3581) ∨ (¬ p 4203) ∨ (¬ p 2995) :=
  ElevenRUP.step91295 (p 2417) (p 2449) (p 2995) (p 3156) (p 3497) (p 3581) (p 4203) (p 4278) (derived73546 p h) (derived73400 p h) (derived69526 p h)

theorem derived91299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3434) ∨ (¬ p 3581) ∨ (¬ p 3958) ∨ (¬ p 2274) ∨ (¬ p 3658) :=
  ElevenRUP.step91299 (p 2274) (p 2396) (p 3434) (p 3581) (p 3658) (p 3958) (p 4324) (derived73556 p h) (derived57703 p h)

theorem derived91300 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 2386) ∨ (p 3016) ∨ (¬ p 2177) ∨ (¬ p 2311) ∨ (p 2396) :=
  ElevenRUP.step91300 (p 2177) (p 2311) (p 2341) (p 2386) (p 2396) (p 3016) (p 3551) (p 3574) (p 4107) (derived73408 p h) (derived73422 p h) (derived73514 p h) (derived61372 p h)

theorem derived91301 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2177) ∨ (¬ p 2386) ∨ (p 2307) ∨ (p 3016) :=
  ElevenRUP.step91301 (p 2177) (p 2299) (p 2307) (p 2313) (p 2386) (p 2459) (p 3016) (p 3574) (p 4348) (derived73562 p h) (derived73234 p h) (derived73238 p h) (derived73422 p h) (derived59709 p h)

theorem derived91302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5118) ∨ (¬ p 3564) ∨ (¬ p 2386) ∨ (¬ p 4345) ∨ (p 2383) :=
  ElevenRUP.step91302 (p 2383) (p 2386) (p 2387) (p 3564) (p 4345) (p 5118) (p 5580) (derived73246 p h) (derived49664 p h)

theorem derived91303 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2553) ∨ (¬ p 2386) :=
  ElevenRUP.step91303 (p 2307) (p 2313) (p 2386) (p 2553) (derived73238 p h) (h 15355)

theorem derived91305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2386) ∨ (p 2383) :=
  ElevenRUP.step91305 (p 2352) (p 2383) (p 2386) (p 2387) (derived73246 p h) (h 2909)

theorem derived91306 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (¬ p 2187) ∨ (¬ p 2386) ∨ (p 2383) ∨ (p 2493) :=
  ElevenRUP.step91306 (p 2187) (p 2274) (p 2383) (p 2386) (p 2387) (p 2493) (p 2499) (p 3097) (derived73352 p h) (derived73246 p h) (derived73260 p h) (derived43108 p h)

theorem derived91309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4331) ∨ (¬ p 3343) ∨ (p 3016) ∨ (¬ p 4624) ∨ (p 2553) :=
  ElevenRUP.step91309 (p 2553) (p 2588) (p 3016) (p 3343) (p 3574) (p 4331) (p 4624) (derived73422 p h) (derived73282 p h) (derived62001 p h)

theorem derived91310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 4331) ∨ (¬ p 2274) ∨ (¬ p 2440) ∨ (p 3125) :=
  ElevenRUP.step91310 (p 2274) (p 2440) (p 3125) (p 3343) (p 3744) (p 4331) (derived73454 p h) (derived55818 p h)

theorem derived91312 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3276) ∨ (p 2352) ∨ (¬ p 4603) ∨ (¬ p 4422) :=
  ElevenRUP.step91312 (p 2352) (p 3276) (p 3461) (p 3956) (p 4191) (p 4422) (p 4603) (derived73530 p h) (derived73500 p h) (derived56830 p h)

theorem derived91315 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 4949) :=
  ElevenRUP.step91315 (p 2982) (p 4946) (p 4949) (derived73844 p h) (h 8224)

theorem derived91321 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3830) ∨ (¬ p 2761) ∨ (¬ p 3399) :=
  ElevenRUP.step91321 (p 2761) (p 3399) (p 3707) (p 3830) (p 3834) (p 4321) (derived73554 p h) (derived73474 p h) (derived47807 p h)

theorem derived91322 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 5363) ∨ (¬ p 3399) :=
  ElevenRUP.step91322 (p 3399) (p 3830) (p 3834) (p 5363) (derived73474 p h) (h 30481)

theorem derived91323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5358) ∨ (p 3830) ∨ (¬ p 3246) ∨ (¬ p 4911) ∨ (¬ p 3399) :=
  ElevenRUP.step91323 (p 3246) (p 3399) (p 3830) (p 3834) (p 4911) (p 5358) (derived73474 p h) (derived42004 p h)

theorem derived91324 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 2417) ∨ (¬ p 3399) ∨ (¬ p 5358) ∨ (¬ p 2930) :=
  ElevenRUP.step91324 (p 2417) (p 2930) (p 3399) (p 3830) (p 3834) (p 5358) (derived73474 p h) (derived42141 p h)

theorem derived91328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (p 3830) ∨ (¬ p 3266) ∨ (¬ p 3847) ∨ (¬ p 2608) :=
  ElevenRUP.step91328 (p 2608) (p 3266) (p 3830) (p 3834) (p 3847) (p 5284) (derived73474 p h) (derived55687 p h)

theorem derived91329 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3830) ∨ (¬ p 2761) ∨ (¬ p 2608) :=
  ElevenRUP.step91329 (p 2608) (p 2761) (p 3707) (p 3830) (p 3834) (p 4321) (derived73554 p h) (derived73474 p h) (derived45833 p h)

theorem derived91330 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 2246) ∨ (¬ p 2807) ∨ (¬ p 2744) ∨ (¬ p 2608) ∨ (¬ p 3941) ∨ (¬ p 5119) ∨ (p 3830) ∨ (¬ p 2264) :=
  ElevenRUP.step91330 (p 2246) (p 2264) (p 2608) (p 2744) (p 2807) (p 3707) (p 3830) (p 3834) (p 3941) (p 4321) (p 5119) (derived73554 p h) (derived73474 p h) (derived52793 p h)

theorem derived91332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4388) ∨ (p 3830) ∨ (¬ p 5043) ∨ (¬ p 2192) ∨ (¬ p 2210) :=
  ElevenRUP.step91332 (p 2192) (p 2210) (p 3830) (p 3834) (p 4388) (p 5043) (derived73474 p h) (derived61033 p h)

theorem derived91334 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 5148) ∨ (¬ p 4843) ∨ (¬ p 4024) ∨ (¬ p 3323) ∨ (¬ p 3093) :=
  ElevenRUP.step91334 (p 3093) (p 3323) (p 3830) (p 3834) (p 4024) (p 4843) (p 5148) (derived73474 p h) (derived51541 p h)

end ElevenLogic
