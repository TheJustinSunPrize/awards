import SunPrize.Certificate.Derived039
import SunPrize.Certificate.Logic040
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived83665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 3051) ∨ (¬ p 2839) ∨ (¬ p 2136) :=
  ElevenRUP.step83665 (p 2136) (p 2839) (p 2870) (p 3051) (p 3556) (p 4734) (derived73414 p h) (derived72735 p h) (derived49768 p h)

theorem derived83666 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2839) ∨ (¬ p 2136) ∨ (p 2156) :=
  ElevenRUP.step83666 (p 2136) (p 2156) (p 2839) (p 2860) (p 3646) (p 4734) (derived72735 p h) (derived73436 p h) (derived49795 p h)

theorem derived83668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 2274) ∨ (p 3367) ∨ (¬ p 2137) ∨ (¬ p 2156) :=
  ElevenRUP.step83668 (p 2137) (p 2156) (p 2274) (p 2839) (p 3367) (p 3585) (derived73428 p h) (derived53795 p h)

theorem derived83673 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2839) ∨ (¬ p 3587) :=
  ElevenRUP.step83673 (p 2707) (p 2839) (p 3587) (p 3588) (derived73430 p h) (h 10452)

theorem derived83680 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2839) ∨ (¬ p 2860) ∨ (p 3425) :=
  ElevenRUP.step83680 (p 2707) (p 2839) (p 2860) (p 3425) (p 3471) (p 3588) (derived73430 p h) (derived73396 p h) (derived53390 p h)

theorem derived83683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 4428) ∨ (p 2829) ∨ (¬ p 2156) :=
  ElevenRUP.step83683 (p 2156) (p 2829) (p 2839) (p 3688) (p 4428) (derived73444 p h) (derived71567 p h)

theorem derived83684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2829) ∨ (¬ p 4882) ∨ (¬ p 4428) ∨ (¬ p 2563) :=
  ElevenRUP.step83684 (p 2563) (p 2829) (p 2839) (p 3688) (p 4428) (p 4882) (derived73444 p h) (derived49224 p h)

theorem derived83685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 2839) ∨ (¬ p 3985) ∨ (p 3367) ∨ (p 3125) :=
  ElevenRUP.step83685 (p 2839) (p 3125) (p 3367) (p 3483) (p 3585) (p 3744) (p 3985) (derived73428 p h) (derived73454 p h) (derived46282 p h)

theorem derived83691 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2132) ∨ (¬ p 3016) ∨ (¬ p 4342) ∨ (¬ p 2839) :=
  ElevenRUP.step83691 (p 2132) (p 2138) (p 2829) (p 2839) (p 3016) (p 3688) (p 4342) (derived73444 p h) (derived73214 p h) (derived55325 p h)

theorem derived83693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 3201) ∨ (p 3367) ∨ (¬ p 3695) ∨ (¬ p 4644) :=
  ElevenRUP.step83693 (p 2839) (p 3201) (p 3367) (p 3585) (p 3695) (p 3876) (p 4644) (derived73486 p h) (derived73428 p h) (derived41016 p h)

theorem derived83694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 2295) ∨ (¬ p 5021) ∨ (¬ p 2608) ∨ (p 2307) ∨ (p 3323) ∨ (¬ p 4397) ∨ (¬ p 2839) :=
  ElevenRUP.step83694 (p 2295) (p 2307) (p 2313) (p 2608) (p 2839) (p 3105) (p 3323) (p 4037) (p 4397) (p 5021) (derived73238 p h) (derived73508 p h) (derived42314 p h)

theorem derived83695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2962) ∨ (¬ p 2839) ∨ (¬ p 2187) ∨ (p 2274) ∨ (¬ p 2137) :=
  ElevenRUP.step83695 (p 2137) (p 2187) (p 2274) (p 2307) (p 2839) (p 2962) (p 3097) (derived73352 p h) (derived48917 p h)

theorem derived83697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (¬ p 2839) ∨ (p 2295) ∨ (¬ p 4902) ∨ (p 2331) ∨ (p 2177) ∨ (¬ p 2373) :=
  ElevenRUP.step83697 (p 2177) (p 2254) (p 2295) (p 2299) (p 2331) (p 2373) (p 2608) (p 2839) (p 2963) (p 3568) (p 3695) (p 4902) (derived73416 p h) (derived73338 p h) (derived73234 p h) (derived63352 p h)

theorem derived83700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4188) ∨ (¬ p 2098) ∨ (¬ p 3146) ∨ (p 2132) ∨ (¬ p 2839) :=
  ElevenRUP.step83700 (p 2098) (p 2132) (p 2138) (p 2839) (p 3146) (p 4188) (derived73214 p h) (derived47730 p h)

theorem derived83702 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2619) ∨ (¬ p 3589) ∨ (¬ p 2839) ∨ (p 3425) :=
  ElevenRUP.step83702 (p 2619) (p 2707) (p 2839) (p 3425) (p 3471) (p 3588) (p 3589) (derived73430 p h) (derived73396 p h) (derived52616 p h)

theorem derived83707 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 2839) ∨ (p 3367) ∨ (p 3422) :=
  ElevenRUP.step83707 (p 2132) (p 2138) (p 2839) (p 3367) (p 3422) (p 3584) (p 3585) (derived73214 p h) (derived73428 p h) (derived73426 p h) (derived45489 p h)

theorem derived83708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2839) ∨ (¬ p 4715) ∨ (p 3422) ∨ (p 3367) :=
  ElevenRUP.step83708 (p 2839) (p 3367) (p 3422) (p 3584) (p 3585) (p 3695) (p 4715) (derived73426 p h) (derived73428 p h) (derived51005 p h)

theorem derived83709 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 2839) ∨ (p 2737) ∨ (¬ p 4752) ∨ (¬ p 2598) :=
  ElevenRUP.step83709 (p 2132) (p 2138) (p 2598) (p 2737) (p 2743) (p 2839) (p 4752) (derived73214 p h) (derived73298 p h) (derived61027 p h)

theorem derived83710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2737) ∨ (¬ p 2860) ∨ (¬ p 2696) :=
  ElevenRUP.step83710 (p 2696) (p 2737) (p 2743) (p 2839) (p 2860) (derived73298 p h) (derived57383 p h)

theorem derived83712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 4902) ∨ (p 2331) ∨ (¬ p 2254) ∨ (p 2177) ∨ (p 2295) :=
  ElevenRUP.step83712 (p 2177) (p 2254) (p 2295) (p 2299) (p 2331) (p 2608) (p 2619) (p 2839) (p 2963) (p 3568) (p 4902) (derived73338 p h) (derived73234 p h) (derived73416 p h) (derived63175 p h)

theorem derived83714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2829) ∨ (¬ p 4428) ∨ (¬ p 4906) ∨ (¬ p 2284) :=
  ElevenRUP.step83714 (p 2284) (p 2829) (p 2839) (p 3688) (p 4428) (p 4906) (derived73444 p h) (derived42256 p h)

theorem derived83715 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3873) ∨ (p 2132) ∨ (¬ p 2750) ∨ (¬ p 2241) ∨ (¬ p 2839) :=
  ElevenRUP.step83715 (p 2132) (p 2138) (p 2241) (p 2750) (p 2839) (p 3873) (derived73214 p h) (derived41667 p h)

theorem derived83717 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2254) ∨ (¬ p 2839) ∨ (¬ p 2598) ∨ (p 2459) ∨ (¬ p 3589) ∨ (p 2807) ∨ (p 3367) ∨ (¬ p 2563) ∨ (¬ p 3695) :=
  ElevenRUP.step83717 (p 2254) (p 2264) (p 2459) (p 2563) (p 2598) (p 2807) (p 2839) (p 3367) (p 3414) (p 3553) (p 3585) (p 3589) (p 3695) (p 4348) (derived73410 p h) (derived73562 p h) (derived73392 p h) (derived73428 p h) (derived58413 p h)

theorem derived83718 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2737) ∨ (¬ p 2839) ∨ (p 2132) :=
  ElevenRUP.step83718 (p 2132) (p 2138) (p 2737) (p 2743) (p 2797) (p 2839) (p 4195) (derived73532 p h) (derived73298 p h) (derived73214 p h) (derived45636 p h)

theorem derived83722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (p 2230) ∨ (¬ p 5193) :=
  ElevenRUP.step83722 (p 2230) (p 2589) (p 2608) (p 2839) (p 3695) (p 5193) (derived73284 p h) (derived53042 p h)

theorem derived83725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 2528) ∨ (¬ p 5193) ∨ (¬ p 2839) ∨ (¬ p 2619) ∨ (¬ p 2459) ∨ (p 2470) ∨ (¬ p 4902) :=
  ElevenRUP.step83725 (p 2459) (p 2470) (p 2476) (p 2528) (p 2534) (p 2608) (p 2619) (p 2839) (p 4902) (p 5193) (derived73268 p h) (derived73250 p h) (derived51095 p h)

theorem derived83726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2839) ∨ (p 2220) ∨ (¬ p 2136) :=
  ElevenRUP.step83726 (p 2136) (p 2220) (p 2619) (p 2839) (p 4120) (p 4734) (derived73522 p h) (derived72735 p h) (derived49550 p h)

theorem derived83727 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) ∨ (¬ p 2608) ∨ (p 2573) ∨ (¬ p 4902) ∨ (¬ p 2839) ∨ (¬ p 5193) ∨ (¬ p 2619) ∨ (p 2177) :=
  ElevenRUP.step83727 (p 2177) (p 2299) (p 2553) (p 2573) (p 2579) (p 2588) (p 2608) (p 2619) (p 2839) (p 4902) (p 5193) (derived73282 p h) (derived73274 p h) (derived73234 p h) (derived52403 p h)

theorem derived83733 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2573) ∨ (¬ p 2860) ∨ (p 2363) ∨ (p 2352) ∨ (p 2284) ∨ (¬ p 5193) ∨ (¬ p 2608) :=
  ElevenRUP.step83733 (p 2284) (p 2352) (p 2363) (p 2573) (p 2579) (p 2608) (p 2839) (p 2860) (p 3952) (p 3956) (p 4347) (p 5193) (derived73274 p h) (derived73560 p h) (derived73500 p h) (derived73496 p h) (derived62034 p h)

theorem derived83734 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 5051) ∨ (¬ p 2651) ∨ (¬ p 2839) ∨ (p 2737) :=
  ElevenRUP.step83734 (p 2651) (p 2737) (p 2743) (p 2839) (p 2946) (p 2952) (p 5051) (derived73330 p h) (derived73298 p h) (derived55408 p h)

theorem derived83738 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5051) ∨ (p 2946) ∨ (¬ p 2839) ∨ (p 2737) :=
  ElevenRUP.step83738 (p 2737) (p 2743) (p 2839) (p 2946) (p 2952) (p 5051) (derived73330 p h) (derived73298 p h) (derived71568 p h)

theorem derived83741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 3367) ∨ (p 2696) ∨ (¬ p 5052) ∨ (¬ p 2839) :=
  ElevenRUP.step83741 (p 2598) (p 2696) (p 2839) (p 3365) (p 3367) (p 3585) (p 5052) (derived73428 p h) (derived73390 p h) (derived61368 p h)

theorem derived83744 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2839) ∨ (p 2352) ∨ (¬ p 2608) ∨ (¬ p 5193) ∨ (p 2363) ∨ (¬ p 3105) ∨ (¬ p 4450) :=
  ElevenRUP.step83744 (p 2352) (p 2363) (p 2573) (p 2579) (p 2608) (p 2839) (p 3105) (p 3956) (p 4347) (p 4450) (p 5193) (derived73274 p h) (derived73500 p h) (derived73560 p h) (derived51384 p h)

theorem derived83746 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2608) ∨ (¬ p 4450) ∨ (p 2331) ∨ (¬ p 2254) ∨ (p 2668) ∨ (¬ p 2839) ∨ (¬ p 3105) :=
  ElevenRUP.step83746 (p 2254) (p 2331) (p 2363) (p 2608) (p 2668) (p 2839) (p 2963) (p 3105) (p 3324) (p 4347) (p 4450) (derived73560 p h) (derived73338 p h) (derived73386 p h) (derived48339 p h)

theorem derived83748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 2132) ∨ (p 2396) ∨ (p 2707) ∨ (¬ p 2248) ∨ (¬ p 2839) ∨ (¬ p 3873) ∨ (¬ p 2807) ∨ (¬ p 4477) :=
  ElevenRUP.step83748 (p 2132) (p 2138) (p 2248) (p 2396) (p 2449) (p 2707) (p 2807) (p 2839) (p 3588) (p 3873) (p 4107) (p 4477) (derived73214 p h) (derived73514 p h) (derived73430 p h) (derived48859 p h)

theorem derived83751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 2363) ∨ (p 2383) ∨ (¬ p 2839) ∨ (¬ p 2619) ∨ (¬ p 4902) ∨ (¬ p 2459) ∨ (¬ p 5021) :=
  ElevenRUP.step83751 (p 2363) (p 2383) (p 2387) (p 2459) (p 2608) (p 2619) (p 2839) (p 4347) (p 4902) (p 5021) (derived73560 p h) (derived73246 p h) (derived57277 p h)

theorem derived83754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 2311) ∨ (¬ p 2839) ∨ (p 2396) ∨ (p 2341) ∨ (¬ p 2608) ∨ (¬ p 5021) ∨ (¬ p 4395) ∨ (¬ p 2177) :=
  ElevenRUP.step83754 (p 2177) (p 2311) (p 2341) (p 2396) (p 2608) (p 2839) (p 3105) (p 3551) (p 4107) (p 4395) (p 5021) (derived73514 p h) (derived73408 p h) (derived61502 p h)

theorem derived83755 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2870) ∨ (p 2807) ∨ (¬ p 2177) ∨ (¬ p 4556) ∨ (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2839) :=
  ElevenRUP.step83755 (p 2177) (p 2254) (p 2264) (p 2608) (p 2807) (p 2839) (p 2870) (p 3414) (p 3553) (p 4556) (derived73410 p h) (derived73392 p h) (derived63404 p h)

theorem derived83758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 2911) ∨ (p 2459) ∨ (¬ p 4450) ∨ (¬ p 2608) ∨ (¬ p 5193) ∨ (p 3389) ∨ (¬ p 2839) :=
  ElevenRUP.step83758 (p 2459) (p 2608) (p 2839) (p 2911) (p 3105) (p 3389) (p 3540) (p 3644) (p 4348) (p 4450) (p 5193) (derived73434 p h) (derived73562 p h) (derived73402 p h) (derived52112 p h)

theorem derived83762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 3367) ∨ (¬ p 2870) ∨ (¬ p 2881) :=
  ElevenRUP.step83762 (p 2839) (p 2870) (p 2881) (p 3367) (p 3585) (derived73428 p h) (derived62473 p h)

theorem derived83763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2881) ∨ (¬ p 2839) ∨ (¬ p 2137) ∨ (p 2737) :=
  ElevenRUP.step83763 (p 2137) (p 2737) (p 2743) (p 2839) (p 2881) (p 3051) (derived73298 p h) (derived48892 p h)

theorem derived83764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 4030) ∨ (¬ p 3051) ∨ (¬ p 2839) ∨ (¬ p 2881) ∨ (¬ p 4666) ∨ (p 2598) ∨ (p 2417) ∨ (p 2922) :=
  ElevenRUP.step83764 (p 2137) (p 2417) (p 2598) (p 2839) (p 2881) (p 2922) (p 2928) (p 3051) (p 3055) (p 4030) (p 4278) (p 4666) (p 4734) (derived73350 p h) (derived73546 p h) (derived73320 p h) (derived72735 p h) (derived50453 p h)

theorem derived83766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2737) ∨ (¬ p 2839) ∨ (¬ p 2696) ∨ (¬ p 3589) ∨ (¬ p 3988) :=
  ElevenRUP.step83766 (p 2619) (p 2696) (p 2737) (p 2743) (p 2839) (p 3589) (p 3988) (derived73298 p h) (derived47614 p h)

theorem derived83767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 2619) ∨ (¬ p 2459) ∨ (¬ p 4902) ∨ (¬ p 2608) ∨ (p 2528) ∨ (p 3389) ∨ (¬ p 5193) ∨ (¬ p 4186) :=
  ElevenRUP.step83767 (p 2459) (p 2528) (p 2534) (p 2608) (p 2619) (p 2839) (p 3389) (p 3540) (p 4186) (p 4902) (p 5193) (derived73268 p h) (derived73402 p h) (derived57838 p h)

theorem derived83769 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 4044) ∨ (¬ p 2241) ∨ (¬ p 2870) ∨ (¬ p 2839) ∨ (¬ p 4666) ∨ (¬ p 2750) ∨ (p 3449) ∨ (¬ p 2881) ∨ (¬ p 5074) :=
  ElevenRUP.step83769 (p 2241) (p 2449) (p 2750) (p 2839) (p 2870) (p 2881) (p 3449) (p 3860) (p 3947) (p 4044) (p 4666) (p 5074) (derived73494 p h) (derived73482 p h) (derived49028 p h)

theorem derived83770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2737) ∨ (¬ p 4204) ∨ (¬ p 2839) ∨ (p 2881) ∨ (¬ p 4988) ∨ (¬ p 2137) :=
  ElevenRUP.step83770 (p 2137) (p 2341) (p 2737) (p 2743) (p 2839) (p 2881) (p 3570) (p 4204) (p 4988) (derived73298 p h) (derived73418 p h) (derived45805 p h)

theorem derived83771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3246) ∨ (¬ p 2137) ∨ (¬ p 4988) ∨ (¬ p 2839) ∨ (p 2881) :=
  ElevenRUP.step83771 (p 2137) (p 2341) (p 2839) (p 2881) (p 3246) (p 3570) (p 4988) (derived73418 p h) (derived50467 p h)

theorem derived83773 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 2137) ∨ (¬ p 3212) ∨ (¬ p 3680) ∨ (¬ p 2839) :=
  ElevenRUP.step83773 (p 2137) (p 2761) (p 2839) (p 3212) (p 3680) (p 4381) (derived73574 p h) (derived56905 p h)

theorem derived83781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 3872) ∨ (¬ p 2881) ∨ (¬ p 2137) ∨ (p 2177) ∨ (¬ p 2156) :=
  ElevenRUP.step83781 (p 2137) (p 2156) (p 2177) (p 2299) (p 2839) (p 2881) (p 3872) (derived73234 p h) (derived53055 p h)

theorem derived83782 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2396) ∨ (¬ p 2563) ∨ (¬ p 2274) ∨ (¬ p 4882) ∨ (¬ p 2839) :=
  ElevenRUP.step83782 (p 2274) (p 2396) (p 2563) (p 2829) (p 2839) (p 3688) (p 4882) (derived73444 p h) (derived66907 p h)

theorem derived83786 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5660) ∨ (p 2132) ∨ (p 2707) ∨ (¬ p 4169) ∨ (¬ p 2839) ∨ (¬ p 3873) :=
  ElevenRUP.step83786 (p 2132) (p 2138) (p 2707) (p 2839) (p 3588) (p 3873) (p 4169) (p 5660) (derived73214 p h) (derived73430 p h) (derived45600 p h)

theorem derived83792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2137) ∨ (p 2427) ∨ (¬ p 2839) ∨ (p 3367) :=
  ElevenRUP.step83792 (p 2137) (p 2427) (p 2839) (p 3051) (p 3367) (p 3585) (p 4235) (derived73536 p h) (derived73428 p h) (derived46678 p h)

theorem derived83793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 3367) ∨ (p 2427) ∨ (¬ p 2870) :=
  ElevenRUP.step83793 (p 2427) (p 2839) (p 2870) (p 3367) (p 3585) (p 4235) (derived73428 p h) (derived73536 p h) (derived62409 p h)

theorem derived83794 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2839) ∨ (¬ p 2741) ∨ (¬ p 2651) ∨ (¬ p 2811) ∨ (¬ p 5052) :=
  ElevenRUP.step83794 (p 2651) (p 2727) (p 2741) (p 2811) (p 2839) (p 4111) (p 5052) (derived73518 p h) (derived49595 p h)

theorem derived83796 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2641) ∨ (p 2132) ∨ (¬ p 3873) ∨ (¬ p 2797) ∨ (¬ p 2741) :=
  ElevenRUP.step83796 (p 2132) (p 2138) (p 2641) (p 2741) (p 2797) (p 2839) (p 3873) (p 4154) (derived73526 p h) (derived73214 p h) (derived46259 p h)

theorem derived83798 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2608) ∨ (¬ p 2742) ∨ (¬ p 2839) ∨ (¬ p 5052) :=
  ElevenRUP.step83798 (p 2241) (p 2247) (p 2608) (p 2742) (p 2839) (p 5052) (derived73226 p h) (derived50168 p h)

theorem derived83807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 4030) ∨ (p 2528) ∨ (¬ p 2509) ∨ (¬ p 3950) ∨ (¬ p 2839) ∨ (¬ p 3051) ∨ (p 2598) ∨ (¬ p 2137) :=
  ElevenRUP.step83807 (p 2137) (p 2509) (p 2528) (p 2534) (p 2598) (p 2839) (p 3051) (p 3055) (p 3246) (p 3950) (p 4030) (p 4734) (derived73268 p h) (derived72735 p h) (derived73350 p h) (derived51947 p h)

theorem derived83809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4030) ∨ (¬ p 4149) ∨ (¬ p 2577) ∨ (¬ p 5580) ∨ (¬ p 4752) ∨ (p 2307) ∨ (¬ p 3955) ∨ (¬ p 3366) ∨ (¬ p 2619) ∨ (¬ p 3347) ∨ (¬ p 2839) ∨ (p 2696) ∨ (¬ p 4434) :=
  ElevenRUP.step83809 (p 2307) (p 2313) (p 2577) (p 2619) (p 2696) (p 2839) (p 3347) (p 3365) (p 3366) (p 3955) (p 4030) (p 4149) (p 4434) (p 4752) (p 5580) (derived73238 p h) (derived73390 p h) (derived62202 p h)

theorem derived83813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3953) ∨ (¬ p 2122) ∨ (¬ p 5052) ∨ (¬ p 4426) ∨ (p 3309) ∨ (¬ p 2839) :=
  ElevenRUP.step83813 (p 2122) (p 2839) (p 3309) (p 3549) (p 3953) (p 4426) (p 5052) (derived73406 p h) (derived54882 p h)

theorem derived83815 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2187) ∨ (¬ p 2748) ∨ (¬ p 4133) ∨ (¬ p 2996) ∨ (¬ p 2156) ∨ (p 2696) ∨ (¬ p 2137) ∨ (¬ p 2839) :=
  ElevenRUP.step83815 (p 2137) (p 2156) (p 2187) (p 2264) (p 2696) (p 2748) (p 2839) (p 2996) (p 3365) (p 3553) (p 4133) (p 4734) (derived73410 p h) (derived72735 p h) (derived73390 p h) (derived57858 p h)

theorem derived83821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2839) ∨ (p 3367) ∨ (¬ p 2440) ∨ (¬ p 4753) :=
  ElevenRUP.step83821 (p 2440) (p 2839) (p 3367) (p 3585) (p 3695) (p 4753) (derived73428 p h) (derived48364 p h)

theorem derived83823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2109) ∨ (¬ p 3696) ∨ (¬ p 3156) ∨ (¬ p 2839) ∨ (p 3537) ∨ (¬ p 4906) :=
  ElevenRUP.step83823 (p 2109) (p 2839) (p 3156) (p 3537) (p 3696) (p 4242) (p 4906) (derived73538 p h) (derived42158 p h)

theorem derived83828 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2839) ∨ (¬ p 3475) ∨ (p 2493) ∨ (¬ p 5052) ∨ (¬ p 4257) ∨ (¬ p 3759) :=
  ElevenRUP.step83828 (p 2493) (p 2499) (p 2573) (p 2839) (p 3475) (p 3759) (p 4257) (p 5052) (derived73260 p h) (derived59731 p h)

theorem derived83829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2839) ∨ (¬ p 3475) ∨ (¬ p 5052) ∨ (¬ p 4257) ∨ (p 2922) :=
  ElevenRUP.step83829 (p 2839) (p 2922) (p 2928) (p 3201) (p 3475) (p 4257) (p 5052) (derived73320 p h) (derived52580 p h)

theorem derived83830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 5160) ∨ (¬ p 4949) ∨ (p 3367) ∨ (¬ p 3695) :=
  ElevenRUP.step83830 (p 2839) (p 3367) (p 3585) (p 3695) (p 4949) (p 5160) (derived73428 p h) (derived51423 p h)

theorem derived83831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (¬ p 2839) ∨ (¬ p 2563) ∨ (p 3367) ∨ (¬ p 2598) :=
  ElevenRUP.step83831 (p 2563) (p 2598) (p 2839) (p 3367) (p 3585) (p 3695) (derived73428 p h) (derived56765 p h)

theorem derived83834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 3367) ∨ (¬ p 2860) ∨ (¬ p 2598) :=
  ElevenRUP.step83834 (p 2598) (p 2839) (p 2860) (p 3367) (p 3585) (derived73428 p h) (derived45180 p h)

theorem derived83838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4400) ∨ (¬ p 2839) ∨ (¬ p 5201) ∨ (¬ p 2341) ∨ (p 3527) ∨ (¬ p 4884) ∨ (¬ p 3759) :=
  ElevenRUP.step83838 (p 2341) (p 2839) (p 3527) (p 3548) (p 3759) (p 4400) (p 4884) (p 5201) (derived73404 p h) (derived59434 p h)

theorem derived83839 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 3309) ∨ (¬ p 4884) ∨ (¬ p 2584) ∨ (¬ p 2839) ∨ (¬ p 3759) ∨ (¬ p 3953) :=
  ElevenRUP.step83839 (p 2307) (p 2584) (p 2839) (p 3309) (p 3549) (p 3759) (p 3953) (p 4884) (derived73406 p h) (derived49511 p h)

theorem derived83840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2839) ∨ (p 2901) ∨ (¬ p 3051) ∨ (p 2737) :=
  ElevenRUP.step83840 (p 2137) (p 2737) (p 2743) (p 2839) (p 2901) (p 3051) (p 4320) (derived73552 p h) (derived73298 p h) (derived52417 p h)

theorem derived83843 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3985) ∨ (p 2737) ∨ (¬ p 2177) ∨ (¬ p 2839) ∨ (¬ p 2122) :=
  ElevenRUP.step83843 (p 2122) (p 2177) (p 2737) (p 2743) (p 2839) (p 3985) (derived73298 p h) (derived45760 p h)

theorem derived83844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 2137) ∨ (p 2737) ∨ (¬ p 2220) ∨ (¬ p 2839) :=
  ElevenRUP.step83844 (p 2137) (p 2220) (p 2737) (p 2743) (p 2839) (p 3146) (derived73298 p h) (derived45802 p h)

theorem derived83851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2707) ∨ (¬ p 2137) ∨ (¬ p 4169) ∨ (¬ p 2156) ∨ (¬ p 4555) :=
  ElevenRUP.step83851 (p 2137) (p 2156) (p 2707) (p 2839) (p 3588) (p 4169) (p 4555) (derived73430 p h) (derived41436 p h)

theorem derived83854 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 4740) ∨ (¬ p 2839) ∨ (¬ p 2220) :=
  ElevenRUP.step83854 (p 2220) (p 2839) (p 3537) (p 4242) (p 4740) (derived73538 p h) (derived71570 p h)

theorem derived83857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3580) ∨ (¬ p 2630) ∨ (p 2685) :=
  ElevenRUP.step83857 (p 2630) (p 2685) (p 2810) (p 3572) (p 3580) (derived73315 p h) (derived73420 p h) (h 27583)

theorem derived83860 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 4976) :=
  ElevenRUP.step83860 (p 3016) (p 3574) (p 4976) (derived73422 p h) (derived46651 p h)

theorem derived83861 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 4975) :=
  ElevenRUP.step83861 (p 3016) (p 3574) (p 4975) (derived73422 p h) (derived48577 p h)

theorem derived83862 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 3016) ∨ (¬ p 2663) ∨ (¬ p 2573) :=
  ElevenRUP.step83862 (p 2573) (p 2663) (p 2946) (p 2952) (p 3016) (p 3574) (derived73330 p h) (derived73422 p h) (derived69645 p h)

theorem derived83865 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2881) ∨ (p 2352) ∨ (p 2651) ∨ (¬ p 4503) ∨ (¬ p 2210) ∨ (p 3016) ∨ (¬ p 2254) :=
  ElevenRUP.step83865 (p 2210) (p 2254) (p 2352) (p 2651) (p 2657) (p 2881) (p 2891) (p 3016) (p 3574) (p 3956) (p 4503) (derived73500 p h) (derived73288 p h) (derived73422 p h) (derived57972 p h)

theorem derived83869 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 3016) ∨ (p 2352) :=
  ElevenRUP.step83869 (p 2352) (p 2727) (p 2992) (p 3016) (p 3574) (p 3956) (p 4111) (derived73518 p h) (derived73422 p h) (derived73500 p h) (derived43753 p h)

theorem derived83870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 4116) ∨ (p 2352) ∨ (p 3016) :=
  ElevenRUP.step83870 (p 2241) (p 2352) (p 3016) (p 3379) (p 3452) (p 3574) (p 3956) (p 4116) (derived73394 p h) (derived73500 p h) (derived73422 p h) (derived65269 p h)

theorem derived83871 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2946) ∨ (p 3016) ∨ (¬ p 2493) :=
  ElevenRUP.step83871 (p 2493) (p 2651) (p 2657) (p 2946) (p 3016) (p 3574) (derived73288 p h) (derived73422 p h) (derived55101 p h)

theorem derived83874 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2946) ∨ (p 2651) ∨ (p 3016) :=
  ElevenRUP.step83874 (p 2651) (p 2657) (p 2946) (p 2992) (p 3016) (p 3574) (p 3662) (derived73440 p h) (derived73288 p h) (derived73422 p h) (derived45249 p h)

theorem derived83875 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3564) ∨ (p 3016) ∨ (p 2651) :=
  ElevenRUP.step83875 (p 2651) (p 2657) (p 3016) (p 3461) (p 3564) (p 3574) (p 4137) (p 4191) (derived73530 p h) (derived73524 p h) (derived73422 p h) (derived73288 p h) (derived64541 p h)

theorem derived83876 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2651) ∨ (p 2177) ∨ (p 2553) :=
  ElevenRUP.step83876 (p 2177) (p 2299) (p 2553) (p 2588) (p 2651) (p 2657) (p 3016) (p 3574) (derived73422 p h) (derived73288 p h) (derived73234 p h) (derived73282 p h) (derived66658 p h)

theorem derived83880 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3083) ∨ (p 2553) ∨ (p 2470) :=
  ElevenRUP.step83880 (p 2470) (p 2476) (p 2553) (p 2588) (p 3016) (p 3083) (p 3574) (derived73422 p h) (derived73282 p h) (derived73250 p h) (derived45318 p h)

theorem derived83881 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 2573) ∨ (¬ p 2663) :=
  ElevenRUP.step83881 (p 2528) (p 2573) (p 2663) (p 3016) (p 3083) (p 3574) (derived73422 p h) (derived45239 p h)

theorem derived83884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2663) ∨ (p 2440) ∨ (¬ p 2573) ∨ (¬ p 2373) ∨ (p 3016) :=
  ElevenRUP.step83884 (p 2373) (p 2440) (p 2542) (p 2573) (p 2663) (p 3016) (p 3574) (derived73270 p h) (derived73422 p h) (derived45977 p h)

theorem derived83885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3083) ∨ (p 2470) ∨ (¬ p 3093) ∨ (¬ p 4718) ∨ (¬ p 5193) ∨ (p 2274) ∨ (p 3016) :=
  ElevenRUP.step83885 (p 2274) (p 2470) (p 2476) (p 3016) (p 3083) (p 3093) (p 3097) (p 3309) (p 3574) (p 4718) (p 5193) (derived73250 p h) (derived73352 p h) (derived73422 p h) (derived56108 p h)

theorem derived83886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3564) ∨ (¬ p 3537) ∨ (¬ p 4604) ∨ (¬ p 2608) ∨ (p 3016) ∨ (p 2651) ∨ (¬ p 2254) :=
  ElevenRUP.step83886 (p 2254) (p 2608) (p 2651) (p 2657) (p 3016) (p 3537) (p 3564) (p 3574) (p 3609) (p 4137) (p 4604) (derived73524 p h) (derived73422 p h) (derived73288 p h) (derived59803 p h)

theorem derived83891 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2254) ∨ (p 3016) ∨ (¬ p 4556) ∨ (¬ p 3399) ∨ (p 2651) ∨ (p 2553) ∨ (p 2881) :=
  ElevenRUP.step83891 (p 2254) (p 2553) (p 2588) (p 2651) (p 2657) (p 2881) (p 3016) (p 3399) (p 3527) (p 3570) (p 3574) (p 4556) (derived73422 p h) (derived73288 p h) (derived73282 p h) (derived73418 p h) (derived53757 p h)

theorem derived83893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 2475) ∨ (¬ p 3923) ∨ (¬ p 3083) ∨ (p 3016) ∨ (¬ p 4113) ∨ (¬ p 3660) :=
  ElevenRUP.step83893 (p 2475) (p 3016) (p 3083) (p 3319) (p 3574) (p 3660) (p 3923) (p 4113) (derived73422 p h) (derived56177 p h)

theorem derived83894 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3083) ∨ (¬ p 4157) ∨ (p 2383) ∨ (¬ p 2581) :=
  ElevenRUP.step83894 (p 2383) (p 2387) (p 2581) (p 3016) (p 3083) (p 3574) (p 4157) (derived73422 p h) (derived73246 p h) (derived48867 p h)

theorem derived83896 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3083) ∨ (¬ p 5222) ∨ (¬ p 2475) ∨ (p 2819) ∨ (¬ p 4113) :=
  ElevenRUP.step83896 (p 2475) (p 2819) (p 3016) (p 3083) (p 3574) (p 4113) (p 4358) (p 5222) (derived73422 p h) (derived73564 p h) (derived61945 p h)

theorem derived83898 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2230) ∨ (p 3389) ∨ (p 3016) ∨ (p 2406) :=
  ElevenRUP.step83898 (p 2230) (p 2406) (p 2437) (p 3016) (p 3238) (p 3389) (p 3540) (p 3574) (derived73402 p h) (derived73422 p h) (derived73374 p h) (derived43485 p h)

theorem derived83899 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3083) ∨ (p 3016) ∨ (¬ p 2528) :=
  ElevenRUP.step83899 (p 2459) (p 2528) (p 3016) (p 3083) (p 3574) (p 4348) (derived73562 p h) (derived73422 p h) (derived53363 p h)

theorem derived83900 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2440) ∨ (¬ p 3660) :=
  ElevenRUP.step83900 (p 2440) (p 2542) (p 3016) (p 3574) (p 3660) (derived73422 p h) (derived73270 p h) (h 9576)

theorem derived83905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3660) ∨ (¬ p 2230) ∨ (¬ p 2656) ∨ (p 3016) :=
  ElevenRUP.step83905 (p 2230) (p 2656) (p 3016) (p 3574) (p 3660) (derived73422 p h) (h 19891)

theorem derived83908 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2437) ∨ (¬ p 3875) ∨ (p 3016) ∨ (¬ p 2528) :=
  ElevenRUP.step83908 (p 2437) (p 2459) (p 2528) (p 3016) (p 3574) (p 3875) (p 4348) (derived73562 p h) (derived73422 p h) (derived45444 p h)

theorem derived83911 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2440) ∨ (¬ p 3096) ∨ (¬ p 2427) ∨ (¬ p 4558) :=
  ElevenRUP.step83911 (p 2427) (p 2440) (p 2542) (p 3016) (p 3096) (p 3574) (p 4558) (derived73422 p h) (derived73270 p h) (derived62954 p h)

theorem derived83913 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (p 2295) ∨ (¬ p 4194) ∨ (p 3016) :=
  ElevenRUP.step83913 (p 2122) (p 2295) (p 2553) (p 2588) (p 3016) (p 3568) (p 3574) (p 4194) (derived73282 p h) (derived73416 p h) (derived73422 p h) (derived66872 p h)

theorem derived83914 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2651) ∨ (¬ p 2274) ∨ (p 2553) :=
  ElevenRUP.step83914 (p 2274) (p 2553) (p 2588) (p 2651) (p 2657) (p 3016) (p 3574) (derived73422 p h) (derived73288 p h) (derived73282 p h) (derived54261 p h)

theorem derived83916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (p 3016) ∨ (p 2307) ∨ (¬ p 4710) ∨ (¬ p 2581) :=
  ElevenRUP.step83916 (p 2307) (p 2313) (p 2437) (p 2581) (p 3016) (p 3574) (p 4710) (derived73422 p h) (derived73238 p h) (derived48559 p h)

theorem derived83917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (p 3016) ∨ (¬ p 4710) ∨ (¬ p 2573) ∨ (p 2274) :=
  ElevenRUP.step83917 (p 2274) (p 2437) (p 2573) (p 3016) (p 3097) (p 3574) (p 4710) (derived73422 p h) (derived73352 p h) (derived46891 p h)

theorem derived83918 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2727) ∨ (¬ p 2573) ∨ (p 2230) :=
  ElevenRUP.step83918 (p 2230) (p 2573) (p 2589) (p 2727) (p 3016) (p 3574) (p 4111) (derived73422 p h) (derived73518 p h) (derived73284 p h) (derived42989 p h)

theorem derived83922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 3016) ∨ (p 2427) ∨ (p 2230) :=
  ElevenRUP.step83922 (p 2230) (p 2427) (p 2573) (p 2589) (p 3016) (p 3574) (p 4235) (derived73422 p h) (derived73536 p h) (derived73284 p h) (derived45705 p h)

theorem derived83923 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (p 3016) ∨ (¬ p 2573) :=
  ElevenRUP.step83923 (p 2573) (p 2656) (p 3016) (p 3574) (derived73422 p h) (h 18996)

theorem derived83929 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (p 2417) ∨ (p 3016) ∨ (¬ p 2573) :=
  ElevenRUP.step83929 (p 2417) (p 2573) (p 3016) (p 3389) (p 3540) (p 3574) (p 4278) (derived73402 p h) (derived73546 p h) (derived73422 p h) (derived47613 p h)

theorem derived83930 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (p 3016) ∨ (p 2911) ∨ (¬ p 2573) :=
  ElevenRUP.step83930 (p 2573) (p 2911) (p 3016) (p 3389) (p 3540) (p 3574) (p 3644) (derived73402 p h) (derived73422 p h) (derived73434 p h) (derived47609 p h)

theorem derived83932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3346) ∨ (p 3016) ∨ (¬ p 2573) ∨ (p 3276) :=
  ElevenRUP.step83932 (p 2573) (p 3016) (p 3276) (p 3346) (p 3574) (p 4425) (derived73422 p h) (derived73578 p h) (derived53467 p h)

theorem derived83933 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (¬ p 4635) ∨ (p 3389) ∨ (¬ p 4949) ∨ (¬ p 2573) ∨ (p 3016) :=
  ElevenRUP.step83933 (p 2440) (p 2542) (p 2573) (p 3016) (p 3389) (p 3540) (p 3574) (p 4635) (p 4949) (derived73270 p h) (derived73402 p h) (derived73422 p h) (derived60477 p h)

theorem derived83934 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2437) ∨ (p 2230) ∨ (¬ p 2573) ∨ (¬ p 4646) :=
  ElevenRUP.step83934 (p 2230) (p 2437) (p 2573) (p 2589) (p 3016) (p 3574) (p 4646) (derived73422 p h) (derived73284 p h) (derived48254 p h)

theorem derived83937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3276) ∨ (¬ p 2663) ∨ (p 3016) ∨ (¬ p 2573) :=
  ElevenRUP.step83937 (p 2573) (p 2663) (p 3016) (p 3276) (p 3343) (p 3574) (derived73422 p h) (derived49126 p h)

theorem derived83938 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (p 3016) ∨ (¬ p 2573) ∨ (¬ p 3921) ∨ (p 2177) :=
  ElevenRUP.step83938 (p 2177) (p 2299) (p 2573) (p 3016) (p 3389) (p 3540) (p 3574) (p 3921) (derived73402 p h) (derived73422 p h) (derived73234 p h) (derived47610 p h)

theorem derived83941 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2220) ∨ (¬ p 2573) ∨ (¬ p 3904) ∨ (¬ p 2373) :=
  ElevenRUP.step83941 (p 2220) (p 2373) (p 2573) (p 3016) (p 3574) (p 3904) (p 4120) (derived73422 p h) (derived73522 p h) (derived45068 p h)

theorem derived83946 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2656) ∨ (¬ p 4718) ∨ (p 3016) ∨ (p 2187) :=
  ElevenRUP.step83946 (p 2187) (p 2470) (p 2656) (p 3016) (p 3574) (p 3989) (p 4718) (derived73422 p h) (derived73502 p h) (derived66851 p h)

theorem derived83947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4157) ∨ (¬ p 2470) ∨ (p 2553) ∨ (¬ p 4405) ∨ (¬ p 2656) ∨ (p 3016) :=
  ElevenRUP.step83947 (p 2470) (p 2553) (p 2588) (p 2656) (p 3016) (p 3574) (p 4157) (p 4405) (derived73282 p h) (derived73422 p h) (derived40991 p h)

theorem derived83948 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4399) ∨ (p 3016) ∨ (¬ p 4715) ∨ (p 2427) ∨ (¬ p 2656) :=
  ElevenRUP.step83948 (p 2427) (p 2656) (p 3016) (p 3051) (p 3574) (p 4235) (p 4399) (p 4715) (derived73422 p h) (derived73536 p h) (derived49679 p h)

theorem derived83949 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 3016) ∨ (¬ p 3096) ∨ (¬ p 5046) ∨ (¬ p 2982) :=
  ElevenRUP.step83949 (p 2440) (p 2542) (p 2982) (p 3016) (p 3096) (p 3574) (p 5046) (derived73270 p h) (derived73422 p h) (derived50990 p h)

theorem derived83952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2881) ∨ (p 3016) ∨ (p 2440) ∨ (¬ p 3096) :=
  ElevenRUP.step83952 (p 2427) (p 2440) (p 2542) (p 2881) (p 3016) (p 3096) (p 3574) (derived73422 p h) (derived73270 p h) (derived63405 p h)

theorem derived83954 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 3654) ∨ (¬ p 4753) ∨ (¬ p 3483) ∨ (¬ p 4375) ∨ (¬ p 2386) :=
  ElevenRUP.step83954 (p 2386) (p 3016) (p 3483) (p 3574) (p 3654) (p 3946) (p 4375) (p 4753) (derived73422 p h) (derived73492 p h) (derived42368 p h)

theorem derived83956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2274) ∨ (¬ p 2951) ∨ (¬ p 2962) ∨ (¬ p 3136) ∨ (p 2187) :=
  ElevenRUP.step83956 (p 2187) (p 2274) (p 2383) (p 2951) (p 2962) (p 3136) (p 3989) (derived73502 p h) (derived47174 p h)

theorem derived83957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2307) ∨ (¬ p 3955) :=
  ElevenRUP.step83957 (p 2307) (p 2313) (p 2383) (p 3955) (derived73238 p h) (h 19973)

theorem derived83960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3016) ∨ (¬ p 2665) ∨ (p 2352) ∨ (¬ p 2584) :=
  ElevenRUP.step83960 (p 2352) (p 2383) (p 2584) (p 2665) (p 3016) (p 3574) (p 3956) (derived73422 p h) (derived73500 p h) (derived48290 p h)

theorem derived83963 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3550) ∨ (p 2307) ∨ (¬ p 4556) ∨ (p 2881) :=
  ElevenRUP.step83963 (p 2307) (p 2313) (p 2383) (p 2881) (p 3550) (p 3570) (p 4556) (derived73238 p h) (derived73418 p h) (derived52564 p h)

theorem derived83965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3146) ∨ (¬ p 2363) ∨ (¬ p 3988) ∨ (¬ p 4489) :=
  ElevenRUP.step83965 (p 2363) (p 2383) (p 3146) (p 3692) (p 3988) (p 4489) (derived73448 p h) (derived49455 p h)

theorem derived83966 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 2383) ∨ (¬ p 4078) ∨ (¬ p 2788) ∨ (¬ p 2363) :=
  ElevenRUP.step83966 (p 2363) (p 2383) (p 2788) (p 3609) (p 4078) (p 4340) (derived73558 p h) (derived49368 p h)

theorem derived83969 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2727) ∨ (¬ p 3567) ∨ (¬ p 2641) ∨ (p 2352) :=
  ElevenRUP.step83969 (p 2352) (p 2383) (p 2641) (p 2727) (p 3567) (p 3956) (p 4111) (derived73518 p h) (derived73500 p h) (derived46366 p h)

theorem derived83971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3567) ∨ (¬ p 2553) ∨ (p 2352) ∨ (¬ p 2641) :=
  ElevenRUP.step83971 (p 2352) (p 2383) (p 2553) (p 2641) (p 3567) (p 3956) (derived73500 p h) (derived52061 p h)

theorem derived83973 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3422) ∨ (¬ p 2584) ∨ (p 2352) ∨ (¬ p 4730) :=
  ElevenRUP.step83973 (p 2352) (p 2383) (p 2584) (p 3422) (p 3584) (p 3956) (p 4730) (derived73426 p h) (derived73500 p h) (derived53571 p h)

theorem derived83974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2383) ∨ (p 2307) ∨ (p 2352) ∨ (¬ p 4976) :=
  ElevenRUP.step83974 (p 2295) (p 2307) (p 2313) (p 2352) (p 2383) (p 3956) (p 4976) (derived73238 p h) (derived73500 p h) (derived55873 p h)

theorem derived83979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 2685) ∨ (¬ p 2781) ∨ (¬ p 4621) ∨ (p 2352) ∨ (¬ p 2383) ∨ (p 2696) ∨ (p 2449) :=
  ElevenRUP.step83979 (p 2352) (p 2383) (p 2449) (p 2685) (p 2696) (p 2781) (p 3365) (p 3564) (p 3572) (p 3947) (p 3956) (p 4621) (derived73420 p h) (derived73500 p h) (derived73390 p h) (derived73494 p h) (derived51075 p h)

theorem derived83982 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 2132) ∨ (¬ p 2383) ∨ (p 2870) ∨ (¬ p 4621) ∨ (¬ p 2781) ∨ (p 2352) ∨ (p 3246) :=
  ElevenRUP.step83982 (p 2132) (p 2138) (p 2352) (p 2383) (p 2781) (p 2870) (p 3246) (p 3564) (p 3690) (p 3956) (p 4244) (p 4621) (derived73214 p h) (derived73540 p h) (derived73500 p h) (derived73446 p h) (derived59776 p h)

theorem derived83987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 2383) ∨ (¬ p 3759) ∨ (p 2352) ∨ (¬ p 2553) ∨ (¬ p 2584) :=
  ElevenRUP.step83987 (p 2352) (p 2383) (p 2553) (p 2584) (p 3367) (p 3759) (p 3956) (derived73500 p h) (derived48951 p h)

theorem derived83990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3083) ∨ (¬ p 4432) ∨ (¬ p 2586) ∨ (¬ p 3016) :=
  ElevenRUP.step83990 (p 2383) (p 2586) (p 3016) (p 3083) (p 4256) (p 4432) (derived73542 p h) (derived54424 p h)

theorem derived83994 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3550) ∨ (¬ p 2383) ∨ (¬ p 4276) ∨ (p 2307) ∨ (p 2911) :=
  ElevenRUP.step83994 (p 2307) (p 2313) (p 2383) (p 2911) (p 3550) (p 3644) (p 4276) (derived73238 p h) (derived73434 p h) (derived41711 p h)

theorem derived83995 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3987) ∨ (¬ p 4786) ∨ (¬ p 5503) ∨ (¬ p 2363) ∨ (¬ p 4831) ∨ (¬ p 3266) ∨ (¬ p 2383) ∨ (p 2598) :=
  ElevenRUP.step83995 (p 2363) (p 2383) (p 2598) (p 3055) (p 3201) (p 3266) (p 3876) (p 3987) (p 4786) (p 4831) (p 5503) (derived73486 p h) (derived73350 p h) (derived54627 p h)

theorem derived84002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2427) ∨ (¬ p 2962) ∨ (¬ p 4539) ∨ (¬ p 3872) ∨ (p 2187) :=
  ElevenRUP.step84002 (p 2187) (p 2383) (p 2427) (p 2962) (p 3872) (p 3989) (p 4235) (p 4539) (derived73536 p h) (derived73502 p h) (derived50852 p h)

theorem derived84009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3019) ∨ (¬ p 2590) ∨ (¬ p 2427) ∨ (p 2352) ∨ (¬ p 2727) ∨ (¬ p 3567) :=
  ElevenRUP.step84009 (p 2352) (p 2383) (p 2427) (p 2590) (p 2727) (p 3019) (p 3567) (p 3956) (derived73500 p h) (derived64623 p h)

theorem derived84014 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2850) ∨ (¬ p 2781) ∨ (¬ p 4905) ∨ (p 2598) ∨ (p 2373) ∨ (¬ p 2363) ∨ (¬ p 2383) :=
  ElevenRUP.step84014 (p 2363) (p 2373) (p 2383) (p 2459) (p 2598) (p 2781) (p 2850) (p 3055) (p 3684) (p 3880) (p 4348) (p 4905) (derived73562 p h) (derived73442 p h) (derived73350 p h) (derived73490 p h) (derived61767 p h)

theorem derived84024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2573) ∨ (¬ p 3987) ∨ (¬ p 3905) ∨ (¬ p 4786) ∨ (p 2352) :=
  ElevenRUP.step84024 (p 2352) (p 2383) (p 2573) (p 2579) (p 3905) (p 3956) (p 3987) (p 4786) (derived73274 p h) (derived73500 p h) (derived59399 p h)

theorem derived84030 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3125) ∨ (¬ p 2383) ∨ (p 2274) :=
  ElevenRUP.step84030 (p 2274) (p 2383) (p 3097) (p 3125) (p 3654) (p 3946) (derived73492 p h) (derived73352 p h) (derived44486 p h)

theorem derived84032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 2383) ∨ (p 3654) ∨ (p 2553) :=
  ElevenRUP.step84032 (p 2383) (p 2553) (p 2588) (p 3564) (p 3654) (p 3946) (derived73492 p h) (derived73282 p h) (derived44480 p h)

theorem derived84033 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 5123) :=
  ElevenRUP.step84033 (p 3707) (p 4321) (p 5123) (derived73554 p h) (derived61994 p h)

theorem derived84034 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3830) ∨ (¬ p 2248) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 3461) ∨ (¬ p 4625) :=
  ElevenRUP.step84034 (p 2248) (p 2417) (p 2437) (p 2651) (p 3461) (p 3707) (p 3830) (p 3834) (p 4321) (p 4625) (derived73554 p h) (derived73474 p h) (derived63805 p h)

theorem derived84036 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3440) ∨ (¬ p 3266) ∨ (¬ p 2459) ∨ (¬ p 4832) :=
  ElevenRUP.step84036 (p 2459) (p 3266) (p 3440) (p 3707) (p 4321) (p 4832) (derived73554 p h) (derived48438 p h)

theorem derived84038 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3941) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 5119) ∨ (¬ p 3519) ∨ (¬ p 2608) ∨ (p 3830) ∨ (¬ p 4376) :=
  ElevenRUP.step84038 (p 2608) (p 2911) (p 3389) (p 3519) (p 3707) (p 3830) (p 3834) (p 3941) (p 4321) (p 4376) (p 5119) (derived73554 p h) (derived73474 p h) (derived42451 p h)

theorem derived84048 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3449) ∨ (¬ p 3379) ∨ (¬ p 3266) ∨ (¬ p 3440) :=
  ElevenRUP.step84048 (p 3266) (p 3379) (p 3440) (p 3449) (p 3707) (p 3860) (p 4321) (derived73554 p h) (derived73482 p h) (derived47708 p h)

theorem derived84049 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3449) ∨ (¬ p 3266) ∨ (¬ p 2608) ∨ (¬ p 3440) :=
  ElevenRUP.step84049 (p 2608) (p 3266) (p 3440) (p 3449) (p 3707) (p 3860) (p 4321) (derived73554 p h) (derived73482 p h) (derived44870 p h)

theorem derived84050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (p 3449) ∨ (p 3707) ∨ (¬ p 4330) ∨ (¬ p 2651) ∨ (¬ p 3564) ∨ (¬ p 3016) ∨ (¬ p 3440) ∨ (¬ p 2248) :=
  ElevenRUP.step84050 (p 2248) (p 2651) (p 3016) (p 3266) (p 3440) (p 3449) (p 3564) (p 3707) (p 3860) (p 4321) (p 4330) (derived73482 p h) (derived73554 p h) (derived48997 p h)

theorem derived84052 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3266) ∨ (¬ p 4433) ∨ (¬ p 4335) ∨ (¬ p 4387) ∨ (¬ p 2363) :=
  ElevenRUP.step84052 (p 2363) (p 3266) (p 3707) (p 4321) (p 4335) (p 4387) (p 4433) (derived73554 p h) (derived48236 p h)

theorem derived84053 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (p 3830) ∨ (¬ p 2241) ∨ (¬ p 3266) :=
  ElevenRUP.step84053 (p 2241) (p 3266) (p 3707) (p 3830) (p 3834) (p 4321) (derived73554 p h) (derived73474 p h) (derived65011 p h)

theorem derived84055 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3266) ∨ (¬ p 4352) :=
  ElevenRUP.step84055 (p 3266) (p 3707) (p 4321) (p 4352) (derived73554 p h) (h 19940)

theorem derived84056 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3266) ∨ (p 3115) ∨ (¬ p 4387) ∨ (¬ p 2901) :=
  ElevenRUP.step84056 (p 2901) (p 3115) (p 3266) (p 3707) (p 4208) (p 4321) (p 4387) (derived73554 p h) (derived73534 p h) (derived46645 p h)

theorem derived84057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5357) ∨ (p 3707) ∨ (¬ p 2396) ∨ (¬ p 2761) ∨ (¬ p 5142) :=
  ElevenRUP.step84057 (p 2396) (p 2761) (p 3707) (p 4321) (p 5142) (p 5357) (derived73554 p h) (derived53183 p h)

theorem derived84060 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3767) ∨ (¬ p 4430) ∨ (¬ p 4516) ∨ (¬ p 3960) ∨ (¬ p 2177) ∨ (p 2563) ∨ (¬ p 4461) :=
  ElevenRUP.step84060 (p 2177) (p 2563) (p 3707) (p 3767) (p 3960) (p 4110) (p 4321) (p 4430) (p 4461) (p 4516) (derived73554 p h) (derived73516 p h) (derived52220 p h)

theorem derived84076 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3125) ∨ (¬ p 2132) ∨ (p 2459) ∨ (¬ p 2860) ∨ (p 3389) ∨ (¬ p 4330) ∨ (¬ p 4729) :=
  ElevenRUP.step84076 (p 2132) (p 2459) (p 2860) (p 2911) (p 3125) (p 3389) (p 3540) (p 3644) (p 4330) (p 4348) (p 4729) (derived73434 p h) (derived73562 p h) (derived73402 p h) (derived50773 p h)

theorem derived84077 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 3201) ∨ (¬ p 2284) ∨ (¬ p 4621) ∨ (p 2598) ∨ (¬ p 3125) ∨ (¬ p 2946) ∨ (¬ p 4786) :=
  ElevenRUP.step84077 (p 2284) (p 2417) (p 2598) (p 2946) (p 3055) (p 3125) (p 3201) (p 3876) (p 4278) (p 4621) (p 4786) (derived73546 p h) (derived73486 p h) (derived73350 p h) (derived56722 p h)

theorem derived84078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2528) ∨ (p 2598) ∨ (¬ p 2210) ∨ (¬ p 4736) ∨ (¬ p 2192) ∨ (¬ p 4330) ∨ (p 3641) :=
  ElevenRUP.step84078 (p 2192) (p 2210) (p 2528) (p 2534) (p 2598) (p 3055) (p 3125) (p 3641) (p 3874) (p 4330) (p 4736) (derived73268 p h) (derived73350 p h) (derived73484 p h) (derived51447 p h)

theorem derived84082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 4624) ∨ (p 2241) ∨ (¬ p 5190) ∨ (¬ p 2563) ∨ (¬ p 2230) ∨ (p 2641) ∨ (p 2295) :=
  ElevenRUP.step84082 (p 2230) (p 2241) (p 2247) (p 2295) (p 2563) (p 2641) (p 3125) (p 3568) (p 4154) (p 4624) (p 5190) (derived73226 p h) (derived73526 p h) (derived73416 p h) (derived64303 p h)

theorem derived84083 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 4623) ∨ (¬ p 3125) ∨ (p 2274) ∨ (¬ p 4276) :=
  ElevenRUP.step84083 (p 2274) (p 2417) (p 3097) (p 3125) (p 4276) (p 4278) (p 4623) (derived73546 p h) (derived73352 p h) (derived41704 p h)

theorem derived84084 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3402) ∨ (p 2493) ∨ (¬ p 3125) ∨ (p 2274) :=
  ElevenRUP.step84084 (p 2274) (p 2493) (p 2499) (p 3097) (p 3125) (p 3402) (p 3564) (p 4137) (derived73524 p h) (derived73260 p h) (derived73352 p h) (derived54055 p h)

theorem derived84090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2717) ∨ (¬ p 3425) ∨ (¬ p 4330) ∨ (¬ p 2284) ∨ (¬ p 2946) ∨ (¬ p 4786) ∨ (p 2459) :=
  ElevenRUP.step84090 (p 2284) (p 2459) (p 2717) (p 2946) (p 3125) (p 3425) (p 3659) (p 4330) (p 4348) (p 4786) (derived73438 p h) (derived73562 p h) (derived42352 p h)

theorem derived84091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3564) ∨ (¬ p 2284) ∨ (¬ p 2373) ∨ (¬ p 2590) :=
  ElevenRUP.step84091 (p 2284) (p 2373) (p 2590) (p 3125) (p 3564) (p 4137) (derived73524 p h) (derived46313 p h)

theorem derived84095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4623) ∨ (¬ p 3125) ∨ (¬ p 4204) ∨ (p 3246) :=
  ElevenRUP.step84095 (p 3125) (p 3246) (p 3690) (p 4204) (p 4623) (derived73446 p h) (h 20595)

theorem derived84099 (p : Nat → Prop) (h : Inputs p) :
    (p 3319) ∨ (¬ p 3125) ∨ (¬ p 4629) ∨ (¬ p 4512) ∨ (¬ p 2563) :=
  ElevenRUP.step84099 (p 2563) (p 3125) (p 3319) (p 4026) (p 4512) (p 4629) (derived73504 p h) (derived41115 p h)

theorem derived84101 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 3256) ∨ (¬ p 2230) ∨ (¬ p 4419) ∨ (¬ p 3125) ∨ (¬ p 2563) ∨ (¬ p 4330) ∨ (p 2696) :=
  ElevenRUP.step84101 (p 2230) (p 2563) (p 2696) (p 3005) (p 3125) (p 3256) (p 3365) (p 3877) (p 4118) (p 4330) (p 4419) (derived73488 p h) (derived73520 p h) (derived73390 p h) (derived53994 p h)

theorem derived84105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3125) ∨ (p 2881) ∨ (¬ p 2312) ∨ (¬ p 4624) ∨ (¬ p 4204) :=
  ElevenRUP.step84105 (p 2312) (p 2341) (p 2881) (p 3125) (p 3570) (p 4204) (p 4624) (derived73418 p h) (derived58842 p h)

theorem derived84110 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3125) ∨ (¬ p 2946) ∨ (¬ p 2248) ∨ (p 3399) ∨ (¬ p 2284) ∨ (¬ p 4330) ∨ (p 2459) :=
  ElevenRUP.step84110 (p 2248) (p 2284) (p 2459) (p 2946) (p 3125) (p 3399) (p 3527) (p 3548) (p 4330) (p 4348) (p 4366) (derived73404 p h) (derived73570 p h) (derived73562 p h) (derived62207 p h)

theorem derived84116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2241) ∨ (¬ p 2210) ∨ (¬ p 2284) ∨ (¬ p 4282) :=
  ElevenRUP.step84116 (p 2210) (p 2241) (p 2247) (p 2284) (p 3125) (p 4282) (derived73226 p h) (derived43232 p h)

theorem derived84123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4621) ∨ (¬ p 3125) ∨ (p 2417) ∨ (p 2437) ∨ (¬ p 2254) ∨ (¬ p 2192) ∨ (p 2651) ∨ (¬ p 2210) :=
  ElevenRUP.step84123 (p 2192) (p 2210) (p 2254) (p 2417) (p 2437) (p 2651) (p 2657) (p 3125) (p 3742) (p 4278) (p 4621) (derived73546 p h) (derived73452 p h) (derived73288 p h) (derived59859 p h)

theorem derived84126 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3461) ∨ (p 2274) ∨ (¬ p 3125) :=
  ElevenRUP.step84126 (p 2274) (p 2761) (p 3097) (p 3125) (p 3461) (p 4381) (derived73574 p h) (derived73352 p h) (derived65143 p h)

theorem derived84129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 4149) ∨ (¬ p 3125) ∨ (p 2187) :=
  ElevenRUP.step84129 (p 2187) (p 3125) (p 3989) (p 4149) (p 5580) (derived73502 p h) (derived44694 p h)

theorem derived84134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3564) ∨ (¬ p 2498) :=
  ElevenRUP.step84134 (p 2498) (p 3319) (p 3564) (p 4137) (derived73524 p h) (h 21224)

theorem derived84138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2608) ∨ (p 3323) ∨ (¬ p 3093) :=
  ElevenRUP.step84138 (p 2608) (p 3093) (p 3319) (p 3323) (p 3954) (p 4037) (derived73498 p h) (derived73508 p h) (derived44461 p h)

theorem derived84139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2341) ∨ (¬ p 4624) ∨ (¬ p 3204) ∨ (¬ p 2311) ∨ (¬ p 2177) :=
  ElevenRUP.step84139 (p 2177) (p 2311) (p 2341) (p 3204) (p 3319) (p 3551) (p 4624) (derived73408 p h) (derived50261 p h)

theorem derived84142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3323) ∨ (¬ p 4194) ∨ (¬ p 2498) ∨ (¬ p 3422) ∨ (¬ p 4753) :=
  ElevenRUP.step84142 (p 2498) (p 3319) (p 3323) (p 3422) (p 4037) (p 4194) (p 4753) (derived73508 p h) (derived41857 p h)

theorem derived84143 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3323) ∨ (¬ p 4975) ∨ (p 2727) ∨ (¬ p 4759) :=
  ElevenRUP.step84143 (p 2727) (p 3319) (p 3323) (p 4037) (p 4111) (p 4759) (p 4975) (derived73508 p h) (derived73518 p h) (derived51276 p h)

theorem derived84145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 2319) ∨ (p 2177) ∨ (p 3654) ∨ (¬ p 2341) :=
  ElevenRUP.step84145 (p 2177) (p 2299) (p 2319) (p 2341) (p 3319) (p 3654) (p 3946) (derived73234 p h) (derived73492 p h) (derived61842 p h)

theorem derived84147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3125) ∨ (¬ p 3093) ∨ (¬ p 2274) :=
  ElevenRUP.step84147 (p 2274) (p 3093) (p 3125) (p 3319) (p 3744) (derived73454 p h) (derived45827 p h)

theorem derived84149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3461) ∨ (¬ p 3319) ∨ (¬ p 5123) ∨ (¬ p 3093) ∨ (p 2619) ∨ (¬ p 4736) ∨ (p 2132) :=
  ElevenRUP.step84149 (p 2132) (p 2138) (p 2619) (p 3093) (p 3319) (p 3461) (p 3694) (p 4736) (p 5123) (p 5568) (derived73450 p h) (derived73214 p h) (derived60232 p h)

theorem derived84152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3564) ∨ (¬ p 2553) ∨ (¬ p 3093) :=
  ElevenRUP.step84152 (p 2553) (p 3093) (p 3319) (p 3564) (p 4137) (derived73524 p h) (derived58546 p h)

theorem derived84156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2608) ∨ (¬ p 3904) ∨ (p 2881) ∨ (¬ p 4330) ∨ (p 2459) ∨ (¬ p 3093) ∨ (¬ p 3347) ∨ (p 3051) :=
  ElevenRUP.step84156 (p 2459) (p 2608) (p 2881) (p 3051) (p 3093) (p 3319) (p 3347) (p 3556) (p 3570) (p 3904) (p 3954) (p 4330) (p 4348) (derived73498 p h) (derived73418 p h) (derived73562 p h) (derived73414 p h) (derived71574 p h)

theorem derived84157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3319) ∨ (¬ p 4105) ∨ (¬ p 4624) ∨ (p 3527) ∨ (¬ p 2312) :=
  ElevenRUP.step84157 (p 2312) (p 2341) (p 3319) (p 3527) (p 3548) (p 4105) (p 4624) (derived73404 p h) (derived51611 p h)

theorem derived84163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4319) ∨ (¬ p 3319) ∨ (¬ p 4717) ∨ (¬ p 2440) ∨ (¬ p 3019) ∨ (p 3564) :=
  ElevenRUP.step84163 (p 2440) (p 3019) (p 3319) (p 3564) (p 4137) (p 4319) (p 4717) (derived73524 p h) (derived41657 p h)

theorem derived84165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2992) ∨ (p 3323) ∨ (¬ p 4759) ∨ (¬ p 4566) :=
  ElevenRUP.step84165 (p 2992) (p 3319) (p 3323) (p 3662) (p 4037) (p 4566) (p 4759) (derived73440 p h) (derived73508 p h) (derived41492 p h)

theorem derived84170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2608) ∨ (p 2459) ∨ (p 2807) ∨ (¬ p 3093) ∨ (¬ p 2750) ∨ (¬ p 2252) ∨ (¬ p 4330) ∨ (p 2264) :=
  ElevenRUP.step84170 (p 2252) (p 2264) (p 2459) (p 2608) (p 2750) (p 2807) (p 3093) (p 3319) (p 3414) (p 3553) (p 3954) (p 4330) (p 4348) (derived73498 p h) (derived73562 p h) (derived73392 p h) (derived73410 p h) (derived41817 p h)

theorem derived84173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5379) ∨ (¬ p 5299) ∨ (¬ p 3319) ∨ (p 2553) ∨ (¬ p 4556) ∨ (¬ p 2498) ∨ (p 3246) :=
  ElevenRUP.step84173 (p 2498) (p 2553) (p 2588) (p 3246) (p 3319) (p 3690) (p 4556) (p 5299) (p 5379) (derived73282 p h) (derived73446 p h) (derived52438 p h)

theorem derived84175 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3319) ∨ (¬ p 3347) ∨ (p 2373) ∨ (¬ p 3093) ∨ (¬ p 4330) ∨ (p 3146) ∨ (p 2230) :=
  ElevenRUP.step84175 (p 2230) (p 2373) (p 2589) (p 2608) (p 3093) (p 3146) (p 3319) (p 3347) (p 3692) (p 3880) (p 3954) (p 4330) (derived73498 p h) (derived73490 p h) (derived73448 p h) (derived73284 p h) (derived71575 p h)

theorem derived84176 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3319) ∨ (¬ p 3093) ∨ (¬ p 2352) :=
  ElevenRUP.step84176 (p 2352) (p 3093) (p 3319) (p 3564) (p 4137) (derived73524 p h) (derived46554 p h)

theorem derived84180 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3564) ∨ (p 2573) ∨ (¬ p 3923) :=
  ElevenRUP.step84180 (p 2573) (p 2579) (p 3319) (p 3564) (p 3923) (p 4137) (derived73524 p h) (derived73274 p h) (derived44687 p h)

theorem derived84183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3654) ∨ (p 3527) ∨ (¬ p 2177) ∨ (¬ p 4105) :=
  ElevenRUP.step84183 (p 2177) (p 3319) (p 3527) (p 3548) (p 3654) (p 3946) (p 4105) (derived73492 p h) (derived73404 p h) (derived45173 p h)

theorem derived84184 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3093) ∨ (¬ p 3319) :=
  ElevenRUP.step84184 (p 3093) (p 3266) (p 3319) (p 3461) (p 4444) (derived73580 p h) (derived43507 p h)

theorem derived84185 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 2761) ∨ (p 3309) ∨ (¬ p 3319) :=
  ElevenRUP.step84185 (p 2761) (p 3309) (p 3319) (p 3461) (p 3549) (p 4381) (derived73574 p h) (derived73406 p h) (derived46772 p h)

theorem derived84187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 2761) ∨ (¬ p 3319) ∨ (¬ p 2498) ∨ (p 2352) :=
  ElevenRUP.step84187 (p 2352) (p 2498) (p 2761) (p 3319) (p 3461) (p 3956) (p 4381) (derived73574 p h) (derived73500 p h) (derived56575 p h)

theorem derived84188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3266) ∨ (¬ p 4697) ∨ (p 2696) ∨ (¬ p 3366) ∨ (¬ p 3461) ∨ (p 3343) ∨ (¬ p 4866) ∨ (p 3136) ∨ (¬ p 3413) :=
  ElevenRUP.step84188 (p 2696) (p 3136) (p 3266) (p 3319) (p 3343) (p 3359) (p 3365) (p 3366) (p 3413) (p 3461) (p 4315) (p 4444) (p 4697) (p 4866) (derived73580 p h) (derived73390 p h) (derived73388 p h) (derived73550 p h) (derived60031 p h)

theorem derived84191 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2241) ∨ (¬ p 2744) ∨ (p 2598) ∨ (¬ p 4624) ∨ (p 3422) ∨ (¬ p 3366) ∨ (¬ p 3093) ∨ (p 2553) :=
  ElevenRUP.step84191 (p 2241) (p 2247) (p 2553) (p 2588) (p 2598) (p 2744) (p 3055) (p 3093) (p 3319) (p 3366) (p 3422) (p 3584) (p 4624) (derived73226 p h) (derived73350 p h) (derived73426 p h) (derived73282 p h) (derived53880 p h)

theorem derived84192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 2241) ∨ (p 3125) ∨ (¬ p 3093) :=
  ElevenRUP.step84192 (p 2241) (p 2247) (p 3093) (p 3125) (p 3319) (p 3744) (derived73226 p h) (derived73454 p h) (derived46454 p h)

theorem derived84193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 3905) ∨ (¬ p 3093) ∨ (p 2459) ∨ (¬ p 4330) ∨ (p 2241) ∨ (p 3389) ∨ (¬ p 2744) ∨ (p 2911) ∨ (¬ p 3366) :=
  ElevenRUP.step84193 (p 2241) (p 2247) (p 2459) (p 2744) (p 2911) (p 3093) (p 3319) (p 3366) (p 3389) (p 3540) (p 3644) (p 3905) (p 4330) (p 4348) (derived73562 p h) (derived73226 p h) (derived73402 p h) (derived73434 p h) (derived64233 p h)

theorem derived84196 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 4623) ∨ (¬ p 3319) ∨ (¬ p 2761) ∨ (¬ p 3923) :=
  ElevenRUP.step84196 (p 2761) (p 3266) (p 3319) (p 3923) (p 4444) (p 4623) (derived73580 p h) (derived52439 p h)

theorem derived84197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 5015) ∨ (¬ p 2608) ∨ (p 3654) ∨ (p 3309) :=
  ElevenRUP.step84197 (p 2608) (p 3309) (p 3319) (p 3549) (p 3654) (p 3946) (p 5015) (derived73492 p h) (derived73406 p h) (derived58938 p h)

theorem derived84201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 4503) ∨ (¬ p 4345) ∨ (¬ p 3923) ∨ (p 2459) :=
  ElevenRUP.step84201 (p 2459) (p 3319) (p 3923) (p 4345) (p 4348) (p 4503) (derived73562 p h) (derived54363 p h)

theorem derived84203 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 3319) ∨ (¬ p 4623) ∨ (p 2307) ∨ (¬ p 2274) ∨ (¬ p 3204) ∨ (¬ p 2264) :=
  ElevenRUP.step84203 (p 2264) (p 2274) (p 2307) (p 2313) (p 2449) (p 3204) (p 3319) (p 3947) (p 4623) (derived73494 p h) (derived73238 p h) (derived43423 p h)

theorem derived84204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3323) ∨ (¬ p 4715) ∨ (¬ p 2498) ∨ (p 2440) ∨ (¬ p 4194) :=
  ElevenRUP.step84204 (p 2440) (p 2498) (p 2542) (p 3319) (p 3323) (p 4037) (p 4194) (p 4715) (derived73508 p h) (derived73270 p h) (derived60753 p h)

theorem derived84205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3286) ∨ (¬ p 5171) ∨ (¬ p 4319) ∨ (¬ p 5325) ∨ (¬ p 2331) :=
  ElevenRUP.step84205 (p 2331) (p 3286) (p 3292) (p 3319) (p 4319) (p 5171) (p 5325) (derived73378 p h) (derived48520 p h)

theorem derived84206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3564) ∨ (¬ p 4644) ∨ (p 2922) ∨ (¬ p 2590) ∨ (¬ p 2505) :=
  ElevenRUP.step84206 (p 2505) (p 2590) (p 2922) (p 2928) (p 3319) (p 3564) (p 4137) (p 4644) (derived73524 p h) (derived73320 p h) (derived58926 p h)

theorem derived84208 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 4391) ∨ (¬ p 4831) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 4736) ∨ (p 2696) ∨ (p 2685) :=
  ElevenRUP.step84208 (p 2685) (p 2696) (p 3093) (p 3319) (p 3365) (p 3461) (p 3572) (p 4391) (p 4736) (p 4831) (derived73390 p h) (derived73420 p h) (derived56489 p h)

theorem derived84210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5600) ∨ (¬ p 3461) ∨ (¬ p 5123) ∨ (¬ p 3093) ∨ (¬ p 4736) ∨ (p 3005) ∨ (p 2696) ∨ (¬ p 3319) :=
  ElevenRUP.step84210 (p 2696) (p 3005) (p 3093) (p 3319) (p 3365) (p 3461) (p 3877) (p 4736) (p 5123) (p 5600) (derived73488 p h) (derived73390 p h) (derived56109 p h)

theorem derived84213 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3093) ∨ (p 2598) ∨ (p 2528) ∨ (¬ p 3319) ∨ (p 3641) ∨ (¬ p 4330) ∨ (¬ p 3366) ∨ (¬ p 2744) :=
  ElevenRUP.step84213 (p 2241) (p 2247) (p 2528) (p 2534) (p 2598) (p 2744) (p 3055) (p 3093) (p 3319) (p 3366) (p 3641) (p 3874) (p 4330) (derived73226 p h) (derived73350 p h) (derived73268 p h) (derived73484 p h) (derived64235 p h)

theorem derived84216 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 3461) ∨ (¬ p 5123) ∨ (¬ p 3093) ∨ (p 2598) ∨ (p 3641) ∨ (¬ p 3319) ∨ (¬ p 4736) :=
  ElevenRUP.step84216 (p 2598) (p 3055) (p 3093) (p 3319) (p 3461) (p 3641) (p 3874) (p 4149) (p 4286) (p 4736) (p 5123) (derived73548 p h) (derived73350 p h) (derived73484 p h) (derived56155 p h)

theorem derived84220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3379) ∨ (p 2459) ∨ (¬ p 4330) ∨ (¬ p 4810) ∨ (¬ p 2252) ∨ (¬ p 3093) ∨ (p 2807) ∨ (p 2264) :=
  ElevenRUP.step84220 (p 2252) (p 2264) (p 2459) (p 2807) (p 3093) (p 3319) (p 3379) (p 3414) (p 3452) (p 3553) (p 4330) (p 4348) (p 4810) (derived73394 p h) (derived73562 p h) (derived73392 p h) (derived73410 p h) (derived64907 p h)

theorem derived84223 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3319) ∨ (¬ p 4376) ∨ (¬ p 3366) ∨ (p 2459) ∨ (p 3379) ∨ (¬ p 4330) ∨ (¬ p 3093) ∨ (p 2807) ∨ (¬ p 4236) :=
  ElevenRUP.step84223 (p 2264) (p 2459) (p 2807) (p 3093) (p 3319) (p 3366) (p 3379) (p 3414) (p 3452) (p 3553) (p 4236) (p 4330) (p 4348) (p 4376) (derived73410 p h) (derived73562 p h) (derived73394 p h) (derived73392 p h) (derived64992 p h)

theorem derived84235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 2307) ∨ (¬ p 4736) ∨ (p 2982) ∨ (p 2598) ∨ (p 2850) ∨ (p 3309) ∨ (¬ p 5020) ∨ (¬ p 4368) :=
  ElevenRUP.step84235 (p 2307) (p 2598) (p 2850) (p 2982) (p 3055) (p 3309) (p 3319) (p 3549) (p 3684) (p 4368) (p 4736) (p 4948) (p 5020) (derived73846 p h) (derived73350 p h) (derived73442 p h) (derived73406 p h) (derived54579 p h)

theorem derived84248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 5046) :=
  ElevenRUP.step84248 (p 3125) (p 5044) (p 5046) (derived73890 p h) (h 8446)

theorem derived84250 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2363) ∨ (¬ p 2750) ∨ (¬ p 4133) ∨ (¬ p 2088) ∨ (p 2651) ∨ (¬ p 2252) ∨ (p 2911) ∨ (¬ p 5242) ∨ (p 2608) :=
  ElevenRUP.step84250 (p 2088) (p 2252) (p 2363) (p 2437) (p 2608) (p 2651) (p 2657) (p 2750) (p 2911) (p 3644) (p 3742) (p 3954) (p 4133) (p 4347) (p 5242) (derived73452 p h) (derived73560 p h) (derived73288 p h) (derived73434 p h) (derived73498 p h) (derived63121 p h)

theorem derived84253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2122) ∨ (¬ p 4666) ∨ (p 2651) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (p 2437) ∨ (p 2417) ∨ (¬ p 2177) :=
  ElevenRUP.step84253 (p 2122) (p 2177) (p 2252) (p 2417) (p 2437) (p 2651) (p 2657) (p 2750) (p 2829) (p 3742) (p 4278) (p 4666) (derived73288 p h) (derived73452 p h) (derived73546 p h) (derived55883 p h)

theorem derived84259 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3922) ∨ (¬ p 3266) ∨ (¬ p 3950) ∨ (p 2331) ∨ (¬ p 4430) ∨ (¬ p 2249) ∨ (¬ p 2951) ∨ (¬ p 3051) ∨ (¬ p 2992) ∨ (¬ p 3246) :=
  ElevenRUP.step84259 (p 2249) (p 2331) (p 2951) (p 2963) (p 2992) (p 3051) (p 3246) (p 3266) (p 3707) (p 3922) (p 3950) (p 4321) (p 4430) (derived73554 p h) (derived73338 p h) (derived52498 p h)

theorem derived84264 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3461) ∨ (¬ p 4973) ∨ (¬ p 4430) ∨ (¬ p 3922) ∨ (¬ p 3564) :=
  ElevenRUP.step84264 (p 3461) (p 3564) (p 3707) (p 3922) (p 4321) (p 4430) (p 4973) (derived73554 p h) (derived41596 p h)

theorem derived84266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2553) ∨ (¬ p 2274) ∨ (p 2383) :=
  ElevenRUP.step84266 (p 2274) (p 2352) (p 2383) (p 2387) (p 2553) (p 2588) (derived73282 p h) (derived73246 p h) (derived71580 p h)

theorem derived84267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 5051) :=
  ElevenRUP.step84267 (p 3136) (p 5050) (p 5051) (derived73894 p h) (h 8460)

theorem derived84269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 5052) :=
  ElevenRUP.step84269 (p 3136) (p 5050) (p 5052) (derived73894 p h) (h 8463)

theorem derived84270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 5053) :=
  ElevenRUP.step84270 (p 3136) (p 5050) (p 5053) (derived73894 p h) (h 8464)

theorem derived84271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3136) ∨ (p 2132) ∨ (p 2630) ∨ (¬ p 4343) ∨ (p 3367) :=
  ElevenRUP.step84271 (p 2132) (p 2138) (p 2630) (p 2737) (p 2810) (p 3136) (p 3367) (p 3585) (p 4343) (p 5050) (derived73894 p h) (derived73214 p h) (derived73316 p h) (derived73428 p h) (derived66782 p h)

theorem derived84272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2274) ∨ (p 2630) ∨ (¬ p 2284) :=
  ElevenRUP.step84272 (p 2274) (p 2284) (p 2630) (p 2810) (p 3136) (derived73316 p h) (derived63016 p h)

theorem derived84275 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3136) ∨ (p 2992) ∨ (p 2630) :=
  ElevenRUP.step84275 (p 2241) (p 2247) (p 2630) (p 2810) (p 2992) (p 3136) (p 3662) (derived73226 p h) (derived73440 p h) (derived73316 p h) (derived47356 p h)

theorem derived84278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3016) ∨ (p 2946) ∨ (p 2630) :=
  ElevenRUP.step84278 (p 2630) (p 2810) (p 2946) (p 2952) (p 3016) (p 3136) (p 3574) (derived73422 p h) (derived73330 p h) (derived73316 p h) (derived63298 p h)

theorem derived84279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3083) ∨ (p 2630) ∨ (p 2946) :=
  ElevenRUP.step84279 (p 2630) (p 2810) (p 2946) (p 2952) (p 3083) (p 3136) (p 4256) (derived73542 p h) (derived73316 p h) (derived73330 p h) (derived42746 p h)

theorem derived84284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2992) ∨ (¬ p 2696) ∨ (¬ p 3136) :=
  ElevenRUP.step84284 (p 2641) (p 2696) (p 2992) (p 3136) (p 3662) (derived73440 p h) (derived43895 p h)

theorem derived84285 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2741) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 3367) :=
  ElevenRUP.step84285 (p 2696) (p 2741) (p 2992) (p 3136) (p 3367) (p 3662) (derived73440 p h) (derived53540 p h)

theorem derived84292 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2177) ∨ (¬ p 3115) ∨ (¬ p 4870) ∨ (¬ p 4450) ∨ (p 3309) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 2753) :=
  ElevenRUP.step84292 (p 2177) (p 2299) (p 2459) (p 2696) (p 2753) (p 3115) (p 3136) (p 3309) (p 3549) (p 4348) (p 4450) (p 4870) (derived73562 p h) (derived73234 p h) (derived73406 p h) (derived62141 p h)

theorem derived84293 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 3136) ∨ (¬ p 2284) ∨ (¬ p 2696) :=
  ElevenRUP.step84293 (p 2132) (p 2138) (p 2284) (p 2696) (p 3136) (derived73214 p h) (derived53634 p h)

theorem derived84294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2946) ∨ (p 3367) ∨ (¬ p 2737) :=
  ElevenRUP.step84294 (p 2737) (p 2946) (p 2952) (p 3136) (p 3367) (p 3585) (derived73330 p h) (derived73428 p h) (derived45045 p h)

theorem derived84298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2427) ∨ (p 2630) ∨ (¬ p 2951) ∨ (¬ p 3051) :=
  ElevenRUP.step84298 (p 2427) (p 2630) (p 2810) (p 2951) (p 3051) (p 3136) (p 4235) (derived73536 p h) (derived73316 p h) (derived46672 p h)

theorem derived84299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3115) ∨ (p 2630) ∨ (p 2982) :=
  ElevenRUP.step84299 (p 2630) (p 2810) (p 2982) (p 3115) (p 3136) (p 4948) (derived73316 p h) (derived73846 p h) (derived59769 p h)

theorem derived84300 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2177) ∨ (¬ p 5015) ∨ (¬ p 4450) ∨ (¬ p 3115) ∨ (¬ p 4733) ∨ (¬ p 3136) ∨ (¬ p 2696) ∨ (p 2307) :=
  ElevenRUP.step84300 (p 2177) (p 2299) (p 2307) (p 2313) (p 2459) (p 2696) (p 3115) (p 3136) (p 4348) (p 4450) (p 4733) (p 5015) (derived73562 p h) (derived73234 p h) (derived73238 p h) (derived62147 p h)

theorem derived84301 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4031) ∨ (¬ p 3136) ∨ (p 2630) ∨ (p 2406) ∨ (¬ p 2951) ∨ (¬ p 4811) :=
  ElevenRUP.step84301 (p 2406) (p 2630) (p 2810) (p 2951) (p 3136) (p 3238) (p 4031) (p 4811) (derived73316 p h) (derived73374 p h) (derived41133 p h)

theorem derived84302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 4241) ∨ (p 2230) ∨ (¬ p 2659) ∨ (p 2630) :=
  ElevenRUP.step84302 (p 2230) (p 2589) (p 2630) (p 2659) (p 2810) (p 3136) (p 4241) (derived73284 p h) (derived73316 p h) (derived41845 p h)

theorem derived84306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2727) ∨ (¬ p 2241) ∨ (p 2630) :=
  ElevenRUP.step84306 (p 2241) (p 2630) (p 2727) (p 2810) (p 3136) (derived73316 p h) (derived45992 p h)

theorem derived84307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 4700) ∨ (p 2630) :=
  ElevenRUP.step84307 (p 2630) (p 2810) (p 3136) (p 4700) (derived73316 p h) (h 20383)

theorem derived84310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2437) ∨ (p 2630) ∨ (¬ p 3389) :=
  ElevenRUP.step84310 (p 2437) (p 2630) (p 2810) (p 3136) (p 3389) (p 3742) (derived73452 p h) (derived73316 p h) (derived47463 p h)

theorem derived84311 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 4343) ∨ (p 2598) ∨ (¬ p 2696) :=
  ElevenRUP.step84311 (p 2598) (p 2696) (p 3055) (p 3136) (p 4343) (p 4704) (derived73046 p h) (derived73350 p h) (derived49699 p h)

theorem derived84312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2307) ∨ (p 2274) ∨ (p 2630) ∨ (¬ p 3567) ∨ (¬ p 4336) :=
  ElevenRUP.step84312 (p 2274) (p 2307) (p 2630) (p 2810) (p 3097) (p 3136) (p 3567) (p 4336) (derived73352 p h) (derived73316 p h) (derived54957 p h)

theorem derived84314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2668) ∨ (p 2187) ∨ (p 2630) ∨ (¬ p 4336) :=
  ElevenRUP.step84314 (p 2187) (p 2630) (p 2668) (p 2810) (p 3136) (p 3989) (p 4336) (derived73502 p h) (derived73316 p h) (derived47206 p h)

theorem derived84316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2437) ∨ (¬ p 4644) ∨ (p 2630) ∨ (¬ p 2951) ∨ (¬ p 4031) :=
  ElevenRUP.step84316 (p 2437) (p 2630) (p 2810) (p 2951) (p 3136) (p 3742) (p 4031) (p 4644) (derived73452 p h) (derived73316 p h) (derived50809 p h)

theorem derived84317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3136) ∨ (¬ p 4241) ∨ (¬ p 2427) ∨ (p 2630) :=
  ElevenRUP.step84317 (p 2427) (p 2630) (p 2651) (p 2810) (p 3136) (p 4241) (derived73316 p h) (derived43804 p h)

theorem derived84318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 4241) ∨ (p 2630) ∨ (¬ p 2563) ∨ (¬ p 2651) :=
  ElevenRUP.step84318 (p 2563) (p 2630) (p 2651) (p 2810) (p 3136) (p 4241) (derived73316 p h) (derived61617 p h)

theorem derived84320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (¬ p 3367) ∨ (¬ p 3136) ∨ (¬ p 3364) ∨ (p 2946) :=
  ElevenRUP.step84320 (p 2946) (p 2952) (p 3136) (p 3364) (p 3367) (p 4236) (p 4734) (derived72735 p h) (derived73330 p h) (derived58647 p h)

theorem derived84321 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3136) ∨ (¬ p 3016) ∨ (p 3422) ∨ (¬ p 3364) :=
  ElevenRUP.step84321 (p 2946) (p 2952) (p 3016) (p 3136) (p 3364) (p 3422) (p 3584) (derived73330 p h) (derived73426 p h) (derived45414 p h)

theorem derived84322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2995) ∨ (¬ p 2264) ∨ (¬ p 3136) ∨ (p 2881) ∨ (¬ p 2696) :=
  ElevenRUP.step84322 (p 2264) (p 2696) (p 2881) (p 2995) (p 3136) (p 3570) (derived73418 p h) (derived52689 p h)

theorem derived84323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 4902) ∨ (p 3389) ∨ (¬ p 3347) ∨ (¬ p 4186) ∨ (¬ p 3136) ∨ (¬ p 2753) ∨ (¬ p 2696) :=
  ElevenRUP.step84323 (p 2459) (p 2528) (p 2534) (p 2696) (p 2753) (p 3136) (p 3156) (p 3347) (p 3389) (p 3540) (p 4186) (p 4902) (derived73268 p h) (derived73402 p h) (derived71585 p h)

theorem derived84324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 3136) ∨ (p 2363) ∨ (p 2352) ∨ (¬ p 4450) ∨ (¬ p 4729) ∨ (p 2573) ∨ (¬ p 2696) :=
  ElevenRUP.step84324 (p 2352) (p 2363) (p 2573) (p 2579) (p 2696) (p 3115) (p 3136) (p 3956) (p 4347) (p 4450) (p 4729) (derived73560 p h) (derived73500 p h) (derived73274 p h) (derived53471 p h)

theorem derived84325 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3266) ∨ (p 3654) ∨ (¬ p 4450) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 2787) ∨ (¬ p 2696) :=
  ElevenRUP.step84325 (p 2696) (p 2787) (p 3115) (p 3136) (p 3266) (p 3461) (p 3654) (p 3946) (p 4191) (p 4450) (derived73530 p h) (derived73492 p h) (derived61396 p h)

theorem derived84330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3136) ∨ (p 2630) ∨ (¬ p 2651) ∨ (¬ p 4117) :=
  ElevenRUP.step84330 (p 2284) (p 2630) (p 2651) (p 2810) (p 3136) (p 4117) (derived73316 p h) (derived50750 p h)

theorem derived84333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (p 2946) ∨ (¬ p 2737) ∨ (¬ p 3136) :=
  ElevenRUP.step84333 (p 2737) (p 2946) (p 2952) (p 3136) (p 4236) (p 4734) (derived73330 p h) (derived72735 p h) (derived51323 p h)

theorem derived84335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (p 2946) ∨ (¬ p 2598) ∨ (p 3367) ∨ (¬ p 3136) :=
  ElevenRUP.step84335 (p 2598) (p 2946) (p 2952) (p 3136) (p 3367) (p 3585) (p 4236) (derived73330 p h) (derived73428 p h) (derived50894 p h)

theorem derived84336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (p 2946) ∨ (¬ p 3136) ∨ (¬ p 4752) ∨ (¬ p 2598) :=
  ElevenRUP.step84336 (p 2598) (p 2946) (p 2952) (p 3136) (p 4236) (p 4752) (derived73330 p h) (derived62053 p h)

theorem derived84337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 2992) ∨ (¬ p 2741) ∨ (p 2598) ∨ (¬ p 3136) :=
  ElevenRUP.step84337 (p 2598) (p 2741) (p 2992) (p 3055) (p 3136) (p 3367) (p 3662) (derived73440 p h) (derived73350 p h) (derived57538 p h)

theorem derived84339 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3136) ∨ (¬ p 4336) :=
  ElevenRUP.step84339 (p 2797) (p 3136) (p 4195) (p 4336) (derived73532 p h) (h 26731)

theorem derived84343 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2331) ∨ (¬ p 3136) ∨ (¬ p 2901) :=
  ElevenRUP.step84343 (p 2331) (p 2797) (p 2901) (p 3136) (p 4195) (derived73532 p h) (derived46578 p h)

theorem derived84344 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3156) ∨ (¬ p 2331) ∨ (¬ p 3136) :=
  ElevenRUP.step84344 (p 2331) (p 2797) (p 3136) (p 3156) (p 4195) (derived73532 p h) (derived64184 p h)

theorem derived84345 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 5016) ∨ (¬ p 3136) ∨ (¬ p 2667) ∨ (¬ p 3957) ∨ (¬ p 4702) ∨ (¬ p 2563) :=
  ElevenRUP.step84345 (p 2563) (p 2667) (p 2797) (p 3136) (p 3957) (p 4195) (p 4702) (p 5016) (derived73532 p h) (derived64207 p h)

theorem derived84346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3691) ∨ (¬ p 4960) ∨ (¬ p 4155) ∨ (¬ p 2891) ∨ (p 2685) :=
  ElevenRUP.step84346 (p 2685) (p 2891) (p 3136) (p 3572) (p 3691) (p 4155) (p 4960) (derived73420 p h) (derived54881 p h)

theorem derived84347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4237) ∨ (p 3005) ∨ (¬ p 3136) :=
  ElevenRUP.step84347 (p 3005) (p 3136) (p 3877) (p 4237) (derived73488 p h) (h 20457)

theorem derived84349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3136) ∨ (¬ p 3166) ∨ (p 3005) :=
  ElevenRUP.step84349 (p 2901) (p 3005) (p 3136) (p 3166) (p 3877) (derived73488 p h) (derived46659 p h)

theorem derived84351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3368) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (p 2891) ∨ (¬ p 2745) :=
  ElevenRUP.step84351 (p 2745) (p 2891) (p 2951) (p 3051) (p 3136) (p 3368) (p 3486) (derived73398 p h) (derived42376 p h)

theorem derived84355 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3136) ∨ (¬ p 3745) ∨ (¬ p 2192) ∨ (¬ p 4960) :=
  ElevenRUP.step84355 (p 2192) (p 2797) (p 3136) (p 3745) (p 4195) (p 4960) (derived73532 p h) (derived41301 p h)

theorem derived84356 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3136) ∨ (¬ p 3051) ∨ (¬ p 4558) ∨ (¬ p 3745) ∨ (¬ p 2951) :=
  ElevenRUP.step84356 (p 2797) (p 2951) (p 3051) (p 3136) (p 3745) (p 4195) (p 4558) (derived73532 p h) (derived63467 p h)

theorem derived84358 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3156) ∨ (¬ p 3745) ∨ (¬ p 4509) ∨ (¬ p 3136) :=
  ElevenRUP.step84358 (p 2797) (p 3136) (p 3156) (p 3745) (p 4195) (p 4509) (derived73532 p h) (derived50308 p h)

theorem derived84360 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3136) ∨ (¬ p 2156) ∨ (¬ p 2960) ∨ (¬ p 3745) :=
  ElevenRUP.step84360 (p 2156) (p 2797) (p 2960) (p 3136) (p 3745) (p 4195) (derived73532 p h) (derived49404 p h)

theorem derived84363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3699) ∨ (¬ p 3136) ∨ (p 2685) ∨ (¬ p 2960) :=
  ElevenRUP.step84363 (p 2685) (p 2960) (p 3051) (p 3136) (p 3572) (p 3699) (derived73420 p h) (derived51316 p h)

theorem derived84365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 5104) ∨ (p 2685) ∨ (¬ p 3699) :=
  ElevenRUP.step84365 (p 2685) (p 3115) (p 3136) (p 3572) (p 3699) (p 5104) (derived73420 p h) (derived59662 p h)

theorem derived84368 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 3136) ∨ (¬ p 2373) ∨ (¬ p 4702) ∨ (¬ p 4312) :=
  ElevenRUP.step84368 (p 2373) (p 3005) (p 3136) (p 3877) (p 4312) (p 4702) (derived73488 p h) (derived52695 p h)

theorem derived84372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3589) ∨ (¬ p 2284) ∨ (p 2563) ∨ (¬ p 2696) :=
  ElevenRUP.step84372 (p 2284) (p 2563) (p 2696) (p 3136) (p 3589) (p 4110) (derived73516 p h) (derived45184 p h)

theorem derived84373 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 3136) ∨ (¬ p 2088) ∨ (¬ p 2745) ∨ (¬ p 2951) ∨ (¬ p 4262) ∨ (¬ p 4238) :=
  ElevenRUP.step84373 (p 2088) (p 2745) (p 2951) (p 3073) (p 3136) (p 4238) (p 4261) (p 4262) (derived73544 p h) (derived51182 p h)

theorem derived84382 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 4187) ∨ (p 2946) ∨ (p 3755) ∨ (¬ p 4236) ∨ (¬ p 3136) ∨ (¬ p 2307) ∨ (¬ p 3461) ∨ (¬ p 4663) ∨ (¬ p 2781) :=
  ElevenRUP.step84382 (p 2307) (p 2761) (p 2781) (p 2946) (p 2952) (p 3136) (p 3461) (p 3755) (p 4035) (p 4187) (p 4236) (p 4381) (p 4663) (derived73574 p h) (derived73330 p h) (derived73506 p h) (derived64892 p h)

theorem derived84384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 3136) ∨ (¬ p 2584) ∨ (¬ p 2656) ∨ (¬ p 2307) ∨ (p 2122) :=
  ElevenRUP.step84384 (p 2122) (p 2307) (p 2584) (p 2656) (p 3136) (p 3822) (p 4704) (p 4841) (derived73046 p h) (derived73472 p h) (derived52018 p h)

theorem derived84386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2662) ∨ (p 3389) ∨ (p 2630) ∨ (¬ p 4644) ∨ (¬ p 4241) :=
  ElevenRUP.step84386 (p 2630) (p 2662) (p 2810) (p 3136) (p 3389) (p 3540) (p 4241) (p 4644) (derived73402 p h) (derived73316 p h) (derived50562 p h)

theorem derived84388 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3201) ∨ (¬ p 2437) ∨ (¬ p 3364) :=
  ElevenRUP.step84388 (p 2437) (p 3136) (p 3201) (p 3364) (p 3876) (p 4704) (derived73486 p h) (derived73046 p h) (derived62601 p h)

theorem derived84392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2459) ∨ (¬ p 3146) ∨ (¬ p 2951) ∨ (¬ p 3136) :=
  ElevenRUP.step84392 (p 2220) (p 2459) (p 2951) (p 3136) (p 3146) (p 4348) (derived73562 p h) (derived54734 p h)

theorem derived84401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4357) ∨ (p 3434) ∨ (¬ p 3580) ∨ (¬ p 2449) ∨ (¬ p 2727) ∨ (¬ p 3136) :=
  ElevenRUP.step84401 (p 2449) (p 2727) (p 3136) (p 3434) (p 3580) (p 4324) (p 4357) (derived73556 p h) (derived45024 p h)

theorem derived84402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (p 3005) ∨ (¬ p 2284) ∨ (¬ p 3136) :=
  ElevenRUP.step84402 (p 2284) (p 3005) (p 3136) (p 3189) (p 3877) (derived73488 p h) (derived58835 p h)

theorem derived84404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 3309) ∨ (p 2122) ∨ (¬ p 3136) ∨ (¬ p 3093) :=
  ElevenRUP.step84404 (p 2122) (p 3093) (p 3136) (p 3309) (p 3822) (p 4841) (derived73472 p h) (derived60209 p h)

theorem derived84408 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3922) ∨ (p 2608) ∨ (p 2797) ∨ (¬ p 3093) ∨ (¬ p 3136) :=
  ElevenRUP.step84408 (p 2608) (p 2797) (p 3093) (p 3136) (p 3922) (p 3954) (p 4195) (derived73498 p h) (derived73532 p h) (derived44530 p h)

theorem derived84411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2662) ∨ (¬ p 4241) ∨ (¬ p 4715) ∨ (¬ p 3519) ∨ (p 2493) ∨ (p 2630) :=
  ElevenRUP.step84411 (p 2493) (p 2499) (p 2630) (p 2662) (p 2810) (p 3136) (p 3519) (p 4241) (p 4715) (derived73260 p h) (derived73316 p h) (derived50352 p h)

theorem derived84417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3136) ∨ (p 2598) ∨ (p 3367) ∨ (¬ p 3366) :=
  ElevenRUP.step84417 (p 2598) (p 2737) (p 2743) (p 3055) (p 3136) (p 3366) (p 3367) (p 3585) (p 4704) (derived73297 p h) (derived73350 p h) (derived73046 p h) (derived73428 p h) (derived67185 p h)

theorem derived84419 (p : Nat → Prop) (h : Inputs p) :
    (p 4316) ∨ (p 3136) :=
  ElevenRUP.step84419 (p 3136) (p 4316) (p 5992) (derived74325 p h) (h 12940)

theorem derived84421 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 3516) ∨ (¬ p 4790) ∨ (p 2685) ∨ (¬ p 4104) :=
  ElevenRUP.step84421 (p 2449) (p 2685) (p 3516) (p 3572) (p 3947) (p 4104) (p 4790) (derived73494 p h) (derived73420 p h) (derived53208 p h)

theorem derived84423 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (¬ p 2958) ∨ (¬ p 4790) ∨ (p 3136) ∨ (¬ p 2156) :=
  ElevenRUP.step84423 (p 2156) (p 2284) (p 2958) (p 3136) (p 3952) (p 4315) (p 4790) (derived73496 p h) (derived73550 p h) (derived53053 p h)

theorem derived84424 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3389) ∨ (¬ p 4790) ∨ (¬ p 2663) ∨ (p 2630) :=
  ElevenRUP.step84424 (p 2437) (p 2630) (p 2663) (p 2810) (p 3389) (p 3742) (p 4790) (derived73452 p h) (derived73316 p h) (derived62646 p h)

theorem derived84426 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2573) ∨ (¬ p 2663) ∨ (¬ p 4790) ∨ (p 2630) :=
  ElevenRUP.step84426 (p 2573) (p 2630) (p 2663) (p 2810) (p 3016) (p 3574) (p 4790) (derived73422 p h) (derived73316 p h) (derived53096 p h)

theorem derived84427 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 4194) ∨ (p 2630) ∨ (¬ p 4790) ∨ (p 2668) ∨ (¬ p 3987) :=
  ElevenRUP.step84427 (p 2383) (p 2630) (p 2668) (p 2810) (p 3324) (p 3987) (p 4194) (p 4790) (derived73316 p h) (derived73386 p h) (derived53070 p h)

theorem derived84428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (p 3083) ∨ (¬ p 2663) ∨ (¬ p 4790) ∨ (p 2630) :=
  ElevenRUP.step84428 (p 2470) (p 2630) (p 2663) (p 2810) (p 3083) (p 4256) (p 4790) (derived73542 p h) (derived73316 p h) (derived53206 p h)

theorem derived84432 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2437) ∨ (¬ p 3364) ∨ (¬ p 4790) ∨ (¬ p 2651) :=
  ElevenRUP.step84432 (p 2437) (p 2651) (p 3201) (p 3364) (p 3876) (p 4790) (derived73486 p h) (derived53475 p h)

theorem derived84437 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (p 2440) ∨ (¬ p 4790) ∨ (p 2850) ∨ (¬ p 3364) :=
  ElevenRUP.step84437 (p 2440) (p 2542) (p 2651) (p 2850) (p 3364) (p 3684) (p 4790) (derived73270 p h) (derived73442 p h) (derived41036 p h)

theorem derived84438 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (p 3343) ∨ (¬ p 4790) ∨ (¬ p 2663) ∨ (p 2630) :=
  ElevenRUP.step84438 (p 2630) (p 2663) (p 2810) (p 3343) (p 3355) (p 3359) (p 4790) (derived73388 p h) (derived73316 p h) (derived53229 p h)

theorem derived84439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2727) ∨ (¬ p 2651) ∨ (p 3136) ∨ (¬ p 4790) :=
  ElevenRUP.step84439 (p 2651) (p 2727) (p 2992) (p 3136) (p 4111) (p 4315) (p 4790) (derived73518 p h) (derived73550 p h) (derived53110 p h)

theorem derived84440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2958) ∨ (¬ p 4202) ∨ (p 2630) ∨ (p 2891) ∨ (¬ p 4790) ∨ (¬ p 3487) :=
  ElevenRUP.step84440 (p 2630) (p 2810) (p 2891) (p 2958) (p 3051) (p 3486) (p 3487) (p 4202) (p 4790) (derived73316 p h) (derived73398 p h) (derived63820 p h)

theorem derived84444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 2284) ∨ (¬ p 4790) ∨ (p 2860) ∨ (¬ p 4392) :=
  ElevenRUP.step84444 (p 2284) (p 2860) (p 2946) (p 3758) (p 4392) (p 4790) (derived73456 p h) (derived41039 p h)

theorem derived84445 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 4392) ∨ (¬ p 2901) ∨ (¬ p 4790) ∨ (p 2870) :=
  ElevenRUP.step84445 (p 2870) (p 2901) (p 2946) (p 4244) (p 4392) (p 4790) (derived73540 p h) (derived50381 p h)

theorem derived84446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 3367) ∨ (¬ p 4343) ∨ (¬ p 4790) ∨ (¬ p 2651) :=
  ElevenRUP.step84446 (p 2651) (p 2737) (p 3367) (p 3585) (p 4343) (p 4790) (derived73428 p h) (derived49307 p h)

theorem derived84447 (p : Nat → Prop) (h : Inputs p) :
    (p 4117) ∨ (¬ p 2696) :=
  ElevenRUP.step84447 (p 2696) (p 4117) (p 4788) (derived73760 p h) (h 7810)

theorem derived84448 (p : Nat → Prop) (h : Inputs p) :
    (p 4117) ∨ (¬ p 2696) :=
  ElevenRUP.step84448 (p 2696) (p 4117) (p 5903) (derived74211 p h) (h 12401)

theorem derived84456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 2132) ∨ (p 3105) ∨ (¬ p 2972) :=
  ElevenRUP.step84456 (p 2132) (p 2138) (p 2972) (p 3105) (p 3371) (p 4385) (p 4734) (derived73214 p h) (derived73576 p h) (derived72735 p h) (derived55011 p h)

theorem derived84458 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (p 2132) ∨ (¬ p 4172) ∨ (¬ p 3212) ∨ (¬ p 4736) :=
  ElevenRUP.step84458 (p 2132) (p 2138) (p 3105) (p 3212) (p 4172) (p 4385) (p 4736) (derived73576 p h) (derived73214 p h) (derived49238 p h)

theorem derived84460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4382) ∨ (¬ p 2449) ∨ (¬ p 2870) ∨ (¬ p 4362) ∨ (p 3105) :=
  ElevenRUP.step84460 (p 2449) (p 2870) (p 3105) (p 4362) (p 4382) (p 4385) (derived73576 p h) (derived55577 p h)

theorem derived84461 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4192) ∨ (p 3105) ∨ (¬ p 2870) :=
  ElevenRUP.step84461 (p 2870) (p 3105) (p 4192) (p 4385) (derived73576 p h) (h 20634)

theorem derived84463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 2737) ∨ (p 3105) ∨ (¬ p 2972) ∨ (¬ p 5052) :=
  ElevenRUP.step84463 (p 2737) (p 2743) (p 2972) (p 3105) (p 3371) (p 4385) (p 5052) (derived73298 p h) (derived73576 p h) (derived61686 p h)

theorem derived84464 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (p 2132) ∨ (¬ p 2241) ∨ (p 2996) ∨ (p 3105) ∨ (¬ p 4322) ∨ (¬ p 4826) ∨ (¬ p 4736) :=
  ElevenRUP.step84464 (p 2132) (p 2138) (p 2241) (p 2996) (p 3027) (p 3105) (p 3931) (p 4322) (p 4385) (p 4736) (p 4826) (derived73214 p h) (derived73340 p h) (derived73576 p h) (derived53060 p h)

theorem derived84465 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3868) ∨ (p 3105) ∨ (¬ p 4826) ∨ (p 2132) ∨ (¬ p 2922) ∨ (¬ p 4736) ∨ (¬ p 3379) :=
  ElevenRUP.step84465 (p 2132) (p 2138) (p 2922) (p 3105) (p 3379) (p 3868) (p 4322) (p 4385) (p 4736) (p 4826) (derived73576 p h) (derived73214 p h) (derived63291 p h)

theorem derived84467 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2619) ∨ (¬ p 2533) :=
  ElevenRUP.step84467 (p 2533) (p 2619) (p 3105) (p 4385) (derived73576 p h) (h 32233)

theorem derived84473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3951) ∨ (¬ p 2295) ∨ (¬ p 2136) ∨ (p 3105) ∨ (¬ p 3366) ∨ (¬ p 2744) ∨ (p 2220) ∨ (¬ p 2396) ∨ (¬ p 2246) ∨ (¬ p 2331) :=
  ElevenRUP.step84473 (p 2136) (p 2220) (p 2246) (p 2295) (p 2331) (p 2396) (p 2619) (p 2744) (p 3105) (p 3366) (p 3951) (p 4120) (p 4385) (derived73576 p h) (derived73522 p h) (derived64430 p h)

theorem derived84475 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2619) ∨ (¬ p 3949) ∨ (¬ p 4441) ∨ (¬ p 4133) ∨ (¬ p 2459) :=
  ElevenRUP.step84475 (p 2459) (p 2619) (p 3105) (p 3949) (p 4133) (p 4385) (p 4441) (derived73576 p h) (derived40939 p h)

theorem derived84476 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2619) ∨ (¬ p 4902) ∨ (¬ p 2459) ∨ (¬ p 3949) :=
  ElevenRUP.step84476 (p 2459) (p 2619) (p 3105) (p 3949) (p 4385) (p 4902) (derived73576 p h) (derived51575 p h)

theorem derived84477 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5122) ∨ (p 3105) ∨ (¬ p 2619) ∨ (¬ p 3949) :=
  ElevenRUP.step84477 (p 2619) (p 3105) (p 3949) (p 3969) (p 4385) (p 5122) (derived73576 p h) (derived42125 p h)

theorem derived84479 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3941) ∨ (¬ p 3921) ∨ (¬ p 5119) ∨ (¬ p 2307) ∨ (¬ p 2911) ∨ (¬ p 2781) ∨ (p 2132) ∨ (p 3105) :=
  ElevenRUP.step84479 (p 2132) (p 2138) (p 2307) (p 2781) (p 2911) (p 3105) (p 3921) (p 3941) (p 4322) (p 4385) (p 5119) (derived73214 p h) (derived73576 p h) (derived42454 p h)

theorem derived84480 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 3105) ∨ (¬ p 2696) ∨ (p 2737) :=
  ElevenRUP.step84480 (p 2132) (p 2138) (p 2696) (p 2737) (p 2743) (p 3105) (p 4385) (derived73214 p h) (derived73576 p h) (derived73298 p h) (derived63256 p h)

theorem derived84481 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2619) ∨ (¬ p 4387) ∨ (¬ p 3830) ∨ (p 2608) :=
  ElevenRUP.step84481 (p 2608) (p 2619) (p 3105) (p 3830) (p 3954) (p 4385) (p 4387) (derived73576 p h) (derived73498 p h) (derived47782 p h)

theorem derived84482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 4188) ∨ (p 2132) ∨ (p 3105) ∨ (¬ p 5056) :=
  ElevenRUP.step84482 (p 2098) (p 2132) (p 2138) (p 3105) (p 4188) (p 4385) (p 5056) (derived73214 p h) (derived73576 p h) (derived57601 p h)

theorem derived84486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3105) ∨ (p 2284) ∨ (p 2132) :=
  ElevenRUP.step84486 (p 2132) (p 2138) (p 2284) (p 3105) (p 3115) (p 3952) (p 4385) (derived73576 p h) (derived73496 p h) (derived73214 p h) (derived42917 p h)

theorem derived84489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 4786) ∨ (¬ p 2136) ∨ (p 3105) ∨ (¬ p 3951) ∨ (p 2220) :=
  ElevenRUP.step84489 (p 2136) (p 2220) (p 2417) (p 2437) (p 2619) (p 2651) (p 3105) (p 3951) (p 4120) (p 4385) (p 4786) (derived73576 p h) (derived73522 p h) (derived52241 p h)

theorem derived84490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2737) ∨ (p 2839) ∨ (p 3105) :=
  ElevenRUP.step84490 (p 2737) (p 2839) (p 3105) (p 3583) (p 4322) (p 4385) (derived73424 p h) (derived73576 p h) (derived62161 p h)

theorem derived84491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2761) ∨ (p 2839) ∨ (p 3105) :=
  ElevenRUP.step84491 (p 2761) (p 2839) (p 3105) (p 3583) (p 4322) (p 4385) (derived73424 p h) (derived73576 p h) (derived43774 p h)

theorem derived84492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 3105) ∨ (p 2608) ∨ (p 2839) :=
  ElevenRUP.step84492 (p 2608) (p 2839) (p 3105) (p 3583) (p 3954) (p 4322) (p 4385) (derived73576 p h) (derived73498 p h) (derived73424 p h) (derived44176 p h)

theorem derived84495 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 4418) ∨ (¬ p 2972) :=
  ElevenRUP.step84495 (p 2972) (p 3105) (p 4385) (p 4418) (derived73576 p h) (h 19889)

theorem derived84498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4334) ∨ (p 3105) ∨ (¬ p 2860) :=
  ElevenRUP.step84498 (p 2860) (p 3105) (p 3758) (p 4334) (p 4385) (derived73576 p h) (derived73455 p h) (h 39818)

theorem derived84501 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 3115) :=
  ElevenRUP.step84501 (p 2274) (p 2860) (p 3105) (p 3115) (p 4385) (derived73576 p h) (derived47808 p h)

theorem derived84503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2972) ∨ (p 3105) ∨ (¬ p 2210) ∨ (p 2608) :=
  ElevenRUP.step84503 (p 2210) (p 2608) (p 2972) (p 3105) (p 3954) (p 4385) (derived73576 p h) (derived73498 p h) (derived46845 p h)

theorem derived84504 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2972) ∨ (¬ p 2210) ∨ (¬ p 2860) :=
  ElevenRUP.step84504 (p 2210) (p 2860) (p 2972) (p 3105) (p 4385) (derived73576 p h) (derived63231 p h)

theorem derived84505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 4322) ∨ (¬ p 2933) ∨ (p 3105) ∨ (¬ p 3366) ∨ (¬ p 4826) ∨ (p 2132) ∨ (¬ p 4376) ∨ (¬ p 3399) ∨ (p 3379) :=
  ElevenRUP.step84505 (p 2132) (p 2138) (p 2933) (p 3105) (p 3366) (p 3379) (p 3399) (p 3452) (p 3868) (p 4322) (p 4376) (p 4385) (p 4826) (derived73576 p h) (derived73214 p h) (derived73394 p h) (derived50871 p h)

theorem derived84506 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 4382) ∨ (¬ p 2870) ∨ (¬ p 4556) ∨ (¬ p 2396) :=
  ElevenRUP.step84506 (p 2396) (p 2870) (p 3105) (p 4382) (p 4385) (p 4556) (derived73576 p h) (derived57442 p h)

theorem derived84515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3054) ∨ (p 3105) ∨ (¬ p 4730) ∨ (¬ p 2230) ∨ (¬ p 2982) :=
  ElevenRUP.step84515 (p 2230) (p 2982) (p 3054) (p 3105) (p 4385) (p 4730) (derived73576 p h) (derived41059 p h)

theorem derived84517 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 3212) ∨ (p 2427) ∨ (¬ p 2870) ∨ (¬ p 4539) :=
  ElevenRUP.step84517 (p 2427) (p 2870) (p 3105) (p 3212) (p 4235) (p 4385) (p 4539) (derived73576 p h) (derived73536 p h) (derived56429 p h)

theorem derived84519 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 4382) ∨ (¬ p 2870) ∨ (p 2761) ∨ (¬ p 2136) ∨ (p 3051) :=
  ElevenRUP.step84519 (p 2136) (p 2761) (p 2870) (p 3051) (p 3105) (p 3556) (p 4381) (p 4382) (p 4385) (derived73576 p h) (derived73574 p h) (derived73414 p h) (derived49122 p h)

theorem derived84522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (¬ p 4322) ∨ (¬ p 3366) ∨ (p 2241) ∨ (¬ p 2744) ∨ (p 2132) ∨ (¬ p 5119) ∨ (¬ p 3449) ∨ (p 3105) :=
  ElevenRUP.step84522 (p 2132) (p 2138) (p 2241) (p 2247) (p 2744) (p 3105) (p 3366) (p 3449) (p 4181) (p 4322) (p 4385) (p 5119) (derived73226 p h) (derived73214 p h) (derived73576 p h) (derived56498 p h)

theorem derived84523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 4322) ∨ (¬ p 4736) ∨ (¬ p 3093) ∨ (p 2132) ∨ (p 3105) ∨ (¬ p 5119) ∨ (¬ p 3979) :=
  ElevenRUP.step84523 (p 2132) (p 2138) (p 3063) (p 3093) (p 3105) (p 3979) (p 4322) (p 4385) (p 4736) (p 5119) (derived73214 p h) (derived73576 p h) (derived49637 p h)

theorem derived84524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3707) ∨ (¬ p 4942) ∨ (p 3105) ∨ (¬ p 4878) :=
  ElevenRUP.step84524 (p 3105) (p 3707) (p 4322) (p 4385) (p 4878) (p 4942) (derived73576 p h) (derived48025 p h)

theorem derived84526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 4322) ∨ (¬ p 3379) ∨ (p 3105) ∨ (¬ p 2518) ∨ (¬ p 5119) ∨ (¬ p 4736) ∨ (p 2132) :=
  ElevenRUP.step84526 (p 2132) (p 2138) (p 2518) (p 3105) (p 3379) (p 4149) (p 4322) (p 4385) (p 4736) (p 5119) (derived73576 p h) (derived73214 p h) (derived51392 p h)

theorem derived84527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 3105) ∨ (¬ p 2870) ∨ (p 2427) :=
  ElevenRUP.step84527 (p 2427) (p 2870) (p 3105) (p 4235) (p 4322) (p 4385) (derived73576 p h) (derived73536 p h) (derived47927 p h)

theorem derived84531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 3461) ∨ (¬ p 4033) ∨ (p 2156) ∨ (p 3105) :=
  ElevenRUP.step84531 (p 2156) (p 2860) (p 3105) (p 3461) (p 3646) (p 4033) (p 4191) (p 4385) (derived73530 p h) (derived73436 p h) (derived73576 p h) (derived47626 p h)

theorem derived84537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 2829) ∨ (p 2608) ∨ (¬ p 4636) ∨ (¬ p 3985) ∨ (¬ p 2341) ∨ (¬ p 5207) ∨ (¬ p 5059) ∨ (p 3105) ∨ (¬ p 3945) ∨ (p 3266) :=
  ElevenRUP.step84537 (p 2341) (p 2608) (p 2829) (p 3105) (p 3266) (p 3276) (p 3688) (p 3945) (p 3954) (p 3985) (p 4385) (p 4444) (p 4636) (p 5059) (p 5207) (derived73444 p h) (derived73498 p h) (derived73576 p h) (derived73580 p h) (derived56544 p h)

theorem derived84539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2742) ∨ (¬ p 4322) ∨ (¬ p 4625) ∨ (¬ p 2449) ∨ (p 2839) ∨ (p 3105) ∨ (p 2996) ∨ (¬ p 5252) ∨ (¬ p 4394) ∨ (¬ p 2696) :=
  ElevenRUP.step84539 (p 2449) (p 2696) (p 2742) (p 2839) (p 2996) (p 3027) (p 3105) (p 3583) (p 4322) (p 4385) (p 4394) (p 4625) (p 5252) (derived73424 p h) (derived73576 p h) (derived73340 p h) (derived71590 p h)

theorem derived84541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 3105) ∨ (¬ p 5043) ∨ (¬ p 4185) ∨ (p 2839) :=
  ElevenRUP.step84541 (p 2829) (p 2839) (p 3105) (p 3583) (p 4185) (p 4385) (p 5043) (derived73576 p h) (derived73424 p h) (derived41012 p h)

theorem derived84542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (p 3105) ∨ (¬ p 2982) :=
  ElevenRUP.step84542 (p 2982) (p 3105) (p 3695) (p 4385) (derived73576 p h) (h 23074)

theorem derived84544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 2383) ∨ (p 3105) ∨ (¬ p 4368) ∨ (p 2668) ∨ (p 2839) ∨ (p 2608) ∨ (¬ p 5017) :=
  ElevenRUP.step84544 (p 2383) (p 2608) (p 2668) (p 2839) (p 3105) (p 3323) (p 3324) (p 3583) (p 3954) (p 4368) (p 4385) (p 5017) (derived73576 p h) (derived73386 p h) (derived73424 p h) (derived73498 p h) (derived54454 p h)

theorem derived84545 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2248) ∨ (p 3105) ∨ (¬ p 2459) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (p 2608) ∨ (¬ p 5059) :=
  ElevenRUP.step84545 (p 2248) (p 2264) (p 2459) (p 2608) (p 2807) (p 2839) (p 3105) (p 3583) (p 3954) (p 4385) (p 5059) (derived73424 p h) (derived73576 p h) (derived73498 p h) (derived57401 p h)

theorem derived84548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 3105) ∨ (p 2563) ∨ (p 2839) :=
  ElevenRUP.step84548 (p 2563) (p 2839) (p 2982) (p 3105) (p 3583) (p 4110) (p 4385) (derived73576 p h) (derived73516 p h) (derived73424 p h) (derived42685 p h)

theorem derived84550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2396) ∨ (¬ p 5190) ∨ (p 3105) ∨ (¬ p 3951) ∨ (p 2839) ∨ (p 2608) ∨ (¬ p 2573) :=
  ElevenRUP.step84550 (p 2396) (p 2553) (p 2573) (p 2608) (p 2839) (p 3105) (p 3583) (p 3951) (p 3954) (p 4385) (p 5190) (derived73576 p h) (derived73424 p h) (derived73498 p h) (derived50699 p h)

theorem derived84551 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2982) ∨ (¬ p 4717) ∨ (¬ p 3054) ∨ (¬ p 3422) :=
  ElevenRUP.step84551 (p 2982) (p 3054) (p 3105) (p 3422) (p 4385) (p 4717) (derived73576 p h) (derived53709 p h)

theorem derived84552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2136) ∨ (p 2156) ∨ (¬ p 5059) ∨ (p 3105) ∨ (¬ p 2807) ∨ (¬ p 2459) ∨ (¬ p 4786) ∨ (¬ p 2264) :=
  ElevenRUP.step84552 (p 2136) (p 2156) (p 2264) (p 2459) (p 2807) (p 2860) (p 3105) (p 3646) (p 4385) (p 4786) (p 5059) (derived73436 p h) (derived73576 p h) (derived55615 p h)

theorem derived84554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 5051) ∨ (p 3105) :=
  ElevenRUP.step84554 (p 3105) (p 3115) (p 4208) (p 4385) (p 5051) (derived73533 p h) (derived73576 p h) (h 25428)

theorem derived84558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4382) ∨ (p 3105) ∨ (¬ p 2870) ∨ (¬ p 3543) ∨ (¬ p 3516) ∨ (¬ p 4914) :=
  ElevenRUP.step84558 (p 2870) (p 3105) (p 3516) (p 3543) (p 4382) (p 4385) (p 4914) (derived73576 p h) (derived63135 p h)

theorem derived84559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2246) ∨ (¬ p 5059) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (p 3051) ∨ (¬ p 2136) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (p 3105) ∨ (¬ p 2870) :=
  ElevenRUP.step84559 (p 2136) (p 2246) (p 2331) (p 2363) (p 2668) (p 2744) (p 2870) (p 3051) (p 3105) (p 3366) (p 3556) (p 4385) (p 5059) (derived73414 p h) (derived73576 p h) (derived52891 p h)

theorem derived84560 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2137) ∨ (p 4032) :=
  ElevenRUP.step84560 (p 2137) (p 3105) (p 4032) (p 4385) (derived73576 p h) (h 33280)

theorem derived84562 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2528) ∨ (¬ p 5059) ∨ (p 2156) ∨ (¬ p 2860) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 4786) ∨ (¬ p 2136) :=
  ElevenRUP.step84562 (p 2136) (p 2156) (p 2528) (p 2651) (p 2860) (p 3083) (p 3105) (p 3646) (p 4385) (p 4786) (p 5059) (derived73576 p h) (derived73436 p h) (derived52174 p h)

theorem derived84563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3105) ∨ (p 3051) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2870) ∨ (¬ p 4368) :=
  ElevenRUP.step84563 (p 2241) (p 2641) (p 2870) (p 3051) (p 3105) (p 3323) (p 3556) (p 4368) (p 4385) (p 4524) (derived73576 p h) (derived72962 p h) (derived73414 p h) (derived52166 p h)

theorem derived84564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2881) ∨ (p 2177) ∨ (p 3105) :=
  ElevenRUP.step84564 (p 2177) (p 2299) (p 2870) (p 2881) (p 3105) (p 4385) (derived73234 p h) (derived73576 p h) (derived64397 p h)

theorem derived84565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 4322) ∨ (¬ p 2352) ∨ (p 3105) ∨ (p 2132) ∨ (¬ p 4419) ∨ (¬ p 5119) ∨ (¬ p 2573) :=
  ElevenRUP.step84565 (p 2132) (p 2138) (p 2352) (p 2573) (p 3105) (p 3979) (p 4322) (p 4385) (p 4419) (p 5119) (derived73576 p h) (derived73214 p h) (derived59507 p h)

theorem derived84566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2608) ∨ (p 2839) ∨ (¬ p 5059) ∨ (p 3105) ∨ (¬ p 5190) ∨ (¬ p 2573) ∨ (¬ p 2363) :=
  ElevenRUP.step84566 (p 2352) (p 2363) (p 2573) (p 2608) (p 2839) (p 3105) (p 3583) (p 3954) (p 4385) (p 5059) (p 5190) (derived73498 p h) (derived73424 p h) (derived73576 p h) (derived55940 p h)

theorem derived84570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3105) ∨ (¬ p 2797) ∨ (¬ p 3413) ∨ (¬ p 4392) ∨ (¬ p 4975) :=
  ElevenRUP.step84570 (p 2797) (p 3105) (p 3115) (p 3413) (p 4385) (p 4392) (p 4975) (derived73576 p h) (derived53291 p h)

theorem derived84573 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 3212) ∨ (¬ p 2630) ∨ (¬ p 4392) ∨ (¬ p 2951) :=
  ElevenRUP.step84573 (p 2630) (p 2951) (p 3105) (p 3212) (p 4385) (p 4392) (derived73576 p h) (derived69648 p h)

theorem derived84576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (p 3105) ∨ (¬ p 2440) ∨ (¬ p 4882) ∨ (¬ p 4952) :=
  ElevenRUP.step84576 (p 2440) (p 3105) (p 3343) (p 4385) (p 4882) (p 4952) (derived73576 p h) (derived56176 p h)

theorem derived84578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 4322) ∨ (¬ p 3366) ∨ (p 3105) ∨ (¬ p 5119) ∨ (¬ p 2744) ∨ (¬ p 2246) ∨ (p 2132) ∨ (¬ p 2651) ∨ (¬ p 3083) :=
  ElevenRUP.step84578 (p 2132) (p 2138) (p 2246) (p 2651) (p 2744) (p 3083) (p 3105) (p 3366) (p 4149) (p 4322) (p 4385) (p 5119) (derived73576 p h) (derived73214 p h) (derived61549 p h)

theorem derived84579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 4322) ∨ (¬ p 4786) ∨ (¬ p 3083) ∨ (p 2132) ∨ (p 3105) ∨ (¬ p 2651) ∨ (¬ p 5119) :=
  ElevenRUP.step84579 (p 2132) (p 2138) (p 2651) (p 3083) (p 3105) (p 4149) (p 4322) (p 4385) (p 4786) (p 5119) (derived73214 p h) (derived73576 p h) (derived52176 p h)

theorem derived84580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3868) ∨ (¬ p 2651) ∨ (¬ p 4826) ∨ (¬ p 2437) ∨ (p 2132) ∨ (¬ p 4786) ∨ (p 3105) :=
  ElevenRUP.step84580 (p 2132) (p 2138) (p 2437) (p 2651) (p 3105) (p 3868) (p 4322) (p 4385) (p 4786) (p 4826) (derived73214 p h) (derived73576 p h) (derived54915 p h)

theorem derived84582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2608) ∨ (¬ p 5059) ∨ (p 2839) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (p 3105) ∨ (¬ p 2248) :=
  ElevenRUP.step84582 (p 2248) (p 2331) (p 2363) (p 2608) (p 2668) (p 2839) (p 3105) (p 3583) (p 3954) (p 4385) (p 5059) (derived73498 p h) (derived73424 p h) (derived73576 p h) (derived48884 p h)

theorem derived84583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3105) ∨ (¬ p 4392) ∨ (¬ p 2946) ∨ (¬ p 4790) :=
  ElevenRUP.step84583 (p 2946) (p 3105) (p 3115) (p 4385) (p 4392) (p 4790) (derived73576 p h) (derived53037 p h)

theorem derived84584 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3506) ∨ (¬ p 3166) ∨ (¬ p 5111) ∨ (p 3105) ∨ (¬ p 2860) ∨ (¬ p 4033) ∨ (¬ p 4786) ∨ (p 2156) ∨ (¬ p 4604) ∨ (¬ p 2136) :=
  ElevenRUP.step84584 (p 2136) (p 2156) (p 2860) (p 3105) (p 3166) (p 3266) (p 3506) (p 3646) (p 4033) (p 4385) (p 4444) (p 4604) (p 4786) (p 5111) (derived73580 p h) (derived73576 p h) (derived73436 p h) (derived52169 p h)

theorem derived84585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 4322) ∨ (¬ p 2807) ∨ (¬ p 4786) ∨ (¬ p 5119) ∨ (p 3105) ∨ (¬ p 2264) ∨ (p 2132) :=
  ElevenRUP.step84585 (p 2132) (p 2138) (p 2264) (p 2807) (p 3105) (p 3941) (p 4322) (p 4385) (p 4786) (p 5119) (derived73576 p h) (derived73214 p h) (derived52160 p h)

theorem derived84586 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 3212) ∨ (¬ p 2881) ∨ (¬ p 2144) ∨ (¬ p 2870) :=
  ElevenRUP.step84586 (p 2144) (p 2870) (p 2881) (p 3105) (p 3212) (p 4385) (derived73576 p h) (derived47825 p h)

theorem derived84588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3276) ∨ (¬ p 4882) ∨ (¬ p 3358) ∨ (p 3105) ∨ (¬ p 4355) :=
  ElevenRUP.step84588 (p 3105) (p 3276) (p 3358) (p 4322) (p 4355) (p 4385) (p 4882) (derived73576 p h) (derived54129 p h)

theorem derived84589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3276) ∨ (p 3105) ∨ (¬ p 2860) :=
  ElevenRUP.step84589 (p 2860) (p 3105) (p 3276) (p 4322) (p 4385) (derived73576 p h) (derived53672 p h)

theorem derived84591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 4033) ∨ (¬ p 2284) ∨ (p 3105) ∨ (¬ p 5051) ∨ (p 2352) :=
  ElevenRUP.step84591 (p 2284) (p 2352) (p 3105) (p 3564) (p 3956) (p 4033) (p 4385) (p 5051) (derived73576 p h) (derived73500 p h) (derived57359 p h)

theorem derived84592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 4322) ∨ (¬ p 2573) ∨ (¬ p 2553) ∨ (¬ p 4826) ∨ (p 3105) ∨ (p 2132) ∨ (¬ p 4419) :=
  ElevenRUP.step84592 (p 2132) (p 2138) (p 2553) (p 2573) (p 3105) (p 3791) (p 4322) (p 4385) (p 4419) (p 4826) (derived73576 p h) (derived73214 p h) (derived51584 p h)

theorem derived84593 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2911) ∨ (p 2608) ∨ (¬ p 5190) ∨ (¬ p 3389) ∨ (¬ p 2459) ∨ (p 3105) ∨ (¬ p 5059) :=
  ElevenRUP.step84593 (p 2459) (p 2608) (p 2839) (p 2911) (p 3105) (p 3389) (p 3583) (p 3954) (p 4385) (p 5059) (p 5190) (derived73424 p h) (derived73498 p h) (derived73576 p h) (derived63699 p h)

theorem derived84599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4387) ∨ (¬ p 3830) ∨ (p 3105) ∨ (¬ p 4878) ∨ (p 2210) :=
  ElevenRUP.step84599 (p 2210) (p 3105) (p 3555) (p 3830) (p 4385) (p 4387) (p 4878) (derived73576 p h) (derived73412 p h) (derived51021 p h)

theorem derived84603 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 2761) ∨ (p 3266) ∨ (¬ p 2136) ∨ (p 2156) ∨ (¬ p 4793) ∨ (¬ p 2860) ∨ (¬ p 5059) ∨ (¬ p 3516) ∨ (¬ p 3543) ∨ (¬ p 3366) :=
  ElevenRUP.step84603 (p 2136) (p 2156) (p 2761) (p 2860) (p 3105) (p 3266) (p 3366) (p 3516) (p 3543) (p 3646) (p 4385) (p 4444) (p 4793) (p 5059) (derived73576 p h) (derived73580 p h) (derived73436 p h) (derived59504 p h)

theorem derived84604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3888) ∨ (¬ p 4322) ∨ (¬ p 5250) ∨ (p 2132) ∨ (¬ p 2781) ∨ (p 2553) ∨ (p 3105) ∨ (¬ p 2307) :=
  ElevenRUP.step84604 (p 2132) (p 2138) (p 2307) (p 2553) (p 2588) (p 2781) (p 3105) (p 3888) (p 4322) (p 4385) (p 5250) (derived73214 p h) (derived73282 p h) (derived73576 p h) (derived64919 p h)

theorem derived84606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 3051) ∨ (¬ p 3645) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (p 3105) ∨ (¬ p 2246) ∨ (¬ p 2744) ∨ (¬ p 4874) ∨ (¬ p 2870) ∨ (¬ p 5059) :=
  ElevenRUP.step84606 (p 2246) (p 2528) (p 2651) (p 2744) (p 2870) (p 3051) (p 3083) (p 3105) (p 3556) (p 3645) (p 4385) (p 4874) (p 5059) (derived73414 p h) (derived73576 p h) (derived59485 p h)

theorem derived84610 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 3696) ∨ (¬ p 2166) ∨ (¬ p 4878) ∨ (¬ p 4359) ∨ (¬ p 2088) :=
  ElevenRUP.step84610 (p 2088) (p 2166) (p 3609) (p 3696) (p 4340) (p 4359) (p 4878) (derived73558 p h) (derived61135 p h)

theorem derived84615 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3309) ∨ (¬ p 4736) ∨ (¬ p 3950) ∨ (¬ p 3093) ∨ (¬ p 2396) ∨ (p 2132) ∨ (p 3146) :=
  ElevenRUP.step84615 (p 2132) (p 2138) (p 2396) (p 2619) (p 3093) (p 3146) (p 3309) (p 3692) (p 3694) (p 3950) (p 4736) (derived73450 p h) (derived73214 p h) (derived73448 p h) (derived50279 p h)

theorem derived84617 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2619) ∨ (¬ p 4332) ∨ (p 3193) ∨ (¬ p 2744) ∨ (p 2132) ∨ (¬ p 3379) ∨ (p 3146) ∨ (¬ p 3366) :=
  ElevenRUP.step84617 (p 2132) (p 2138) (p 2241) (p 2247) (p 2619) (p 2744) (p 3146) (p 3193) (p 3222) (p 3366) (p 3379) (p 3692) (p 3694) (p 4332) (derived73226 p h) (derived73450 p h) (derived73364 p h) (derived73214 p h) (derived73448 p h) (derived52591 p h)

theorem derived84619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2911) ∨ (¬ p 4132) ∨ (p 2619) ∨ (¬ p 4647) :=
  ElevenRUP.step84619 (p 2619) (p 2870) (p 2911) (p 3694) (p 4132) (p 4647) (derived73450 p h) (derived49398 p h)

theorem derived84620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 3051) ∨ (p 2459) ∨ (¬ p 4132) ∨ (p 2619) :=
  ElevenRUP.step84620 (p 2459) (p 2619) (p 2870) (p 3051) (p 3556) (p 3694) (p 4132) (p 4348) (derived73414 p h) (derived73562 p h) (derived73450 p h) (derived43772 p h)

theorem derived84621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2619) ∨ (¬ p 4132) ∨ (¬ p 4668) ∨ (¬ p 3691) ∨ (¬ p 2870) :=
  ElevenRUP.step84621 (p 2619) (p 2870) (p 3516) (p 3691) (p 3694) (p 4132) (p 4668) (derived73450 p h) (derived52883 p h)

theorem derived84624 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2132) ∨ (¬ p 2598) ∨ (¬ p 2166) :=
  ElevenRUP.step84624 (p 2132) (p 2138) (p 2166) (p 2598) (p 2619) (p 3694) (derived73450 p h) (derived73214 p h) (derived44261 p h)

theorem derived84626 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2132) ∨ (¬ p 2241) ∨ (p 2996) ∨ (p 2619) ∨ (¬ p 2449) ∨ (¬ p 3950) ∨ (¬ p 4736) :=
  ElevenRUP.step84626 (p 2132) (p 2138) (p 2241) (p 2449) (p 2619) (p 2996) (p 3027) (p 3146) (p 3692) (p 3694) (p 3950) (p 4736) (derived73448 p h) (derived73214 p h) (derived73340 p h) (derived73450 p h) (derived49539 p h)

theorem derived84629 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2274) ∨ (¬ p 4506) ∨ (¬ p 2860) :=
  ElevenRUP.step84629 (p 2274) (p 2619) (p 2860) (p 3694) (p 4506) (derived73450 p h) (derived71592 p h)

theorem derived84630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2449) ∨ (¬ p 5123) ∨ (p 2619) ∨ (¬ p 2761) ∨ (¬ p 4786) ∨ (p 2132) ∨ (¬ p 2807) :=
  ElevenRUP.step84630 (p 2132) (p 2138) (p 2449) (p 2619) (p 2761) (p 2807) (p 3694) (p 4786) (p 5123) (p 5568) (derived73450 p h) (derived73214 p h) (derived58194 p h)

theorem derived84634 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2619) ∨ (p 3425) ∨ (¬ p 4901) ∨ (¬ p 4344) :=
  ElevenRUP.step84634 (p 2132) (p 2138) (p 2619) (p 3425) (p 3471) (p 3694) (p 4344) (p 4901) (derived73214 p h) (derived73450 p h) (derived73396 p h) (derived48252 p h)

theorem derived84638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3146) ∨ (p 2132) ∨ (¬ p 4736) ∨ (¬ p 4330) ∨ (¬ p 2493) ∨ (p 2619) ∨ (¬ p 3379) :=
  ElevenRUP.step84638 (p 2132) (p 2138) (p 2493) (p 2619) (p 3146) (p 3379) (p 3564) (p 3692) (p 3694) (p 4330) (p 4736) (derived73448 p h) (derived73214 p h) (derived73450 p h) (derived49646 p h)

theorem derived84641 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4032) ∨ (¬ p 2860) ∨ (¬ p 2220) :=
  ElevenRUP.step84641 (p 2220) (p 2619) (p 2860) (p 3694) (p 4032) (derived73450 p h) (derived44769 p h)

theorem derived84645 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2210) ∨ (¬ p 2860) ∨ (p 2192) :=
  ElevenRUP.step84645 (p 2192) (p 2210) (p 2619) (p 2860) (p 3555) (p 3694) (p 4173) (derived73450 p h) (derived73412 p h) (derived73528 p h) (derived46258 p h)

theorem derived84646 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2619) ∨ (¬ p 2860) ∨ (p 2192) ∨ (¬ p 4506) :=
  ElevenRUP.step84646 (p 2192) (p 2363) (p 2619) (p 2860) (p 3694) (p 4173) (p 4347) (p 4506) (derived73560 p h) (derived73450 p h) (derived73528 p h) (derived48821 p h)

theorem derived84647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 2132) ∨ (¬ p 3366) ∨ (¬ p 3156) ∨ (p 2619) :=
  ElevenRUP.step84647 (p 2132) (p 2138) (p 2619) (p 2737) (p 3156) (p 3366) (p 3694) (derived73214 p h) (derived73450 p h) (derived44728 p h)

theorem derived84649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2619) ∨ (p 2156) ∨ (¬ p 3051) :=
  ElevenRUP.step84649 (p 2156) (p 2619) (p 2860) (p 3051) (p 3646) (p 3694) (derived73450 p h) (derived73436 p h) (derived58290 p h)

theorem derived84651 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 3156) :=
  ElevenRUP.step84651 (p 2274) (p 2619) (p 2860) (p 3156) (p 3694) (derived73450 p h) (derived42730 p h)

theorem derived84655 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3146) ∨ (p 2132) ∨ (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 4786) ∨ (¬ p 3950) ∨ (¬ p 2331) :=
  ElevenRUP.step84655 (p 2132) (p 2138) (p 2295) (p 2331) (p 2396) (p 2619) (p 3146) (p 3692) (p 3694) (p 3950) (p 4786) (derived73450 p h) (derived73448 p h) (derived73214 p h) (derived52044 p h)

theorem derived84656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2619) ∨ (¬ p 2870) ∨ (¬ p 4204) :=
  ElevenRUP.step84656 (p 2190) (p 2619) (p 2870) (p 3694) (p 4204) (derived73450 p h) (h 20188)

theorem derived84658 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2284) ∨ (p 3146) ∨ (¬ p 2860) :=
  ElevenRUP.step84658 (p 2284) (p 2619) (p 2860) (p 3146) (p 3692) (p 3694) (p 3952) (derived73450 p h) (derived73496 p h) (derived73448 p h) (derived54653 p h)

theorem derived84659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (p 2132) ∨ (p 2619) :=
  ElevenRUP.step84659 (p 2132) (p 2138) (p 2284) (p 2619) (p 3156) (p 3694) (p 3952) (derived73496 p h) (derived73214 p h) (derived73450 p h) (derived43074 p h)

theorem derived84663 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3266) ∨ (p 2132) ∨ (p 3146) :=
  ElevenRUP.step84663 (p 2132) (p 2138) (p 2619) (p 3146) (p 3266) (p 3692) (p 3694) (p 4444) (derived73450 p h) (derived73580 p h) (derived73214 p h) (derived73448 p h) (derived46195 p h)

theorem derived84666 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3063) ∨ (¬ p 5118) ∨ (¬ p 4736) ∨ (¬ p 3093) ∨ (p 2132) ∨ (¬ p 2363) ∨ (p 2619) :=
  ElevenRUP.step84666 (p 2132) (p 2138) (p 2363) (p 2619) (p 3063) (p 3093) (p 3694) (p 4736) (p 5118) (p 5568) (derived73214 p h) (derived73450 p h) (derived50350 p h)

theorem derived84667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 5123) ∨ (¬ p 2761) ∨ (¬ p 2417) ∨ (¬ p 3389) ∨ (¬ p 4419) :=
  ElevenRUP.step84667 (p 2132) (p 2138) (p 2417) (p 2619) (p 2761) (p 3389) (p 3694) (p 4419) (p 5123) (p 5568) (derived73214 p h) (derived73450 p h) (derived64978 p h)

theorem derived84668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 3051) ∨ (¬ p 3166) ∨ (¬ p 4786) ∨ (p 2619) ∨ (¬ p 3256) ∨ (¬ p 4134) ∨ (p 2363) ∨ (¬ p 2136) :=
  ElevenRUP.step84668 (p 2136) (p 2363) (p 2619) (p 2870) (p 3051) (p 3166) (p 3256) (p 3556) (p 3694) (p 4134) (p 4347) (p 4786) (derived73414 p h) (derived73450 p h) (derived73560 p h) (derived50878 p h)

theorem derived84669 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3412) ∨ (p 2284) ∨ (¬ p 2166) ∨ (¬ p 2870) :=
  ElevenRUP.step84669 (p 2166) (p 2284) (p 2619) (p 2870) (p 3412) (p 3694) (p 3952) (derived73450 p h) (derived73496 p h) (derived49059 p h)

theorem derived84670 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2210) ∨ (¬ p 2870) ∨ (¬ p 2166) :=
  ElevenRUP.step84670 (p 2166) (p 2210) (p 2619) (p 2870) (p 3694) (derived73450 p h) (derived43880 p h)

theorem derived84673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2619) ∨ (¬ p 4204) ∨ (¬ p 2870) ∨ (¬ p 4506) :=
  ElevenRUP.step84673 (p 2619) (p 2668) (p 2870) (p 3694) (p 4204) (p 4506) (p 4560) (derived73450 p h) (derived72955 p h) (derived48698 p h)

theorem derived84677 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3105) ∨ (¬ p 2532) ∨ (p 2619) ∨ (¬ p 4134) :=
  ElevenRUP.step84677 (p 2363) (p 2532) (p 2619) (p 3105) (p 3694) (p 4134) (p 4347) (derived73560 p h) (derived73450 p h) (derived51119 p h)

theorem derived84680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2619) ∨ (¬ p 2373) ∨ (¬ p 2230) :=
  ElevenRUP.step84680 (p 2230) (p 2373) (p 2619) (p 2870) (p 3694) (derived73450 p h) (derived47986 p h)

theorem derived84682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 4905) ∨ (p 2619) ∨ (p 2459) ∨ (¬ p 2532) :=
  ElevenRUP.step84682 (p 2459) (p 2532) (p 2619) (p 3105) (p 3694) (p 4348) (p 4905) (derived73450 p h) (derived73562 p h) (derived54699 p h)

theorem derived84683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (¬ p 3256) ∨ (p 2459) ∨ (¬ p 4905) ∨ (¬ p 2248) ∨ (p 2839) ∨ (p 2608) ∨ (p 2619) :=
  ElevenRUP.step84683 (p 2248) (p 2459) (p 2608) (p 2619) (p 2839) (p 3166) (p 3256) (p 3583) (p 3694) (p 3954) (p 4348) (p 4905) (derived73562 p h) (derived73424 p h) (derived73498 p h) (derived73450 p h) (derived58207 p h)

theorem derived84684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 3232) ∨ (p 2619) ∨ (¬ p 4388) ∨ (p 3343) ∨ (p 2440) :=
  ElevenRUP.step84684 (p 2440) (p 2542) (p 2619) (p 3105) (p 3232) (p 3343) (p 3359) (p 3694) (p 4388) (derived73450 p h) (derived73388 p h) (derived73270 p h) (derived55269 p h)

theorem derived84686 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2839) ∨ (¬ p 2220) ∨ (¬ p 2144) :=
  ElevenRUP.step84686 (p 2144) (p 2220) (p 2619) (p 2839) (p 3583) (p 3694) (derived73450 p h) (derived73424 p h) (derived71593 p h)

theorem derived84689 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2307) ∨ (¬ p 4506) ∨ (¬ p 2860) ∨ (¬ p 3743) :=
  ElevenRUP.step84689 (p 2307) (p 2619) (p 2860) (p 3694) (p 3743) (p 4506) (derived73450 p h) (derived71594 p h)

theorem derived84690 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4736) ∨ (p 3146) ∨ (¬ p 3950) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (p 2132) :=
  ElevenRUP.step84690 (p 2132) (p 2138) (p 2417) (p 2619) (p 2922) (p 3146) (p 3379) (p 3692) (p 3694) (p 3950) (p 4736) (derived73450 p h) (derived73448 p h) (derived73214 p h) (derived49447 p h)

theorem derived84693 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4558) ∨ (¬ p 2373) ∨ (¬ p 3096) ∨ (¬ p 2870) ∨ (¬ p 2590) :=
  ElevenRUP.step84693 (p 2373) (p 2590) (p 2619) (p 2870) (p 3096) (p 3694) (p 4558) (derived73450 p h) (derived51440 p h)

theorem derived84694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3054) ∨ (p 2563) ∨ (p 2274) ∨ (¬ p 2373) ∨ (p 2619) :=
  ElevenRUP.step84694 (p 2274) (p 2373) (p 2563) (p 2619) (p 3054) (p 3097) (p 3694) (p 4110) (derived73516 p h) (derived73352 p h) (derived73450 p h) (derived55166 p h)

theorem derived84695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 3016) ∨ (¬ p 4158) ∨ (¬ p 2573) ∨ (¬ p 4419) ∨ (¬ p 3083) ∨ (¬ p 2136) ∨ (p 2619) ∨ (p 3051) :=
  ElevenRUP.step84695 (p 2136) (p 2573) (p 2619) (p 2870) (p 3016) (p 3051) (p 3083) (p 3556) (p 3574) (p 3694) (p 4158) (p 4419) (derived73422 p h) (derived73450 p h) (derived73414 p h) (derived60510 p h)

theorem derived84699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4311) ∨ (¬ p 3166) ∨ (¬ p 4906) ∨ (p 2619) ∨ (p 2946) :=
  ElevenRUP.step84699 (p 2619) (p 2946) (p 2952) (p 3166) (p 3694) (p 4311) (p 4906) (derived73450 p h) (derived73330 p h) (derived41960 p h)

theorem derived84707 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2774) ∨ (¬ p 4842) ∨ (¬ p 2220) ∨ (¬ p 4392) ∨ (¬ p 2144) :=
  ElevenRUP.step84707 (p 2144) (p 2220) (p 2619) (p 2774) (p 2780) (p 3694) (p 4392) (p 4842) (derived73450 p h) (derived73308 p h) (derived61954 p h)

theorem derived84709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (p 2619) ∨ (¬ p 2373) :=
  ElevenRUP.step84709 (p 2373) (p 2619) (p 3694) (p 3695) (derived73450 p h) (h 5397)

theorem derived84710 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (p 2619) ∨ (¬ p 2166) ∨ (¬ p 5052) ∨ (¬ p 3371) :=
  ElevenRUP.step84710 (p 2166) (p 2619) (p 2737) (p 2743) (p 3371) (p 3694) (p 5052) (derived73298 p h) (derived73450 p h) (derived50304 p h)

theorem derived84715 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3146) ∨ (p 2839) ∨ (p 2608) :=
  ElevenRUP.step84715 (p 2608) (p 2619) (p 2839) (p 3146) (p 3583) (p 3692) (p 3694) (p 3954) (derived73450 p h) (derived73448 p h) (derived73424 p h) (derived73498 p h) (derived44174 p h)

theorem derived84716 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2839) ∨ (¬ p 2737) ∨ (p 2619) :=
  ElevenRUP.step84716 (p 2619) (p 2737) (p 2839) (p 3146) (p 3583) (p 3692) (p 3694) (derived73448 p h) (derived73424 p h) (derived73450 p h) (derived46808 p h)

theorem derived84717 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2437) ∨ (¬ p 5190) ∨ (p 2619) ∨ (¬ p 4158) ∨ (p 2839) ∨ (p 2608) ∨ (¬ p 3083) :=
  ElevenRUP.step84717 (p 2437) (p 2608) (p 2619) (p 2839) (p 3083) (p 3389) (p 3583) (p 3694) (p 3742) (p 3954) (p 4158) (p 5190) (derived73452 p h) (derived73450 p h) (derived73424 p h) (derived73498 p h) (derived42496 p h)

theorem derived84722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 2839) ∨ (¬ p 3156) ∨ (p 2619) :=
  ElevenRUP.step84722 (p 2619) (p 2737) (p 2839) (p 3156) (p 3583) (p 3694) (derived73424 p h) (derived73450 p h) (derived56866 p h)

theorem derived84723 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2210) ∨ (¬ p 2166) ∨ (p 2839) :=
  ElevenRUP.step84723 (p 2166) (p 2210) (p 2619) (p 2839) (p 3583) (p 3694) (derived73450 p h) (derived73424 p h) (derived43118 p h)

theorem derived84725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (p 3016) ∨ (¬ p 4419) ∨ (p 2132) ∨ (¬ p 4332) ∨ (p 3146) ∨ (¬ p 2573) ∨ (p 2619) :=
  ElevenRUP.step84725 (p 2132) (p 2138) (p 2573) (p 2619) (p 3016) (p 3146) (p 3343) (p 3574) (p 3692) (p 3694) (p 4332) (p 4419) (derived73422 p h) (derived73214 p h) (derived73448 p h) (derived73450 p h) (derived64413 p h)

theorem derived84727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (p 3125) ∨ (p 2619) :=
  ElevenRUP.step84727 (p 2284) (p 2619) (p 3125) (p 3156) (p 3694) (p 3744) (p 3952) (derived73496 p h) (derived73454 p h) (derived73450 p h) (derived57996 p h)

theorem derived84729 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3256) ∨ (p 3146) ∨ (¬ p 4237) ∨ (¬ p 4906) :=
  ElevenRUP.step84729 (p 2619) (p 3146) (p 3256) (p 3692) (p 3694) (p 4237) (p 4906) (derived73450 p h) (derived73448 p h) (derived64416 p h)

theorem derived84730 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2363) ∨ (¬ p 4134) ∨ (p 2839) ∨ (¬ p 3166) ∨ (p 2608) ∨ (p 2619) ∨ (¬ p 2248) :=
  ElevenRUP.step84730 (p 2248) (p 2363) (p 2608) (p 2619) (p 2839) (p 3166) (p 3256) (p 3583) (p 3694) (p 3954) (p 4134) (p 4347) (derived73560 p h) (derived73424 p h) (derived73498 p h) (derived73450 p h) (derived50382 p h)

theorem derived84731 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4418) ∨ (¬ p 3747) ∨ (¬ p 2891) :=
  ElevenRUP.step84731 (p 2619) (p 2891) (p 3694) (p 3747) (p 4418) (derived73450 p h) (h 31176)

theorem derived84736 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 3146) ∨ (p 2619) ∨ (¬ p 2696) :=
  ElevenRUP.step84736 (p 2132) (p 2138) (p 2619) (p 2696) (p 3146) (p 3692) (p 3694) (derived73214 p h) (derived73448 p h) (derived73450 p h) (derived43169 p h)

theorem derived84737 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3146) ∨ (p 2132) ∨ (¬ p 2459) :=
  ElevenRUP.step84737 (p 2132) (p 2138) (p 2459) (p 2619) (p 3146) (p 3692) (p 3694) (derived73450 p h) (derived73448 p h) (derived73214 p h) (derived42694 p h)

theorem derived84741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2619) ∨ (p 3146) ∨ (p 2553) ∨ (¬ p 2781) ∨ (¬ p 3564) ∨ (p 2132) ∨ (¬ p 4330) :=
  ElevenRUP.step84741 (p 2132) (p 2138) (p 2307) (p 2553) (p 2588) (p 2619) (p 2781) (p 3146) (p 3564) (p 3692) (p 3694) (p 4330) (derived73450 p h) (derived73448 p h) (derived73282 p h) (derived73214 p h) (derived64872 p h)

theorem derived84743 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2417) ∨ (p 2132) ∨ (¬ p 4376) ∨ (p 2619) ∨ (¬ p 3950) ∨ (¬ p 2933) ∨ (¬ p 3399) ∨ (p 3379) ∨ (¬ p 3366) :=
  ElevenRUP.step84743 (p 2132) (p 2138) (p 2417) (p 2619) (p 2933) (p 3146) (p 3366) (p 3379) (p 3399) (p 3452) (p 3692) (p 3694) (p 3950) (p 4376) (derived73448 p h) (derived73214 p h) (derived73450 p h) (derived73394 p h) (derived64847 p h)

theorem derived84749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (p 3461) ∨ (p 2619) ∨ (¬ p 3830) ∨ (¬ p 4736) ∨ (p 2132) ∨ (¬ p 4330) ∨ (p 3146) :=
  ElevenRUP.step84749 (p 2132) (p 2138) (p 2619) (p 3146) (p 3461) (p 3692) (p 3694) (p 3707) (p 3830) (p 4191) (p 4330) (p 4736) (derived73530 p h) (derived73450 p h) (derived73214 p h) (derived73448 p h) (derived55573 p h)

theorem derived84752 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2608) ∨ (p 2839) ∨ (p 2619) ∨ (¬ p 2563) :=
  ElevenRUP.step84752 (p 2190) (p 2563) (p 2608) (p 2619) (p 2839) (p 3583) (p 3694) (p 3954) (derived73498 p h) (derived73424 p h) (derived73450 p h) (derived57688 p h)

theorem derived84755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 2528) ∨ (¬ p 2532) ∨ (p 2619) ∨ (¬ p 4158) :=
  ElevenRUP.step84755 (p 2528) (p 2532) (p 2534) (p 2619) (p 3105) (p 3694) (p 4158) (derived73268 p h) (derived73450 p h) (derived41839 p h)

theorem derived84760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 3256) ∨ (¬ p 2532) ∨ (p 2619) ∨ (¬ p 5063) :=
  ElevenRUP.step84760 (p 2532) (p 2619) (p 3105) (p 3256) (p 3694) (p 4118) (p 5063) (derived73520 p h) (derived73450 p h) (derived50285 p h)

theorem derived84764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3054) ∨ (p 2619) ∨ (¬ p 4730) ∨ (¬ p 2230) ∨ (¬ p 2373) :=
  ElevenRUP.step84764 (p 2230) (p 2373) (p 2619) (p 3054) (p 3694) (p 4730) (derived73450 p h) (derived62590 p h)

theorem derived84766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5016) ∨ (p 2132) ∨ (¬ p 2307) ∨ (¬ p 3366) ∨ (¬ p 3323) ∨ (p 3146) ∨ (p 2295) ∨ (¬ p 3950) ∨ (¬ p 4866) ∨ (¬ p 4623) ∨ (p 2619) :=
  ElevenRUP.step84766 (p 2132) (p 2138) (p 2295) (p 2307) (p 2619) (p 3146) (p 3323) (p 3366) (p 3568) (p 3692) (p 3694) (p 3950) (p 4623) (p 4866) (p 5016) (derived73214 p h) (derived73448 p h) (derived73416 p h) (derived73450 p h) (derived42342 p h)

theorem derived84768 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3146) ∨ (¬ p 4882) ∨ (¬ p 2528) ∨ (¬ p 4355) :=
  ElevenRUP.step84768 (p 2528) (p 2619) (p 3146) (p 3692) (p 3694) (p 4355) (p 4882) (derived73450 p h) (derived73448 p h) (derived49801 p h)

theorem derived84771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2619) ∨ (¬ p 4882) ∨ (¬ p 2531) ∨ (¬ p 2440) :=
  ElevenRUP.step84771 (p 2440) (p 2531) (p 2619) (p 3083) (p 3694) (p 4882) (derived73450 p h) (derived50424 p h)

theorem derived84772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5051) ∨ (p 2619) ∨ (¬ p 3156) :=
  ElevenRUP.step84772 (p 2619) (p 3156) (p 3694) (p 5051) (derived73450 p h) (h 20046)

theorem derived84773 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2284) ∨ (¬ p 2951) ∨ (¬ p 2220) ∨ (p 2839) :=
  ElevenRUP.step84773 (p 2220) (p 2284) (p 2619) (p 2839) (p 2951) (p 3583) (p 3694) (p 3952) (derived73450 p h) (derived73496 p h) (derived73424 p h) (derived58520 p h)

theorem derived84774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4402) ∨ (¬ p 3105) ∨ (¬ p 4556) ∨ (p 2619) ∨ (¬ p 4132) ∨ (¬ p 2177) :=
  ElevenRUP.step84774 (p 2177) (p 2619) (p 3105) (p 3694) (p 4132) (p 4402) (p 4556) (derived73450 p h) (derived50173 p h)

theorem derived84775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 4132) ∨ (¬ p 2177) ∨ (¬ p 4556) ∨ (p 2619) :=
  ElevenRUP.step84775 (p 2177) (p 2619) (p 2870) (p 3694) (p 4132) (p 4556) (derived73450 p h) (derived49320 p h)

theorem derived84776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4874) ∨ (¬ p 2246) ∨ (¬ p 3645) ∨ (¬ p 2553) ∨ (¬ p 3016) ∨ (¬ p 2870) ∨ (¬ p 2744) ∨ (¬ p 4506) ∨ (p 3051) ∨ (p 2619) ∨ (¬ p 2651) :=
  ElevenRUP.step84776 (p 2246) (p 2553) (p 2619) (p 2651) (p 2744) (p 2870) (p 3016) (p 3051) (p 3556) (p 3645) (p 3694) (p 4506) (p 4874) (derived73414 p h) (derived73450 p h) (derived71595 p h)

theorem derived84778 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2839) ∨ (¬ p 2177) ∨ (¬ p 4905) ∨ (¬ p 2331) ∨ (¬ p 2248) ∨ (p 2619) ∨ (¬ p 2295) :=
  ElevenRUP.step84778 (p 2177) (p 2248) (p 2295) (p 2331) (p 2608) (p 2619) (p 2839) (p 3583) (p 3694) (p 3954) (p 4905) (derived73498 p h) (derived73424 p h) (derived73450 p h) (derived48839 p h)

theorem derived84780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3519) ∨ (¬ p 2396) ∨ (¬ p 4376) ∨ (¬ p 3950) ∨ (¬ p 3366) ∨ (p 2619) ∨ (p 3146) ∨ (¬ p 2573) ∨ (p 2132) :=
  ElevenRUP.step84780 (p 2132) (p 2138) (p 2396) (p 2553) (p 2573) (p 2619) (p 3146) (p 3366) (p 3519) (p 3692) (p 3694) (p 3950) (p 4376) (derived73450 p h) (derived73448 p h) (derived73214 p h) (derived64940 p h)

theorem derived84786 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2839) ∨ (¬ p 2958) ∨ (¬ p 2220) ∨ (¬ p 4117) :=
  ElevenRUP.step84786 (p 2220) (p 2619) (p 2839) (p 2958) (p 3583) (p 3694) (p 4117) (derived73450 p h) (derived73424 p h) (derived71596 p h)

theorem derived84789 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2951) ∨ (¬ p 2630) ∨ (¬ p 2220) ∨ (¬ p 4392) :=
  ElevenRUP.step84789 (p 2220) (p 2619) (p 2630) (p 2951) (p 3694) (p 4392) (derived73450 p h) (derived69650 p h)

theorem derived84791 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2274) ∨ (p 2307) ∨ (¬ p 2220) ∨ (¬ p 4198) :=
  ElevenRUP.step84791 (p 2220) (p 2274) (p 2307) (p 2313) (p 2619) (p 3694) (p 4198) (derived73450 p h) (derived73238 p h) (derived45030 p h)

theorem derived84793 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 3564) ∨ (¬ p 2651) ∨ (p 3146) ∨ (¬ p 4330) ∨ (¬ p 4786) ∨ (p 2619) ∨ (¬ p 3016) :=
  ElevenRUP.step84793 (p 2132) (p 2138) (p 2619) (p 2651) (p 3016) (p 3146) (p 3564) (p 3692) (p 3694) (p 4330) (p 4786) (derived73214 p h) (derived73448 p h) (derived73450 p h) (derived52389 p h)

theorem derived84795 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 2417) ∨ (¬ p 4882) ∨ (¬ p 3741) ∨ (¬ p 4115) ∨ (p 2619) ∨ (¬ p 4590) :=
  ElevenRUP.step84795 (p 2417) (p 2619) (p 3516) (p 3694) (p 3741) (p 3821) (p 4115) (p 4590) (p 4882) (derived73470 p h) (derived73450 p h) (derived55582 p h)

theorem derived84797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2619) ∨ (¬ p 3166) ∨ (p 2156) ∨ (¬ p 2860) ∨ (¬ p 2136) ∨ (¬ p 4786) ∨ (p 2459) ∨ (¬ p 4905) :=
  ElevenRUP.step84797 (p 2136) (p 2156) (p 2459) (p 2619) (p 2860) (p 3166) (p 3256) (p 3646) (p 3694) (p 4348) (p 4786) (p 4905) (derived73450 p h) (derived73436 p h) (derived73562 p h) (derived63990 p h)

theorem derived84800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 3461) ∨ (¬ p 4200) ∨ (¬ p 5568) ∨ (p 2132) ∨ (¬ p 2331) ∨ (¬ p 4330) ∨ (¬ p 4421) ∨ (p 2619) ∨ (¬ p 4786) :=
  ElevenRUP.step84800 (p 2132) (p 2138) (p 2331) (p 2619) (p 3461) (p 3506) (p 3694) (p 4191) (p 4200) (p 4330) (p 4421) (p 4786) (p 5568) (derived73530 p h) (derived73214 p h) (derived73450 p h) (derived48220 p h)

theorem derived84803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 2761) ∨ (p 2132) ∨ (¬ p 4786) ∨ (¬ p 3286) ∨ (p 2619) ∨ (¬ p 3950) ∨ (p 3146) :=
  ElevenRUP.step84803 (p 2132) (p 2138) (p 2619) (p 2761) (p 3146) (p 3286) (p 3506) (p 3692) (p 3694) (p 3950) (p 4381) (p 4786) (derived73574 p h) (derived73214 p h) (derived73450 p h) (derived73448 p h) (derived52227 p h)

theorem derived84804 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3950) ∨ (¬ p 4661) ∨ (p 3146) ∨ (¬ p 4786) ∨ (¬ p 3506) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 2807) :=
  ElevenRUP.step84804 (p 2132) (p 2138) (p 2619) (p 2761) (p 2807) (p 3146) (p 3506) (p 3692) (p 3694) (p 3950) (p 4381) (p 4661) (p 4786) (derived73574 p h) (derived73448 p h) (derived73214 p h) (derived73450 p h) (derived54400 p h)

theorem derived84805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 4421) ∨ (¬ p 5117) ∨ (p 2619) ∨ (p 2132) ∨ (¬ p 2331) ∨ (¬ p 3506) ∨ (¬ p 4786) :=
  ElevenRUP.step84805 (p 2132) (p 2138) (p 2331) (p 2619) (p 3506) (p 3694) (p 4421) (p 4786) (p 5117) (p 5568) (derived73450 p h) (derived73214 p h) (derived48221 p h)

theorem derived84807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2619) ∨ (¬ p 2870) ∨ (p 2156) ∨ (¬ p 4558) :=
  ElevenRUP.step84807 (p 2156) (p 2220) (p 2619) (p 2870) (p 3646) (p 3694) (p 4558) (derived73450 p h) (derived73436 p h) (derived54947 p h)

theorem derived84808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2668) ∨ (¬ p 4786) ∨ (p 2619) ∨ (p 2132) ∨ (¬ p 2363) ∨ (¬ p 5118) ∨ (¬ p 2331) :=
  ElevenRUP.step84808 (p 2132) (p 2138) (p 2331) (p 2363) (p 2619) (p 2668) (p 3694) (p 4786) (p 5118) (p 5568) (derived73450 p h) (derived73214 p h) (derived51242 p h)

theorem derived84810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 4149) ∨ (¬ p 4355) ∨ (p 2619) ∨ (¬ p 4882) :=
  ElevenRUP.step84810 (p 2619) (p 3694) (p 4149) (p 4355) (p 4882) (p 5568) (derived73450 p h) (derived63216 p h)

theorem derived84811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3461) ∨ (p 2132) ∨ (¬ p 5568) ∨ (¬ p 5123) ∨ (¬ p 4786) ∨ (p 2619) ∨ (¬ p 2331) :=
  ElevenRUP.step84811 (p 2132) (p 2138) (p 2331) (p 2619) (p 3323) (p 3461) (p 3694) (p 4786) (p 5123) (p 5568) (derived73214 p h) (derived73450 p h) (derived56495 p h)

theorem derived84817 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2563) ∨ (p 2132) ∨ (p 2619) :=
  ElevenRUP.step84817 (p 2132) (p 2138) (p 2373) (p 2563) (p 2619) (p 3694) (p 4110) (derived73516 p h) (derived73214 p h) (derived73450 p h) (derived43959 p h)

theorem derived84819 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2619) ∨ (¬ p 4558) ∨ (¬ p 2373) ∨ (p 2563) :=
  ElevenRUP.step84819 (p 2373) (p 2563) (p 2619) (p 2870) (p 3694) (p 4110) (p 4558) (derived73450 p h) (derived73516 p h) (derived62158 p h)

theorem derived84821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2352) ∨ (¬ p 4115) ∨ (¬ p 4718) ∨ (p 2619) ∨ (¬ p 4170) :=
  ElevenRUP.step84821 (p 2352) (p 2619) (p 2860) (p 3694) (p 4115) (p 4170) (p 4718) (derived73450 p h) (derived41634 p h)

theorem derived84823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 3519) ∨ (¬ p 3564) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 5123) ∨ (¬ p 4376) ∨ (¬ p 3461) :=
  ElevenRUP.step84823 (p 2132) (p 2138) (p 2573) (p 2619) (p 3366) (p 3461) (p 3519) (p 3564) (p 3694) (p 4376) (p 5123) (p 5568) (derived73214 p h) (derived73450 p h) (derived64936 p h)

theorem derived84824 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2619) ∨ (¬ p 2751) ∨ (¬ p 4392) ∨ (¬ p 3156) :=
  ElevenRUP.step84824 (p 2619) (p 2751) (p 2992) (p 3156) (p 3694) (p 4392) (derived73450 p h) (derived48070 p h)

theorem derived84825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2619) ∨ (p 2651) ∨ (¬ p 3156) :=
  ElevenRUP.step84825 (p 2619) (p 2651) (p 2657) (p 2946) (p 3156) (p 3694) (derived73450 p h) (derived73288 p h) (derived46179 p h)

theorem derived84826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2619) ∨ (p 2156) ∨ (p 2839) :=
  ElevenRUP.step84826 (p 2156) (p 2220) (p 2619) (p 2839) (p 3583) (p 3646) (p 3694) (derived73450 p h) (derived73436 p h) (derived73424 p h) (derived42911 p h)

theorem derived84829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (p 2210) ∨ (¬ p 4878) ∨ (¬ p 4446) ∨ (p 2619) :=
  ElevenRUP.step84829 (p 2210) (p 2619) (p 3449) (p 3555) (p 3694) (p 4446) (p 4878) (derived73412 p h) (derived73450 p h) (derived51590 p h)

theorem derived84832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 3519) ∨ (¬ p 5118) ∨ (¬ p 3366) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 2573) ∨ (¬ p 4376) :=
  ElevenRUP.step84832 (p 2132) (p 2138) (p 2352) (p 2363) (p 2573) (p 2619) (p 3366) (p 3519) (p 3694) (p 4376) (p 5118) (p 5568) (derived73214 p h) (derived73450 p h) (derived51080 p h)

theorem derived84833 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3830) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (p 3379) ∨ (¬ p 3366) ∨ (p 2132) ∨ (¬ p 3707) ∨ (p 2619) :=
  ElevenRUP.step84833 (p 2132) (p 2138) (p 2619) (p 3366) (p 3379) (p 3452) (p 3694) (p 3707) (p 3830) (p 4376) (p 5123) (p 5568) (derived73394 p h) (derived73214 p h) (derived73450 p h) (derived64848 p h)

theorem derived84835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4157) ∨ (¬ p 2470) ∨ (¬ p 2656) ∨ (p 2946) ∨ (p 2619) ∨ (¬ p 3979) ∨ (¬ p 2630) ∨ (p 3146) ∨ (¬ p 5122) ∨ (¬ p 5051) :=
  ElevenRUP.step84835 (p 2470) (p 2619) (p 2630) (p 2656) (p 2946) (p 2952) (p 3146) (p 3692) (p 3694) (p 3979) (p 4157) (p 5051) (p 5122) (derived73330 p h) (derived73450 p h) (derived73448 p h) (derived71598 p h)

theorem derived84838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2619) ∨ (¬ p 3873) ∨ (p 2774) ∨ (p 2839) :=
  ElevenRUP.step84838 (p 2619) (p 2774) (p 2780) (p 2829) (p 2839) (p 3583) (p 3694) (p 3873) (derived73450 p h) (derived73308 p h) (derived73424 p h) (derived47079 p h)

theorem derived84840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 3830) ∨ (¬ p 2608) ∨ (¬ p 4388) ∨ (p 2619) :=
  ElevenRUP.step84840 (p 2608) (p 2619) (p 3105) (p 3694) (p 3830) (p 3834) (p 4388) (derived73474 p h) (derived73450 p h) (derived46958 p h)

theorem derived84842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2619) ∨ (¬ p 2284) ∨ (¬ p 4906) ∨ (p 2156) :=
  ElevenRUP.step84842 (p 2156) (p 2220) (p 2284) (p 2619) (p 3646) (p 3694) (p 4906) (derived73450 p h) (derived73436 p h) (derived64704 p h)

theorem derived84845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 3146) ∨ (¬ p 3759) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 3950) ∨ (¬ p 2417) ∨ (¬ p 3389) :=
  ElevenRUP.step84845 (p 2132) (p 2138) (p 2417) (p 2619) (p 3146) (p 3367) (p 3389) (p 3692) (p 3694) (p 3759) (p 3950) (p 4734) (derived73448 p h) (derived72735 p h) (derived73214 p h) (derived73450 p h) (derived53687 p h)

theorem derived84850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4342) ∨ (¬ p 2819) ∨ (p 2352) :=
  ElevenRUP.step84850 (p 2352) (p 2819) (p 3956) (p 4342) (p 4358) (derived73563 p h) (derived73500 p h) (h 21763)

theorem derived84853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 4185) ∨ (p 2819) :=
  ElevenRUP.step84853 (p 2187) (p 2819) (p 3989) (p 4185) (p 4358) (derived73501 p h) (derived73564 p h) (h 6917)

theorem derived84855 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2619) ∨ (¬ p 4185) ∨ (¬ p 2774) :=
  ElevenRUP.step84855 (p 2132) (p 2138) (p 2619) (p 2774) (p 3694) (p 4185) (derived73214 p h) (derived73450 p h) (derived69501 p h)

theorem derived84856 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 2774) ∨ (p 2284) ∨ (¬ p 4185) ∨ (¬ p 5053) :=
  ElevenRUP.step84856 (p 2132) (p 2138) (p 2284) (p 2774) (p 3952) (p 4185) (p 5053) (derived73214 p h) (derived73496 p h) (derived41943 p h)

theorem derived84859 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2274) ∨ (¬ p 4185) ∨ (¬ p 2785) :=
  ElevenRUP.step84859 (p 2274) (p 2307) (p 2313) (p 2785) (p 3097) (p 4185) (derived73238 p h) (derived73351 p h) (h 28946)

theorem derived84860 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3872) ∨ (¬ p 4140) ∨ (¬ p 4185) :=
  ElevenRUP.step84860 (p 2122) (p 3822) (p 3872) (p 4140) (p 4185) (derived73472 p h) (h 6714)

theorem derived84868 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (¬ p 4555) ∨ (¬ p 4185) ∨ (¬ p 2774) :=
  ElevenRUP.step84868 (p 2132) (p 2138) (p 2774) (p 2870) (p 4185) (p 4244) (p 4555) (derived73540 p h) (derived73214 p h) (derived41803 p h)

theorem derived84869 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 2774) ∨ (¬ p 4185) ∨ (p 2563) ∨ (¬ p 4885) :=
  ElevenRUP.step84869 (p 2132) (p 2138) (p 2563) (p 2774) (p 4110) (p 4185) (p 4885) (derived73214 p h) (derived73516 p h) (derived41829 p h)

theorem derived84871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2839) ∨ (¬ p 4185) ∨ (p 2220) ∨ (¬ p 2143) :=
  ElevenRUP.step84871 (p 2143) (p 2220) (p 2829) (p 2839) (p 3583) (p 4120) (p 4185) (derived73424 p h) (derived73522 p h) (derived69503 p h)

theorem derived84872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2839) ∨ (¬ p 2143) ∨ (¬ p 4185) ∨ (p 3051) ∨ (¬ p 4555) :=
  ElevenRUP.step84872 (p 2143) (p 2829) (p 2839) (p 3051) (p 3556) (p 3583) (p 4185) (p 4555) (derived73424 p h) (derived73414 p h) (derived41987 p h)

theorem derived84877 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4193) ∨ (¬ p 2619) ∨ (p 2122) ∨ (¬ p 2274) ∨ (¬ p 4509) :=
  ElevenRUP.step84877 (p 2122) (p 2274) (p 2619) (p 3822) (p 4193) (p 4509) (derived73472 p h) (derived49567 p h)

theorem derived84879 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2122) ∨ (¬ p 2553) ∨ (p 2839) ∨ (¬ p 4193) :=
  ElevenRUP.step84879 (p 2122) (p 2553) (p 2608) (p 2839) (p 3583) (p 3822) (p 3954) (p 4193) (derived73498 p h) (derived73472 p h) (derived73424 p h) (derived57245 p h)

theorem derived84880 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3105) ∨ (¬ p 5046) ∨ (¬ p 2295) ∨ (¬ p 4193) ∨ (¬ p 3745) :=
  ElevenRUP.step84880 (p 2122) (p 2295) (p 3105) (p 3745) (p 3822) (p 4193) (p 5046) (derived73472 p h) (derived64329 p h)

theorem derived84887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (p 2122) ∨ (p 2972) ∨ (¬ p 2553) ∨ (¬ p 2137) ∨ (¬ p 4193) :=
  ElevenRUP.step84887 (p 2122) (p 2137) (p 2553) (p 2972) (p 3212) (p 3822) (p 4193) (p 4363) (derived73472 p h) (derived73568 p h) (derived45961 p h)

theorem derived84889 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 4149) ∨ (p 2383) ∨ (p 3564) ∨ (¬ p 2577) ∨ (¬ p 2510) :=
  ElevenRUP.step84889 (p 2383) (p 2387) (p 2510) (p 2577) (p 3564) (p 4137) (p 4149) (p 5580) (derived73246 p h) (derived73524 p h) (derived46642 p h)

theorem derived84890 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5580) ∨ (p 2563) ∨ (¬ p 2373) ∨ (¬ p 3955) :=
  ElevenRUP.step84890 (p 2373) (p 2563) (p 3955) (p 3969) (p 4110) (p 5580) (derived73516 p h) (derived46053 p h)

theorem derived84893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5123) ∨ (¬ p 4117) ∨ (¬ p 4877) ∨ (¬ p 2753) ∨ (¬ p 3580) ∨ (¬ p 2449) ∨ (¬ p 2761) ∨ (p 2187) ∨ (¬ p 3645) ∨ (¬ p 2651) ∨ (p 2156) :=
  ElevenRUP.step84893 (p 2156) (p 2187) (p 2449) (p 2651) (p 2753) (p 2761) (p 3580) (p 3645) (p 3646) (p 3989) (p 4117) (p 4877) (p 5123) (p 5580) (derived73502 p h) (derived73436 p h) (derived50378 p h)

theorem derived84897 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3519) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3051) ∨ (p 2668) ∨ (¬ p 4399) ∨ (¬ p 5123) ∨ (¬ p 4236) ∨ (¬ p 2761) ∨ (¬ p 4376) ∨ (p 2331) :=
  ElevenRUP.step84897 (p 2331) (p 2668) (p 2761) (p 2963) (p 3051) (p 3246) (p 3324) (p 3366) (p 3519) (p 4236) (p 4376) (p 4399) (p 5123) (p 5580) (derived73386 p h) (derived73338 p h) (derived53847 p h)

theorem derived84898 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 2331) ∨ (¬ p 3136) ∨ (¬ p 5118) ∨ (¬ p 2470) ∨ (¬ p 3146) ∨ (p 2668) ∨ (¬ p 2951) ∨ (¬ p 3904) ∨ (¬ p 2531) :=
  ElevenRUP.step84898 (p 2331) (p 2470) (p 2531) (p 2668) (p 2951) (p 2963) (p 3136) (p 3146) (p 3324) (p 3904) (p 5118) (p 5580) (derived73338 p h) (derived73386 p h) (derived71599 p h)

theorem derived84900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5123) ∨ (¬ p 2761) ∨ (¬ p 2807) ∨ (p 2187) ∨ (¬ p 4786) ∨ (¬ p 2136) ∨ (¬ p 2449) ∨ (p 2156) :=
  ElevenRUP.step84900 (p 2136) (p 2156) (p 2187) (p 2449) (p 2761) (p 2807) (p 3646) (p 3989) (p 4786) (p 5123) (p 5580) (derived73502 p h) (derived73436 p h) (derived52226 p h)

end ElevenLogic
