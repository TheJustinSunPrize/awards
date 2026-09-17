import SunPrize.Certificate.Derived061
import SunPrize.Certificate.Logic062
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived113615 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2122) ∨ (p 2396) ∨ (p 3093) ∨ (¬ p 2608) :=
  ElevenRUP.step113615 (p 2122) (p 2396) (p 2608) (p 2829) (p 3093) (p 3918) (derived95271 p h) (derived96376 p h)

theorem derived113617 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 2774) ∨ (¬ p 3309) :=
  ElevenRUP.step113617 (p 2177) (p 2717) (p 2774) (p 2829) (p 3309) (p 3918) (derived95275 p h) (derived96376 p h)

theorem derived113618 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2295) ∨ (p 2696) ∨ (¬ p 3309) ∨ (¬ p 2774) :=
  ElevenRUP.step113618 (p 2295) (p 2696) (p 2774) (p 2829) (p 3309) (p 3918) (derived95277 p h) (derived96376 p h)

theorem derived113620 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2860) ∨ (¬ p 2166) ∨ (p 3093) ∨ (¬ p 2210) :=
  ElevenRUP.step113620 (p 2166) (p 2210) (p 2829) (p 2860) (p 3093) (p 3918) (derived113168 p h) (derived96376 p h)

theorem derived113622 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (¬ p 2504) ∨ (p 3016) ∨ (p 2598) :=
  ElevenRUP.step113622 (p 2504) (p 2598) (p 2774) (p 2829) (p 3016) (p 3918) (p 4753) (derived105514 p h) (derived95282 p h) (derived96376 p h)

theorem derived113625 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 5503) ∨ (¬ p 4075) ∨ (¬ p 4710) ∨ (¬ p 4452) ∨ (p 2819) :=
  ElevenRUP.step113625 (p 2819) (p 2829) (p 3918) (p 4075) (p 4452) (p 4710) (p 5503) (derived95290 p h) (derived96376 p h)

theorem derived113630 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 4435) ∨ (¬ p 5514) ∨ (¬ p 3019) ∨ (¬ p 4337) ∨ (¬ p 2440) :=
  ElevenRUP.step113630 (p 2440) (p 2829) (p 3019) (p 3918) (p 4337) (p 4435) (p 5514) (derived111312 p h) (derived96376 p h)

theorem derived113633 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 3125) ∨ (p 2982) ∨ (p 2122) ∨ (¬ p 3319) ∨ (¬ p 2563) :=
  ElevenRUP.step113633 (p 2122) (p 2563) (p 2829) (p 2982) (p 3125) (p 3319) (p 3918) (derived112446 p h) (derived96376 p h)

theorem derived113634 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2860) ∨ (¬ p 2210) ∨ (¬ p 2373) ∨ (¬ p 4210) ∨ (p 3093) :=
  ElevenRUP.step113634 (p 2210) (p 2373) (p 2829) (p 2860) (p 3093) (p 3918) (p 4210) (derived113177 p h) (derived96376 p h)

theorem derived113641 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2860) ∨ (¬ p 2102) ∨ (¬ p 4313) ∨ (p 2088) ∨ (¬ p 3073) ∨ (¬ p 4317) ∨ (p 3425) :=
  ElevenRUP.step113641 (p 2088) (p 2102) (p 2829) (p 2860) (p 3073) (p 3425) (p 3918) (p 4313) (p 4317) (derived113535 p h) (derived96376 p h)

theorem derived113642 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2177) ∨ (p 2230) ∨ (¬ p 2774) ∨ (p 3367) ∨ (p 2373) ∨ (¬ p 3363) ∨ (¬ p 3309) :=
  ElevenRUP.step113642 (p 2177) (p 2230) (p 2373) (p 2774) (p 2829) (p 3309) (p 3363) (p 3367) (p 3918) (p 4905) (derived105995 p h) (derived81189 p h) (derived96376 p h)

theorem derived113643 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2363) ∨ (¬ p 3361) ∨ (p 2737) ∨ (¬ p 2774) ∨ (¬ p 3063) ∨ (p 3115) ∨ (p 2946) ∨ (¬ p 5059) :=
  ElevenRUP.step113643 (p 2363) (p 2737) (p 2774) (p 2829) (p 2946) (p 3063) (p 3115) (p 3361) (p 3918) (p 5059) (derived83500 p h) (derived96376 p h)

theorem derived113644 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (¬ p 2363) ∨ (p 2807) ∨ (p 2737) ∨ (p 2449) ∨ (¬ p 3063) ∨ (¬ p 3361) :=
  ElevenRUP.step113644 (p 2363) (p 2449) (p 2737) (p 2774) (p 2807) (p 2829) (p 3063) (p 3361) (p 3918) (p 4669) (derived105415 p h) (derived83503 p h) (derived96376 p h)

theorem derived113645 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2396) ∨ (p 3166) ∨ (p 2737) ∨ (p 3256) ∨ (¬ p 2774) ∨ (¬ p 3361) ∨ (¬ p 3950) ∨ (¬ p 3309) :=
  ElevenRUP.step113645 (p 2396) (p 2737) (p 2774) (p 2829) (p 3166) (p 3256) (p 3309) (p 3361) (p 3918) (p 3950) (derived85342 p h) (derived96376 p h)

theorem derived113650 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2396) ∨ (p 3166) ∨ (p 3367) ∨ (¬ p 3309) ∨ (p 3256) ∨ (¬ p 2774) ∨ (¬ p 2663) ∨ (¬ p 3363) ∨ (¬ p 3950) :=
  ElevenRUP.step113650 (p 2396) (p 2663) (p 2774) (p 2829) (p 3166) (p 3256) (p 3309) (p 3363) (p 3367) (p 3918) (p 3950) (derived85321 p h) (derived96376 p h)

theorem derived113651 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3073) ∨ (¬ p 3361) ∨ (¬ p 4317) ∨ (p 2363) ∨ (p 3156) ∨ (¬ p 2774) ∨ (p 2737) ∨ (p 2946) :=
  ElevenRUP.step113651 (p 2363) (p 2737) (p 2774) (p 2829) (p 2946) (p 3073) (p 3156) (p 3361) (p 3918) (p 4134) (p 4317) (derived105379 p h) (derived88523 p h) (derived96376 p h)

theorem derived113657 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 2608) ∨ (p 3093) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 4329) ∨ (¬ p 5254) :=
  ElevenRUP.step113657 (p 2417) (p 2608) (p 2761) (p 2829) (p 3093) (p 3389) (p 3519) (p 3918) (p 4329) (p 4376) (p 5254) (derived106320 p h) (derived95285 p h) (derived96376 p h)

theorem derived113660 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2819) ∨ (¬ p 4044) ∨ (¬ p 2807) ∨ (p 3093) ∨ (¬ p 3256) ∨ (¬ p 2608) ∨ (¬ p 2246) ∨ (p 2459) :=
  ElevenRUP.step113660 (p 2246) (p 2459) (p 2608) (p 2744) (p 2807) (p 2819) (p 2829) (p 3093) (p 3256) (p 3918) (p 4044) (p 4503) (derived106503 p h) (derived106530 p h) (derived95278 p h) (derived96376 p h)

theorem derived113663 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3516) ∨ (p 3343) ∨ (¬ p 3543) ∨ (¬ p 4697) ∨ (¬ p 2761) ∨ (p 3266) ∨ (¬ p 2608) ∨ (¬ p 3019) ∨ (p 3093) ∨ (¬ p 4337) :=
  ElevenRUP.step113663 (p 2608) (p 2761) (p 2829) (p 3019) (p 3093) (p 3266) (p 3343) (p 3516) (p 3543) (p 3918) (p 4337) (p 4697) (p 4793) (derived105438 p h) (derived95280 p h) (derived96376 p h)

theorem derived113667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 4194) ∨ (¬ p 4112) :=
  ElevenRUP.step113667 (p 2295) (p 4112) (p 4156) (p 4194) (h 29696) (derived96453 p h)

theorem derived113668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2995) ∨ (¬ p 4336) :=
  ElevenRUP.step113668 (p 2295) (p 2995) (p 4156) (p 4336) (h 23993) (derived96453 p h)

theorem derived113669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2996) ∨ (¬ p 2641) :=
  ElevenRUP.step113669 (p 2295) (p 2641) (p 2996) (p 4156) (derived86139 p h) (derived96453 p h)

theorem derived113670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2797) ∨ (p 2685) :=
  ElevenRUP.step113670 (p 2295) (p 2685) (p 2797) (p 4156) (derived87125 p h) (derived96453 p h)

theorem derived113671 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2807) ∨ (¬ p 2331) :=
  ElevenRUP.step113671 (p 2295) (p 2331) (p 2807) (p 4156) (derived90826 p h) (derived96453 p h)

theorem derived113672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3931) ∨ (¬ p 4260) ∨ (p 2668) :=
  ElevenRUP.step113672 (p 2295) (p 2668) (p 3931) (p 4156) (p 4260) (derived90833 p h) (derived96453 p h)

theorem derived113673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2449) ∨ (p 2668) ∨ (p 2396) :=
  ElevenRUP.step113673 (p 2295) (p 2396) (p 2449) (p 2668) (p 4156) (derived90839 p h) (derived96453 p h)

theorem derived113676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2449) ∨ (p 2553) ∨ (p 2396) :=
  ElevenRUP.step113676 (p 2295) (p 2396) (p 2449) (p 2553) (p 4156) (p 4976) (derived105465 p h) (derived86510 p h) (derived96453 p h)

theorem derived113677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2449) ∨ (p 2396) ∨ (p 2122) :=
  ElevenRUP.step113677 (p 2122) (p 2295) (p 2396) (p 2449) (p 4156) (p 4843) (derived105449 p h) (derived86531 p h) (derived96453 p h)

theorem derived113678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2264) ∨ (p 2177) ∨ (p 2307) :=
  ElevenRUP.step113678 (p 2177) (p 2264) (p 2295) (p 2307) (p 4156) (p 4581) (derived105405 p h) (derived90825 p h) (derived96453 p h)

theorem derived113679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (¬ p 4140) ∨ (p 2881) ∨ (¬ p 2264) :=
  ElevenRUP.step113679 (p 2264) (p 2295) (p 2881) (p 3323) (p 4140) (p 4156) (derived107313 p h) (derived96453 p h)

theorem derived113680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (¬ p 2241) ∨ (p 2177) ∨ (¬ p 2264) :=
  ElevenRUP.step113680 (p 2177) (p 2241) (p 2264) (p 2295) (p 2641) (p 4156) (derived90836 p h) (derived96453 p h)

theorem derived113683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3631) ∨ (¬ p 2449) ∨ (¬ p 3547) ∨ (p 2274) :=
  ElevenRUP.step113683 (p 2274) (p 2295) (p 2449) (p 3547) (p 3631) (p 4156) (derived91726 p h) (derived96453 p h)

theorem derived113684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2797) ∨ (p 2177) ∨ (¬ p 2264) ∨ (p 2630) :=
  ElevenRUP.step113684 (p 2177) (p 2264) (p 2295) (p 2630) (p 2797) (p 4156) (derived92159 p h) (derived96453 p h)

theorem derived113685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2797) ∨ (¬ p 2264) ∨ (p 2177) ∨ (¬ p 2737) :=
  ElevenRUP.step113685 (p 2177) (p 2264) (p 2295) (p 2737) (p 2797) (p 4156) (derived92207 p h) (derived96453 p h)

theorem derived113687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 4328) ∨ (¬ p 2264) ∨ (p 2696) ∨ (p 2177) ∨ (¬ p 2774) :=
  ElevenRUP.step113687 (p 2177) (p 2264) (p 2295) (p 2696) (p 2774) (p 4156) (p 4328) (derived76187 p h) (derived96453 p h)

theorem derived113693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2246) ∨ (p 2177) ∨ (¬ p 2264) ∨ (¬ p 2331) ∨ (p 2992) :=
  ElevenRUP.step113693 (p 2177) (p 2246) (p 2264) (p 2295) (p 2331) (p 2992) (p 4156) (derived82381 p h) (derived96453 p h)

theorem derived113698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (¬ p 3654) ∨ (p 2177) ∨ (¬ p 2264) ∨ (¬ p 2962) :=
  ElevenRUP.step113698 (p 2177) (p 2264) (p 2295) (p 2962) (p 3323) (p 3654) (p 4156) (derived90930 p h) (derived96453 p h)

theorem derived113700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2797) ∨ (¬ p 2396) ∨ (¬ p 2341) ∨ (p 2177) ∨ (¬ p 4066) :=
  ElevenRUP.step113700 (p 2177) (p 2295) (p 2341) (p 2396) (p 2797) (p 4066) (p 4156) (derived101375 p h) (derived96453 p h)

theorem derived113720 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3537) ∨ (¬ p 2331) ∨ (p 2177) ∨ (¬ p 2264) ∨ (¬ p 4477) ∨ (p 2707) ∨ (p 2098) ∨ (¬ p 3873) :=
  ElevenRUP.step113720 (p 2098) (p 2177) (p 2248) (p 2264) (p 2295) (p 2331) (p 2707) (p 3537) (p 3873) (p 4156) (p 4477) (derived105365 p h) (derived88383 p h) (derived96453 p h)

theorem derived113721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2264) ∨ (¬ p 2331) ∨ (¬ p 3873) ∨ (p 2177) ∨ (¬ p 4477) ∨ (p 2598) ∨ (¬ p 3367) ∨ (p 2707) :=
  ElevenRUP.step113721 (p 2177) (p 2248) (p 2264) (p 2295) (p 2331) (p 2598) (p 2707) (p 3367) (p 3873) (p 4156) (p 4477) (derived105365 p h) (derived88459 p h) (derived96453 p h)

theorem derived113727 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 4041) :=
  ElevenRUP.step113727 (p 3083) (p 4041) (p 4437) (derived106487 p h) (derived93397 p h)

theorem derived113728 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2528) ∨ (¬ p 3256) :=
  ElevenRUP.step113728 (p 2528) (p 3083) (p 3256) (p 4437) (h 25758) (derived93397 p h)

theorem derived113730 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2481) ∨ (¬ p 3256) ∨ (p 2088) :=
  ElevenRUP.step113730 (p 2088) (p 2481) (p 3083) (p 3256) (p 4437) (derived76913 p h) (derived93397 p h)

theorem derived113731 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3166) ∨ (¬ p 2470) ∨ (¬ p 2663) :=
  ElevenRUP.step113731 (p 2470) (p 2663) (p 3083) (p 3166) (p 4437) (derived87337 p h) (derived93397 p h)

theorem derived113732 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 3878) ∨ (¬ p 4355) ∨ (p 2440) :=
  ElevenRUP.step113732 (p 2440) (p 3083) (p 3878) (p 4355) (p 4437) (derived93674 p h) (derived93397 p h)

theorem derived113735 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3166) ∨ (¬ p 2651) ∨ (¬ p 3641) :=
  ElevenRUP.step113735 (p 2651) (p 3083) (p 3166) (p 3641) (p 4437) (p 4753) (derived105514 p h) (derived77420 p h) (derived93397 p h)

theorem derived113736 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3189) ∨ (¬ p 3641) ∨ (¬ p 2727) :=
  ElevenRUP.step113736 (p 2727) (p 3083) (p 3189) (p 3641) (p 4437) (p 4753) (derived105514 p h) (derived77424 p h) (derived93397 p h)

theorem derived113738 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (p 3166) ∨ (¬ p 4432) :=
  ElevenRUP.step113738 (p 2295) (p 2331) (p 3083) (p 3166) (p 4432) (p 4437) (derived79335 p h) (derived93397 p h)

theorem derived113739 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2518) ∨ (p 3166) ∨ (¬ p 2651) :=
  ElevenRUP.step113739 (p 2518) (p 2651) (p 3083) (p 3166) (p 4437) (p 4814) (derived105440 p h) (derived81502 p h) (derived93397 p h)

theorem derived113740 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3189) ∨ (p 2528) ∨ (p 2651) ∨ (¬ p 2727) :=
  ElevenRUP.step113740 (p 2528) (p 2651) (p 2727) (p 3083) (p 3189) (p 4437) (derived82192 p h) (derived93397 p h)

theorem derived113741 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3189) ∨ (¬ p 2470) ∨ (¬ p 2727) :=
  ElevenRUP.step113741 (p 2470) (p 2665) (p 2727) (p 3083) (p 3189) (p 4437) (derived105373 p h) (derived82288 p h) (derived93397 p h)

theorem derived113743 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3189) ∨ (¬ p 2727) ∨ (p 2440) :=
  ElevenRUP.step113743 (p 2440) (p 2727) (p 3083) (p 3189) (p 4437) (p 4608) (derived105540 p h) (derived82311 p h) (derived93397 p h)

theorem derived113744 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3005) ∨ (p 2528) ∨ (¬ p 2630) ∨ (p 2651) :=
  ElevenRUP.step113744 (p 2528) (p 2630) (p 2651) (p 3005) (p 3083) (p 4437) (derived86946 p h) (derived93397 p h)

theorem derived113745 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3005) ∨ (¬ p 2470) ∨ (¬ p 2630) :=
  ElevenRUP.step113745 (p 2470) (p 2630) (p 2665) (p 3005) (p 3083) (p 4437) (derived105373 p h) (derived87067 p h) (derived93397 p h)

theorem derived113748 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3166) ∨ (p 2528) ∨ (p 2727) ∨ (¬ p 2651) :=
  ElevenRUP.step113748 (p 2528) (p 2651) (p 2727) (p 3083) (p 3166) (p 4437) (derived100206 p h) (derived93397 p h)

theorem derived113749 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3166) ∨ (p 2630) ∨ (¬ p 2651) ∨ (p 2528) :=
  ElevenRUP.step113749 (p 2528) (p 2630) (p 2651) (p 3083) (p 3166) (p 4437) (derived100570 p h) (derived93397 p h)

theorem derived113759 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 4355) ∨ (p 3146) ∨ (¬ p 3256) ∨ (p 2563) :=
  ElevenRUP.step113759 (p 2563) (p 3083) (p 3146) (p 3256) (p 4355) (p 4437) (p 4509) (derived105392 p h) (derived93677 p h) (derived93397 p h)

theorem derived113760 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 4149) ∨ (p 3005) ∨ (¬ p 4236) ∨ (p 2651) ∨ (¬ p 2630) :=
  ElevenRUP.step113760 (p 2630) (p 2651) (p 3005) (p 3083) (p 4149) (p 4236) (p 4437) (derived93877 p h) (derived93397 p h)

theorem derived113772 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3286) ∨ (¬ p 2088) ∨ (¬ p 3755) ∨ (p 2459) ∨ (¬ p 4438) ∨ (p 3005) :=
  ElevenRUP.step113772 (p 2088) (p 2459) (p 3005) (p 3083) (p 3286) (p 3755) (p 4437) (p 4438) (derived109990 p h) (derived93397 p h)

theorem derived113780 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2774) ∨ (p 2651) ∨ (¬ p 4438) ∨ (¬ p 2727) ∨ (p 3189) ∨ (¬ p 2245) ∨ (¬ p 2177) ∨ (¬ p 2122) :=
  ElevenRUP.step113780 (p 2122) (p 2177) (p 2245) (p 2651) (p 2727) (p 2774) (p 3083) (p 3189) (p 4437) (p 4438) (p 4733) (derived105430 p h) (derived82303 p h) (derived93397 p h)

theorem derived113782 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 3166) ∨ (¬ p 3125) ∨ (¬ p 2192) ∨ (p 3367) ∨ (¬ p 2132) ∨ (p 2528) ∨ (¬ p 2663) ∨ (¬ p 3363) ∨ (¬ p 4418) :=
  ElevenRUP.step113782 (p 2132) (p 2192) (p 2528) (p 2663) (p 3083) (p 3125) (p 3166) (p 3363) (p 3367) (p 4330) (p 4418) (p 4437) (derived106329 p h) (derived75603 p h) (derived93397 p h)

theorem derived113787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3461) ∨ (¬ p 2761) :=
  ElevenRUP.step113787 (p 2396) (p 2761) (p 3461) (p 4623) (derived82504 p h) (derived91159 p h)

theorem derived113788 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3564) ∨ (¬ p 3581) ∨ (p 2417) :=
  ElevenRUP.step113788 (p 2396) (p 2417) (p 3564) (p 3581) (p 4623) (h 19717) (derived91159 p h)

theorem derived113789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3246) ∨ (¬ p 4204) ∨ (¬ p 3125) :=
  ElevenRUP.step113789 (p 2396) (p 3125) (p 3246) (p 4204) (p 4623) (derived84095 p h) (derived91159 p h)

theorem derived113792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3125) ∨ (p 2274) ∨ (¬ p 2761) ∨ (¬ p 2307) :=
  ElevenRUP.step113792 (p 2274) (p 2307) (p 2396) (p 2761) (p 3125) (p 4623) (derived78409 p h) (derived91159 p h)

theorem derived113794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3564) ∨ (p 2274) ∨ (p 2449) ∨ (¬ p 3096) :=
  ElevenRUP.step113794 (p 2274) (p 2396) (p 2449) (p 3096) (p 3564) (p 4623) (derived79518 p h) (derived91159 p h)

theorem derived113795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3246) ∨ (¬ p 2881) ∨ (¬ p 3266) ∨ (p 3461) :=
  ElevenRUP.step113795 (p 2396) (p 2881) (p 3246) (p 3266) (p 3461) (p 4623) (derived82486 p h) (derived91159 p h)

theorem derived113796 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3125) ∨ (p 2417) ∨ (p 2274) :=
  ElevenRUP.step113796 (p 2274) (p 2396) (p 2417) (p 3125) (p 4276) (p 4623) (derived105516 p h) (derived84083 p h) (derived91159 p h)

theorem derived113799 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3319) ∨ (¬ p 3923) ∨ (¬ p 2761) ∨ (p 3266) :=
  ElevenRUP.step113799 (p 2396) (p 2761) (p 3266) (p 3319) (p 3923) (p 4623) (derived84196 p h) (derived91159 p h)

theorem derived113800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3434) ∨ (p 2295) ∨ (¬ p 3323) ∨ (¬ p 4473) :=
  ElevenRUP.step113800 (p 2295) (p 2396) (p 3323) (p 3434) (p 4473) (p 4623) (derived88129 p h) (derived91159 p h)

theorem derived113801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3483) ∨ (p 2122) ∨ (p 3516) :=
  ElevenRUP.step113801 (p 2122) (p 2315) (p 2396) (p 3483) (p 3516) (p 4623) (derived105368 p h) (derived90236 p h) (derived91159 p h)

theorem derived113802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3654) ∨ (p 3246) ∨ (p 2307) :=
  ElevenRUP.step113802 (p 2307) (p 2396) (p 3246) (p 3654) (p 4556) (p 4623) (derived105399 p h) (derived90928 p h) (derived91159 p h)

theorem derived113803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3654) ∨ (p 2417) ∨ (p 2307) :=
  ElevenRUP.step113803 (p 2307) (p 2396) (p 2417) (p 3654) (p 4276) (p 4623) (derived105516 p h) (derived90931 p h) (derived91159 p h)

theorem derived113804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2307) ∨ (¬ p 2553) ∨ (¬ p 3654) ∨ (¬ p 2761) :=
  ElevenRUP.step113804 (p 2307) (p 2396) (p 2553) (p 2761) (p 3654) (p 4623) (derived90936 p h) (derived91159 p h)

theorem derived113806 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2553) ∨ (p 2177) ∨ (¬ p 3564) :=
  ElevenRUP.step113806 (p 2177) (p 2396) (p 2553) (p 3564) (p 4623) (p 4668) (derived105414 p h) (derived91287 p h) (derived91159 p h)

theorem derived113807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3654) ∨ (¬ p 2295) ∨ (p 2307) ∨ (¬ p 2761) :=
  ElevenRUP.step113807 (p 2295) (p 2307) (p 2396) (p 2761) (p 3654) (p 4623) (derived98297 p h) (derived91159 p h)

theorem derived113808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3323) ∨ (p 2295) ∨ (¬ p 2553) ∨ (¬ p 2761) :=
  ElevenRUP.step113808 (p 2295) (p 2396) (p 2553) (p 2761) (p 3323) (p 4623) (derived98640 p h) (derived91159 p h)

theorem derived113811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2459) ∨ (¬ p 3266) ∨ (p 3461) ∨ (¬ p 3146) :=
  ElevenRUP.step113811 (p 2396) (p 2459) (p 3146) (p 3266) (p 3461) (p 4623) (derived112689 p h) (derived91159 p h)

theorem derived113813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3791) ∨ (¬ p 3581) ∨ (¬ p 2274) ∨ (¬ p 5503) ∨ (¬ p 3564) :=
  ElevenRUP.step113813 (p 2274) (p 2396) (p 3564) (p 3581) (p 3791) (p 4623) (p 5503) (derived64988 p h) (derived91159 p h)

theorem derived113825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2459) ∨ (¬ p 3256) ∨ (p 3461) ∨ (¬ p 4041) ∨ (¬ p 3266) :=
  ElevenRUP.step113825 (p 2396) (p 2459) (p 3256) (p 3266) (p 3461) (p 4041) (p 4623) (derived112688 p h) (derived91159 p h)

theorem derived113829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2449) ∨ (¬ p 2264) ∨ (p 2307) ∨ (¬ p 2274) ∨ (¬ p 3319) ∨ (¬ p 3204) :=
  ElevenRUP.step113829 (p 2264) (p 2274) (p 2307) (p 2396) (p 2449) (p 3204) (p 3319) (p 4623) (derived84203 p h) (derived91159 p h)

theorem derived113834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3564) ∨ (p 2696) ∨ (¬ p 2307) ∨ (p 2553) ∨ (p 3005) ∨ (p 3256) ∨ (¬ p 3950) ∨ (¬ p 2781) :=
  ElevenRUP.step113834 (p 2307) (p 2396) (p 2553) (p 2696) (p 2781) (p 3005) (p 3256) (p 3564) (p 3950) (p 4623) (derived82863 p h) (derived91159 p h)

theorem derived113838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3323) ∨ (p 2132) ∨ (¬ p 2307) ∨ (p 3146) ∨ (p 2295) ∨ (p 2619) ∨ (¬ p 3366) ∨ (¬ p 5016) ∨ (¬ p 3950) :=
  ElevenRUP.step113838 (p 2132) (p 2295) (p 2307) (p 2396) (p 2619) (p 3146) (p 3323) (p 3366) (p 3950) (p 4623) (p 4866) (p 5016) (derived106063 p h) (derived84766 p h) (derived91159 p h)

theorem derived113840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3343) ∨ (p 2996) ∨ (¬ p 3266) ∨ (p 2651) ∨ (¬ p 2727) ∨ (p 3461) ∨ (¬ p 3286) ∨ (p 3631) ∨ (¬ p 4952) ∨ (¬ p 4450) :=
  ElevenRUP.step113840 (p 2396) (p 2651) (p 2727) (p 2996) (p 3266) (p 3286) (p 3343) (p 3461) (p 3631) (p 4450) (p 4623) (p 4952) (derived111286 p h) (derived91159 p h)

theorem derived113842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3256) ∨ (¬ p 3366) ∨ (p 2696) ∨ (¬ p 3125) ∨ (p 3005) ∨ (¬ p 2307) ∨ (p 2274) ∨ (¬ p 2962) ∨ (¬ p 3370) ∨ (¬ p 3950) :=
  ElevenRUP.step113842 (p 2274) (p 2307) (p 2396) (p 2696) (p 2962) (p 3005) (p 3125) (p 3256) (p 3366) (p 3370) (p 3950) (p 4377) (p 4623) (derived106170 p h) (derived78396 p h) (derived91159 p h)

theorem derived113845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 5284) ∨ (¬ p 3362) ∨ (¬ p 3266) ∨ (p 3286) ∨ (¬ p 2573) ∨ (p 3422) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (¬ p 3333) ∨ (¬ p 3950) ∨ (¬ p 4331) :=
  ElevenRUP.step113845 (p 2252) (p 2396) (p 2573) (p 2750) (p 2753) (p 3266) (p 3286) (p 3333) (p 3362) (p 3422) (p 3950) (p 4331) (p 4623) (p 5284) (derived106345 p h) (derived95634 p h) (derived91159 p h)

theorem derived113847 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 4404) ∨ (¬ p 2459) :=
  ElevenRUP.step113847 (p 2459) (p 2528) (p 4404) (p 4440) (derived112469 p h) (derived102553 p h)

theorem derived113848 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2088) ∨ (¬ p 2475) :=
  ElevenRUP.step113848 (p 2088) (p 2475) (p 2528) (p 4440) (derived112470 p h) (derived102553 p h)

theorem derived113849 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3032) ∨ (¬ p 4427) :=
  ElevenRUP.step113849 (p 2295) (p 3032) (p 3552) (p 4427) (h 32019) (derived96452 p h)

theorem derived113850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (p 2449) :=
  ElevenRUP.step113850 (p 2295) (p 2396) (p 2449) (p 3552) (h 6739) (derived96452 p h)

theorem derived113851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2177) ∨ (p 2264) :=
  ElevenRUP.step113851 (p 2177) (p 2264) (p 2295) (p 3552) (derived76676 p h) (derived96452 p h)

theorem derived113853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 4475) ∨ (¬ p 4325) :=
  ElevenRUP.step113853 (p 2295) (p 3552) (p 4325) (p 4475) (h 37091) (derived96452 p h)

theorem derived113854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2331) ∨ (p 2668) ∨ (¬ p 2807) :=
  ElevenRUP.step113854 (p 2295) (p 2331) (p 2668) (p 2807) (p 3552) (derived76668 p h) (derived96452 p h)

theorem derived113856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (p 2331) ∨ (¬ p 2807) :=
  ElevenRUP.step113856 (p 2295) (p 2331) (p 2807) (p 3323) (p 3552) (derived107112 p h) (derived96452 p h)

theorem derived113857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (¬ p 2685) ∨ (p 2797) :=
  ElevenRUP.step113857 (p 2295) (p 2685) (p 2797) (p 3323) (p 3552) (derived107113 p h) (derived96452 p h)

theorem derived113858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2274) ∨ (p 2331) ∨ (¬ p 2807) :=
  ElevenRUP.step113858 (p 2274) (p 2295) (p 2331) (p 2807) (p 3552) (derived76674 p h) (derived96452 p h)

theorem derived113859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2996) ∨ (p 2274) ∨ (p 2641) :=
  ElevenRUP.step113859 (p 2274) (p 2295) (p 2641) (p 2996) (p 3552) (derived76680 p h) (derived96452 p h)

theorem derived113860 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (p 2641) ∨ (p 2996) :=
  ElevenRUP.step113860 (p 2295) (p 2641) (p 2996) (p 3323) (p 3552) (derived107131 p h) (derived96452 p h)

theorem derived113861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 4325) ∨ (¬ p 2177) ∨ (p 2717) :=
  ElevenRUP.step113861 (p 2177) (p 2295) (p 2717) (p 3552) (p 4325) (derived87517 p h) (derived96452 p h)

theorem derived113862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2685) ∨ (p 2797) ∨ (p 2553) :=
  ElevenRUP.step113862 (p 2295) (p 2553) (p 2685) (p 2797) (p 3552) (p 4976) (derived105465 p h) (derived76661 p h) (derived96452 p h)

theorem derived113863 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2331) ∨ (¬ p 2807) ∨ (p 2553) :=
  ElevenRUP.step113863 (p 2295) (p 2331) (p 2553) (p 2807) (p 3552) (p 4976) (derived105465 p h) (derived76662 p h) (derived96452 p h)

theorem derived113865 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2331) ∨ (p 2122) ∨ (¬ p 2807) :=
  ElevenRUP.step113865 (p 2122) (p 2295) (p 2331) (p 2807) (p 3552) (p 4843) (derived105449 p h) (derived76665 p h) (derived96452 p h)

theorem derived113866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3309) ∨ (p 2331) ∨ (¬ p 2807) ∨ (¬ p 4757) :=
  ElevenRUP.step113866 (p 2295) (p 2331) (p 2807) (p 3309) (p 3552) (p 4757) (derived76666 p h) (derived96452 p h)

theorem derived113867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2996) ∨ (p 2641) ∨ (p 2383) ∨ (¬ p 2667) :=
  ElevenRUP.step113867 (p 2295) (p 2383) (p 2641) (p 2667) (p 2996) (p 3552) (derived76670 p h) (derived96452 p h)

theorem derived113869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2996) ∨ (p 2553) ∨ (p 2641) :=
  ElevenRUP.step113869 (p 2295) (p 2553) (p 2641) (p 2996) (p 3552) (p 4976) (derived105465 p h) (derived76678 p h) (derived96452 p h)

theorem derived113870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2307) ∨ (p 2996) ∨ (p 2641) :=
  ElevenRUP.step113870 (p 2295) (p 2307) (p 2641) (p 2996) (p 3552) (p 4581) (derived105405 p h) (derived76681 p h) (derived96452 p h)

theorem derived113872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (¬ p 2651) ∨ (p 2727) ∨ (p 2996) :=
  ElevenRUP.step113872 (p 2295) (p 2553) (p 2651) (p 2727) (p 2996) (p 3552) (derived81975 p h) (derived96452 p h)

theorem derived113874 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2685) ∨ (¬ p 2459) ∨ (p 2797) ∨ (¬ p 2177) :=
  ElevenRUP.step113874 (p 2177) (p 2295) (p 2459) (p 2685) (p 2797) (p 3552) (derived88967 p h) (derived96452 p h)

theorem derived113875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2177) ∨ (¬ p 2685) ∨ (¬ p 2331) ∨ (p 2797) :=
  ElevenRUP.step113875 (p 2177) (p 2295) (p 2331) (p 2685) (p 2797) (p 3552) (derived89137 p h) (derived96452 p h)

theorem derived113879 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2122) ∨ (p 2641) ∨ (p 2996) :=
  ElevenRUP.step113879 (p 2122) (p 2295) (p 2641) (p 2996) (p 3552) (p 4843) (derived105449 p h) (derived97913 p h) (derived96452 p h)

theorem derived113880 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2383) ∨ (p 2307) ∨ (p 2264) :=
  ElevenRUP.step113880 (p 2264) (p 2295) (p 2307) (p 2383) (p 3552) (p 4133) (derived105712 p h) (derived98304 p h) (derived96452 p h)

theorem derived113886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2685) ∨ (¬ p 4117) ∨ (p 2274) ∨ (¬ p 2331) ∨ (p 2797) :=
  ElevenRUP.step113886 (p 2274) (p 2295) (p 2331) (p 2685) (p 2797) (p 3552) (p 4117) (derived100740 p h) (derived96452 p h)

theorem derived113887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3309) ∨ (p 2331) ∨ (¬ p 2807) ∨ (¬ p 4024) :=
  ElevenRUP.step113887 (p 2295) (p 2331) (p 2807) (p 3309) (p 3552) (p 4024) (p 4843) (derived105449 p h) (derived101122 p h) (derived96452 p h)

theorem derived113888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2449) ∨ (¬ p 5284) ∨ (¬ p 3276) ∨ (p 2352) ∨ (¬ p 4422) :=
  ElevenRUP.step113888 (p 2295) (p 2352) (p 2449) (p 3276) (p 3552) (p 4422) (p 5284) (derived110910 p h) (derived96452 p h)

theorem derived113889 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2449) ∨ (¬ p 3767) ∨ (¬ p 5284) ∨ (p 2383) ∨ (¬ p 4036) :=
  ElevenRUP.step113889 (p 2295) (p 2383) (p 2449) (p 3552) (p 3767) (p 4036) (p 5284) (derived110913 p h) (derived96452 p h)

theorem derived113899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2122) ∨ (¬ p 2717) ∨ (p 2341) ∨ (¬ p 4401) ∨ (p 2274) ∨ (¬ p 4155) :=
  ElevenRUP.step113899 (p 2122) (p 2274) (p 2295) (p 2341) (p 2717) (p 3552) (p 4155) (p 4401) (derived111341 p h) (derived96452 p h)

theorem derived113906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2417) ∨ (¬ p 2396) ∨ (p 3670) ∨ (p 3367) ∨ (p 2996) ∨ (¬ p 2696) ∨ (¬ p 3276) ∨ (¬ p 2742) ∨ (¬ p 5158) :=
  ElevenRUP.step113906 (p 2295) (p 2396) (p 2417) (p 2696) (p 2742) (p 2996) (p 3276) (p 3367) (p 3552) (p 3670) (p 5158) (derived112994 p h) (derived96452 p h)

theorem derived113908 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2264) ∨ (p 2307) ∨ (¬ p 2210) ∨ (p 2459) ∨ (p 2608) ∨ (¬ p 2252) ∨ (¬ p 2972) ∨ (¬ p 3983) ∨ (¬ p 4450) :=
  ElevenRUP.step113908 (p 2210) (p 2252) (p 2264) (p 2295) (p 2307) (p 2459) (p 2608) (p 2750) (p 2972) (p 3552) (p 3983) (p 4450) (derived106345 p h) (derived91867 p h) (derived96452 p h)

theorem derived113911 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 3917) ∨ (p 3323) :=
  ElevenRUP.step113911 (p 2797) (p 3323) (p 3917) (p 4337) (derived93205 p h) (derived90912 p h)

theorem derived113912 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2668) ∨ (¬ p 2819) :=
  ElevenRUP.step113912 (p 2668) (p 2797) (p 2819) (p 4337) (derived98593 p h) (derived90912 p h)

theorem derived113913 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2295) ∨ (¬ p 2122) :=
  ElevenRUP.step113913 (p 2122) (p 2295) (p 2797) (p 4337) (derived98653 p h) (derived90912 p h)

theorem derived113915 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2331) ∨ (¬ p 4117) ∨ (p 2774) :=
  ElevenRUP.step113915 (p 2331) (p 2774) (p 2797) (p 4117) (p 4337) (derived100759 p h) (derived90912 p h)

theorem derived113917 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 3461) ∨ (p 2774) ∨ (¬ p 2696) ∨ (p 3323) :=
  ElevenRUP.step113917 (p 2696) (p 2774) (p 2797) (p 3323) (p 3461) (p 4337) (derived86366 p h) (derived90912 p h)

theorem derived113918 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2696) ∨ (¬ p 2641) ∨ (p 2774) :=
  ElevenRUP.step113918 (p 2641) (p 2696) (p 2751) (p 2774) (p 2797) (p 4337) (derived106343 p h) (derived86408 p h) (derived90912 p h)

theorem derived113919 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2727) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (p 2774) :=
  ElevenRUP.step113919 (p 2696) (p 2727) (p 2742) (p 2774) (p 2797) (p 4337) (derived107281 p h) (derived90912 p h)

theorem derived113921 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2098) ∨ (p 2727) ∨ (p 2774) ∨ (¬ p 2641) :=
  ElevenRUP.step113921 (p 2098) (p 2641) (p 2727) (p 2774) (p 2797) (p 4337) (derived86421 p h) (derived90912 p h)

theorem derived113922 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2295) ∨ (p 2774) ∨ (¬ p 2274) ∨ (¬ p 2696) :=
  ElevenRUP.step113922 (p 2274) (p 2295) (p 2696) (p 2774) (p 2797) (p 4337) (derived86454 p h) (derived90912 p h)

theorem derived113924 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2829) ∨ (p 2668) ∨ (¬ p 2737) ∨ (p 2363) :=
  ElevenRUP.step113924 (p 2363) (p 2668) (p 2737) (p 2797) (p 2829) (p 4337) (derived90467 p h) (derived90912 p h)

theorem derived113926 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2295) ∨ (¬ p 2737) ∨ (¬ p 2274) ∨ (p 2829) :=
  ElevenRUP.step113926 (p 2274) (p 2295) (p 2737) (p 2797) (p 2829) (p 4337) (derived90522 p h) (derived90912 p h)

theorem derived113927 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 4393) ∨ (p 3323) ∨ (p 2563) ∨ (¬ p 3914) :=
  ElevenRUP.step113927 (p 2563) (p 2797) (p 3323) (p 3914) (p 4337) (p 4393) (derived96103 p h) (derived90912 p h)

theorem derived113929 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2829) ∨ (¬ p 2331) ∨ (¬ p 2737) :=
  ElevenRUP.step113929 (p 2331) (p 2737) (p 2797) (p 2829) (p 4337) (p 4790) (derived106424 p h) (derived100391 p h) (derived90912 p h)

theorem derived113932 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2829) ∨ (p 2295) ∨ (¬ p 3873) ∨ (p 2696) ∨ (¬ p 2737) :=
  ElevenRUP.step113932 (p 2295) (p 2696) (p 2737) (p 2797) (p 2829) (p 3873) (p 4337) (derived90528 p h) (derived90912 p h)

theorem derived113933 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2619) ∨ (¬ p 3745) ∨ (¬ p 2132) ∨ (p 2774) :=
  ElevenRUP.step113933 (p 2132) (p 2619) (p 2774) (p 2797) (p 3745) (p 4337) (p 4509) (derived105392 p h) (derived90635 p h) (derived90912 p h)

theorem derived113939 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2829) ∨ (p 4435) ∨ (¬ p 5514) ∨ (¬ p 3019) ∨ (¬ p 2440) :=
  ElevenRUP.step113939 (p 2440) (p 2797) (p 2829) (p 3019) (p 4337) (p 4435) (p 5514) (derived113630 p h) (derived90912 p h)

theorem derived113947 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 3323) ∨ (¬ p 3631) ∨ (¬ p 5284) ∨ (¬ p 3707) ∨ (¬ p 2427) ∨ (¬ p 4909) ∨ (¬ p 2819) :=
  ElevenRUP.step113947 (p 2427) (p 2797) (p 2819) (p 3323) (p 3631) (p 3707) (p 4337) (p 4909) (p 5284) (derived111016 p h) (derived90912 p h)

theorem derived113960 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2829) ∨ (¬ p 3516) ∨ (p 3343) ∨ (¬ p 3543) ∨ (¬ p 4697) ∨ (¬ p 2761) ∨ (p 3266) ∨ (¬ p 2608) ∨ (¬ p 3019) ∨ (p 3093) :=
  ElevenRUP.step113960 (p 2608) (p 2761) (p 2797) (p 2829) (p 3019) (p 3093) (p 3266) (p 3343) (p 3516) (p 3543) (p 4337) (p 4697) (derived113663 p h) (derived90912 p h)

theorem derived113971 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2807) ∨ (p 2651) :=
  ElevenRUP.step113971 (p 2437) (p 2651) (p 2807) (p 4112) (derived74850 p h) (derived96077 p h)

theorem derived113972 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2996) ∨ (p 2727) :=
  ElevenRUP.step113972 (p 2437) (p 2727) (p 2996) (p 4112) (derived81952 p h) (derived96077 p h)

theorem derived113973 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2685) ∨ (p 2630) :=
  ElevenRUP.step113973 (p 2437) (p 2630) (p 2685) (p 4112) (derived87500 p h) (derived96077 p h)

theorem derived113974 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2295) ∨ (p 4194) :=
  ElevenRUP.step113974 (p 2295) (p 2437) (p 4112) (p 4194) (derived113667 p h) (derived96077 p h)

theorem derived113975 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3016) ∨ (¬ p 3920) ∨ (¬ p 3740) :=
  ElevenRUP.step113975 (p 2437) (p 3016) (p 3740) (p 3920) (p 4112) (h 25297) (derived96077 p h)

theorem derived113979 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2417) ∨ (p 2449) ∨ (p 2440) :=
  ElevenRUP.step113979 (p 2417) (p 2437) (p 2440) (p 2449) (p 4112) (p 4644) (derived105411 p h) (derived74555 p h) (derived96077 p h)

theorem derived113980 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2911) ∨ (p 2264) ∨ (p 2440) :=
  ElevenRUP.step113980 (p 2264) (p 2437) (p 2440) (p 2911) (p 4112) (p 4644) (derived105411 p h) (derived74565 p h) (derived96077 p h)

theorem derived113982 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3389) ∨ (¬ p 2911) ∨ (p 2264) :=
  ElevenRUP.step113982 (p 2264) (p 2437) (p 2665) (p 2911) (p 3389) (p 4112) (derived105373 p h) (derived74852 p h) (derived96077 p h)

theorem derived113983 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 4391) ∨ (¬ p 3868) ∨ (¬ p 3389) :=
  ElevenRUP.step113983 (p 2437) (p 2665) (p 3389) (p 3868) (p 4112) (p 4391) (derived105373 p h) (derived49144 p h) (derived96077 p h)

theorem derived113984 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2417) ∨ (p 2449) ∨ (¬ p 3389) :=
  ElevenRUP.step113984 (p 2417) (p 2437) (p 2449) (p 2665) (p 3389) (p 4112) (derived105373 p h) (derived74853 p h) (derived96077 p h)

theorem derived113985 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3038) ∨ (p 2264) ∨ (¬ p 3527) ∨ (p 2992) :=
  ElevenRUP.step113985 (p 2264) (p 2437) (p 2992) (p 3038) (p 3527) (p 4112) (derived76747 p h) (derived96077 p h)

theorem derived113986 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2911) ∨ (p 2264) ∨ (¬ p 3201) :=
  ElevenRUP.step113986 (p 2264) (p 2437) (p 2911) (p 3201) (p 4112) (p 4753) (derived105514 p h) (derived77171 p h) (derived96077 p h)

theorem derived113987 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2449) ∨ (¬ p 2417) ∨ (¬ p 3201) :=
  ElevenRUP.step113987 (p 2417) (p 2437) (p 2449) (p 3201) (p 4112) (p 4753) (derived105514 p h) (derived77228 p h) (derived96077 p h)

theorem derived113988 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 4391) ∨ (¬ p 4129) ∨ (p 2373) ∨ (¬ p 2427) :=
  ElevenRUP.step113988 (p 2373) (p 2427) (p 2437) (p 4112) (p 4129) (p 4391) (derived80282 p h) (derived96077 p h)

theorem derived113989 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2922) ∨ (¬ p 2911) ∨ (p 2264) :=
  ElevenRUP.step113989 (p 2264) (p 2437) (p 2911) (p 2922) (p 4112) (p 4814) (derived105440 p h) (derived88854 p h) (derived96077 p h)

theorem derived113990 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3631) ∨ (¬ p 3038) ∨ (p 2449) ∨ (p 2992) :=
  ElevenRUP.step113990 (p 2437) (p 2449) (p 2992) (p 3038) (p 3631) (p 4112) (derived89342 p h) (derived96077 p h)

theorem derived113994 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2177) ∨ (p 2573) ∨ (p 2264) ∨ (¬ p 3016) :=
  ElevenRUP.step113994 (p 2177) (p 2264) (p 2437) (p 2573) (p 3016) (p 4112) (derived99420 p h) (derived96077 p h)

theorem derived113995 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2417) ∨ (p 2449) ∨ (p 2727) ∨ (p 2911) :=
  ElevenRUP.step113995 (p 2417) (p 2437) (p 2449) (p 2727) (p 2911) (p 4112) (derived100130 p h) (derived96077 p h)

theorem derived113996 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3434) ∨ (¬ p 2707) ∨ (p 2737) ∨ (p 2449) :=
  ElevenRUP.step113996 (p 2437) (p 2449) (p 2707) (p 2737) (p 3434) (p 4112) (derived100180 p h) (derived96077 p h)

theorem derived113998 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2341) ∨ (¬ p 2911) ∨ (¬ p 4155) ∨ (p 2440) :=
  ElevenRUP.step113998 (p 2341) (p 2437) (p 2440) (p 2911) (p 4112) (p 4155) (p 4644) (derived105411 p h) (derived74586 p h) (derived96077 p h)

theorem derived114006 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2417) ∨ (¬ p 2850) ∨ (p 2449) ∨ (¬ p 3741) :=
  ElevenRUP.step114006 (p 2417) (p 2437) (p 2449) (p 2850) (p 3741) (p 4112) (p 4753) (derived105514 p h) (derived87874 p h) (derived96077 p h)

theorem derived114009 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 4391) ∨ (¬ p 3868) ∨ (¬ p 3016) ∨ (¬ p 3741) :=
  ElevenRUP.step114009 (p 2437) (p 3016) (p 3741) (p 3868) (p 4112) (p 4391) (p 4717) (derived105424 p h) (derived61630 p h) (derived96077 p h)

theorem derived114010 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2911) ∨ (p 2573) ∨ (p 2264) ∨ (¬ p 3016) ∨ (¬ p 2655) :=
  ElevenRUP.step114010 (p 2264) (p 2437) (p 2573) (p 2655) (p 2911) (p 3016) (p 4112) (derived99338 p h) (derived96077 p h)

theorem derived114012 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2417) ∨ (p 2449) ∨ (¬ p 3016) ∨ (¬ p 3741) :=
  ElevenRUP.step114012 (p 2417) (p 2437) (p 2449) (p 3016) (p 3741) (p 4112) (p 4717) (derived105424 p h) (derived100124 p h) (derived96077 p h)

theorem derived114014 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2553) ∨ (¬ p 2417) ∨ (¬ p 4155) ∨ (p 3516) ∨ (¬ p 3016) :=
  ElevenRUP.step114014 (p 2417) (p 2437) (p 2553) (p 3016) (p 3516) (p 4112) (p 4155) (derived109154 p h) (derived96077 p h)

theorem derived114023 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 4988) ∨ (¬ p 2341) ∨ (p 2264) ∨ (¬ p 3016) ∨ (¬ p 4109) :=
  ElevenRUP.step114023 (p 2264) (p 2341) (p 2437) (p 3016) (p 4109) (p 4112) (p 4717) (p 4988) (derived105424 p h) (derived94478 p h) (derived96077 p h)

theorem derived114025 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2264) ∨ (¬ p 2341) ∨ (¬ p 3016) ∨ (¬ p 4104) ∨ (¬ p 2811) ∨ (¬ p 2737) :=
  ElevenRUP.step114025 (p 2264) (p 2341) (p 2437) (p 2737) (p 2811) (p 3016) (p 4104) (p 4112) (derived99449 p h) (derived96077 p h)

theorem derived114031 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2220) ∨ (p 3146) ∨ (¬ p 3016) ∨ (¬ p 3399) ∨ (p 3266) ∨ (¬ p 4075) ∨ (¬ p 4391) :=
  ElevenRUP.step114031 (p 2220) (p 2437) (p 3016) (p 3146) (p 3266) (p 3399) (p 4075) (p 4112) (p 4391) (derived97254 p h) (derived96077 p h)

theorem derived114034 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (¬ p 2737) ∨ (p 2598) :=
  ElevenRUP.step114034 (p 2598) (p 2707) (p 2737) (p 3425) (p 4400) (derived113569 p h) (derived96392 p h)

theorem derived114036 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 2774) ∨ (¬ p 2737) ∨ (¬ p 4842) :=
  ElevenRUP.step114036 (p 2707) (p 2737) (p 2774) (p 3425) (p 4400) (p 4842) (derived113568 p h) (derived96392 p h)

theorem derived114038 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 4881) :=
  ElevenRUP.step114038 (p 2630) (p 3364) (p 4881) (derived67309 p h) (derived88126 p h)

theorem derived114039 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2737) ∨ (¬ p 3367) :=
  ElevenRUP.step114039 (p 2630) (p 2737) (p 3364) (p 3367) (derived81274 p h) (derived88126 p h)

theorem derived114040 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (p 2737) :=
  ElevenRUP.step114040 (p 2598) (p 2630) (p 2737) (p 2753) (p 3364) (derived81283 p h) (derived88126 p h)

theorem derived114041 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3362) ∨ (¬ p 3363) ∨ (p 2696) :=
  ElevenRUP.step114041 (p 2630) (p 2696) (p 3362) (p 3363) (p 3364) (derived82871 p h) (derived88126 p h)

theorem derived114042 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2437) ∨ (p 3201) ∨ (¬ p 3136) :=
  ElevenRUP.step114042 (p 2437) (p 2630) (p 3136) (p 3201) (p 3364) (derived84388 p h) (derived88126 p h)

theorem derived114043 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3641) ∨ (¬ p 3083) ∨ (¬ p 3136) :=
  ElevenRUP.step114043 (p 2630) (p 3083) (p 3136) (p 3364) (p 3641) (derived97302 p h) (derived88126 p h)

theorem derived114044 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 5160) ∨ (¬ p 3343) ∨ (¬ p 3136) :=
  ElevenRUP.step114044 (p 2630) (p 3136) (p 3343) (p 3364) (p 5160) (derived99797 p h) (derived88126 p h)

theorem derived114045 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3422) ∨ (p 2437) ∨ (¬ p 3016) ∨ (p 2911) :=
  ElevenRUP.step114045 (p 2437) (p 2630) (p 2911) (p 3016) (p 3364) (p 3422) (derived75118 p h) (derived88126 p h)

theorem derived114046 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3136) ∨ (p 2946) ∨ (¬ p 3367) ∨ (¬ p 4236) :=
  ElevenRUP.step114046 (p 2630) (p 2946) (p 3136) (p 3364) (p 3367) (p 4236) (derived84320 p h) (derived88126 p h)

theorem derived114047 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3016) ∨ (¬ p 3136) ∨ (p 2946) ∨ (p 3422) :=
  ElevenRUP.step114047 (p 2630) (p 2946) (p 3016) (p 3136) (p 3364) (p 3422) (derived84321 p h) (derived88126 p h)

theorem derived114049 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3201) ∨ (¬ p 2437) ∨ (¬ p 2651) :=
  ElevenRUP.step114049 (p 2437) (p 2630) (p 2651) (p 3201) (p 3364) (p 4790) (derived106424 p h) (derived84432 p h) (derived88126 p h)

theorem derived114050 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2850) ∨ (¬ p 2651) ∨ (p 2440) :=
  ElevenRUP.step114050 (p 2440) (p 2630) (p 2651) (p 2850) (p 3364) (p 4790) (derived106424 p h) (derived84437 p h) (derived88126 p h)

theorem derived114052 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2797) ∨ (p 2850) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step114052 (p 2406) (p 2630) (p 2797) (p 2850) (p 3364) (p 3379) (derived91059 p h) (derived88126 p h)

theorem derived114054 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2518) ∨ (p 3641) ∨ (p 2839) ∨ (¬ p 3541) :=
  ElevenRUP.step114054 (p 2518) (p 2630) (p 2839) (p 3364) (p 3541) (p 3641) (derived99679 p h) (derived88126 p h)

theorem derived114055 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2573) ∨ (p 3422) ∨ (p 2132) ∨ (¬ p 3362) :=
  ElevenRUP.step114055 (p 2132) (p 2573) (p 2630) (p 3362) (p 3364) (p 3422) (derived99726 p h) (derived88126 p h)

theorem derived114056 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2470) ∨ (p 3641) ∨ (p 2132) ∨ (¬ p 3362) :=
  ElevenRUP.step114056 (p 2132) (p 2470) (p 2630) (p 3362) (p 3364) (p 3641) (derived99728 p h) (derived88126 p h)

theorem derived114057 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 5160) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (p 2132) :=
  ElevenRUP.step114057 (p 2132) (p 2630) (p 3355) (p 3362) (p 3364) (p 5160) (derived99796 p h) (derived88126 p h)

theorem derived114058 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 5160) ∨ (¬ p 2727) ∨ (¬ p 3343) :=
  ElevenRUP.step114058 (p 2630) (p 2727) (p 2751) (p 3343) (p 3364) (p 5160) (derived106343 p h) (derived41675 p h) (derived88126 p h)

theorem derived114059 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3422) ∨ (¬ p 2651) ∨ (¬ p 3016) :=
  ElevenRUP.step114059 (p 2630) (p 2651) (p 3016) (p 3364) (p 3422) (p 4790) (derived106424 p h) (derived101257 p h) (derived88126 p h)

theorem derived114062 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3201) ∨ (¬ p 2264) ∨ (p 2996) ∨ (p 2717) :=
  ElevenRUP.step114062 (p 2264) (p 2630) (p 2717) (p 2996) (p 3201) (p 3364) (derived111406 p h) (derived88126 p h)

theorem derived114063 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3146) ∨ (¬ p 4210) ∨ (p 2166) ∨ (p 2850) ∨ (p 3266) :=
  ElevenRUP.step114063 (p 2166) (p 2630) (p 2850) (p 3146) (p 3266) (p 3364) (p 4210) (derived76079 p h) (derived88126 p h)

theorem derived114065 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2518) ∨ (p 3641) ∨ (¬ p 4116) ∨ (¬ p 2651) :=
  ElevenRUP.step114065 (p 2518) (p 2630) (p 2651) (p 3364) (p 3641) (p 4116) (p 4790) (derived106424 p h) (derived81499 p h) (derived88126 p h)

theorem derived114066 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3363) ∨ (p 2573) ∨ (¬ p 2727) ∨ (¬ p 3016) :=
  ElevenRUP.step114066 (p 2573) (p 2630) (p 2727) (p 2751) (p 3016) (p 3363) (p 3364) (derived106343 p h) (derived82212 p h) (derived88126 p h)

theorem derived114067 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2850) ∨ (¬ p 2230) ∨ (¬ p 2656) ∨ (¬ p 2727) :=
  ElevenRUP.step114067 (p 2230) (p 2630) (p 2656) (p 2727) (p 2751) (p 2850) (p 3364) (derived106343 p h) (derived82298 p h) (derived88126 p h)

theorem derived114069 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2707) ∨ (¬ p 2406) ∨ (¬ p 3541) ∨ (p 2850) ∨ (¬ p 4778) :=
  ElevenRUP.step114069 (p 2406) (p 2630) (p 2707) (p 2850) (p 3364) (p 3541) (p 4778) (derived88295 p h) (derived88126 p h)

theorem derived114071 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3541) ∨ (¬ p 2406) ∨ (p 2850) ∨ (¬ p 2774) ∨ (p 2829) :=
  ElevenRUP.step114071 (p 2406) (p 2630) (p 2774) (p 2829) (p 2850) (p 3364) (p 3541) (derived90481 p h) (derived88126 p h)

theorem derived114073 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3422) ∨ (¬ p 2573) ∨ (¬ p 2727) ∨ (¬ p 2656) :=
  ElevenRUP.step114073 (p 2573) (p 2630) (p 2656) (p 2727) (p 2751) (p 3364) (p 3422) (derived106343 p h) (derived101450 p h) (derived88126 p h)

theorem derived114076 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2797) ∨ (p 2850) ∨ (¬ p 2230) ∨ (¬ p 2656) :=
  ElevenRUP.step114076 (p 2230) (p 2630) (p 2656) (p 2797) (p 2850) (p 3364) (p 4975) (derived105464 p h) (derived101831 p h) (derived88126 p h)

theorem derived114077 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3389) ∨ (p 3201) ∨ (¬ p 2656) ∨ (¬ p 2727) :=
  ElevenRUP.step114077 (p 2630) (p 2656) (p 2727) (p 2751) (p 3201) (p 3364) (p 3389) (derived106343 p h) (derived101840 p h) (derived88126 p h)

theorem derived114084 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2951) ∨ (p 3422) ∨ (¬ p 2573) ∨ (¬ p 3904) ∨ (¬ p 2992) :=
  ElevenRUP.step114084 (p 2573) (p 2630) (p 2751) (p 2951) (p 2992) (p 3364) (p 3422) (p 3904) (derived106343 p h) (derived94560 p h) (derived88126 p h)

theorem derived114104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2992) ∨ (p 2641) :=
  ElevenRUP.step114104 (p 2284) (p 2641) (p 2992) (p 4336) (derived81807 p h) (derived79172 p h)

theorem derived114105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3136) ∨ (p 2797) :=
  ElevenRUP.step114105 (p 2284) (p 2797) (p 3136) (p 4336) (derived84339 p h) (derived79172 p h)

theorem derived114106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2331) ∨ (¬ p 2946) :=
  ElevenRUP.step114106 (p 2284) (p 2331) (p 2946) (p 4336) (h 24463) (derived79172 p h)

theorem derived114107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 3019) ∨ (¬ p 3413) :=
  ElevenRUP.step114107 (p 2284) (p 3019) (p 3413) (p 4336) (h 23675) (derived79172 p h)

theorem derived114109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2295) ∨ (p 2995) :=
  ElevenRUP.step114109 (p 2284) (p 2295) (p 2995) (p 4336) (derived113668 p h) (derived79172 p h)

theorem derived114110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2295) ∨ (p 2901) ∨ (¬ p 4275) :=
  ElevenRUP.step114110 (p 2284) (p 2295) (p 2901) (p 4275) (p 4336) (derived78210 p h) (derived79172 p h)

theorem derived114111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2668) ∨ (¬ p 4506) ∨ (p 3156) :=
  ElevenRUP.step114111 (p 2284) (p 2668) (p 3156) (p 4336) (p 4506) (h 26917) (derived79172 p h)

theorem derived114114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2274) ∨ (¬ p 2187) ∨ (¬ p 2295) ∨ (¬ p 2946) :=
  ElevenRUP.step114114 (p 2187) (p 2274) (p 2284) (p 2295) (p 2946) (p 4336) (derived79409 p h) (derived79172 p h)

theorem derived114115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2187) ∨ (¬ p 2668) ∨ (p 2630) ∨ (¬ p 3136) :=
  ElevenRUP.step114115 (p 2187) (p 2284) (p 2630) (p 2668) (p 3136) (p 4336) (derived84314 p h) (derived79172 p h)

theorem derived114116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2992) ∨ (p 2727) ∨ (¬ p 2668) ∨ (p 2187) :=
  ElevenRUP.step114116 (p 2187) (p 2284) (p 2668) (p 2727) (p 2992) (p 4336) (derived85882 p h) (derived79172 p h)

theorem derived114117 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2992) ∨ (¬ p 2295) ∨ (p 2274) ∨ (p 2727) :=
  ElevenRUP.step114117 (p 2274) (p 2284) (p 2295) (p 2727) (p 2992) (p 4336) (derived85883 p h) (derived79172 p h)

theorem derived114118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 3125) ∨ (¬ p 3323) ∨ (¬ p 2187) ∨ (¬ p 2992) :=
  ElevenRUP.step114118 (p 2187) (p 2284) (p 2992) (p 3125) (p 3323) (p 4336) (derived85930 p h) (derived79172 p h)

theorem derived114121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3323) ∨ (p 3125) ∨ (p 2901) :=
  ElevenRUP.step114121 (p 2284) (p 2901) (p 3125) (p 3323) (p 4336) (p 4555) (derived105542 p h) (derived98775 p h) (derived79172 p h)

theorem derived114125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2274) ∨ (¬ p 2307) ∨ (¬ p 3567) ∨ (¬ p 3136) ∨ (¬ p 2187) :=
  ElevenRUP.step114125 (p 2187) (p 2274) (p 2284) (p 2307) (p 3136) (p 3567) (p 4336) (derived78392 p h) (derived79172 p h)

theorem derived114127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2785) ∨ (p 3156) ∨ (¬ p 2295) ∨ (p 2307) ∨ (¬ p 4185) :=
  ElevenRUP.step114127 (p 2284) (p 2295) (p 2307) (p 2785) (p 3156) (p 4185) (p 4336) (derived79086 p h) (derived79172 p h)

theorem derived114128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2563) ∨ (¬ p 2668) ∨ (¬ p 4356) ∨ (p 2383) :=
  ElevenRUP.step114128 (p 2284) (p 2383) (p 2563) (p 2668) (p 4336) (p 4356) (p 4705) (derived106238 p h) (derived79236 p h) (derived79172 p h)

theorem derived114132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2860) ∨ (¬ p 2295) ∨ (p 2307) ∨ (¬ p 4356) :=
  ElevenRUP.step114132 (p 2284) (p 2295) (p 2307) (p 2860) (p 4336) (p 4356) (p 4906) (derived105632 p h) (derived79412 p h) (derived79172 p h)

theorem derived114133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2295) ∨ (¬ p 4356) ∨ (p 2307) ∨ (p 2563) :=
  ElevenRUP.step114133 (p 2284) (p 2295) (p 2307) (p 2563) (p 4336) (p 4356) (p 4705) (derived106238 p h) (derived79414 p h) (derived79172 p h)

theorem derived114134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2860) ∨ (¬ p 2668) ∨ (p 2383) ∨ (¬ p 4356) :=
  ElevenRUP.step114134 (p 2284) (p 2383) (p 2668) (p 2860) (p 4336) (p 4356) (p 4906) (derived105632 p h) (derived83306 p h) (derived79172 p h)

theorem derived114137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2274) ∨ (¬ p 2307) ∨ (¬ p 3136) ∨ (p 2630) ∨ (¬ p 3567) :=
  ElevenRUP.step114137 (p 2274) (p 2284) (p 2307) (p 2630) (p 3136) (p 3567) (p 4336) (derived84312 p h) (derived79172 p h)

theorem derived114138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 3125) ∨ (¬ p 3323) ∨ (¬ p 4957) ∨ (p 2156) ∨ (¬ p 3645) :=
  ElevenRUP.step114138 (p 2156) (p 2284) (p 3125) (p 3323) (p 3645) (p 4336) (p 4957) (derived85495 p h) (derived79172 p h)

theorem derived114140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2563) ∨ (p 3654) ∨ (¬ p 4356) ∨ (¬ p 3323) :=
  ElevenRUP.step114140 (p 2284) (p 2563) (p 3323) (p 3654) (p 4336) (p 4356) (p 4705) (derived106238 p h) (derived90905 p h) (derived79172 p h)

theorem derived114141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 4228) ∨ (¬ p 4393) ∨ (p 2192) ∨ (¬ p 3747) ∨ (p 3156) :=
  ElevenRUP.step114141 (p 2192) (p 2284) (p 3156) (p 3747) (p 4228) (p 4336) (p 4393) (derived96109 p h) (derived79172 p h)

theorem derived114142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 4228) ∨ (¬ p 4393) ∨ (p 2156) ∨ (¬ p 3747) ∨ (p 3156) :=
  ElevenRUP.step114142 (p 2156) (p 2284) (p 3156) (p 3747) (p 4228) (p 4336) (p 4393) (derived96116 p h) (derived79172 p h)

theorem derived114154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 4781) ∨ (p 2797) ∨ (¬ p 2717) ∨ (p 2341) ∨ (¬ p 2662) ∨ (¬ p 5197) :=
  ElevenRUP.step114154 (p 2284) (p 2341) (p 2662) (p 2717) (p 2797) (p 4336) (p 4781) (p 5197) (derived94440 p h) (derived79172 p h)

theorem derived114170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2911) ∨ (p 2417) :=
  ElevenRUP.step114170 (p 2417) (p 2459) (p 2911) (p 3945) (h 6932) (derived92417 p h)

theorem derived114171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2396) ∨ (¬ p 2177) :=
  ElevenRUP.step114171 (p 2177) (p 2396) (p 2459) (p 3945) (h 15523) (derived92417 p h)

theorem derived114172 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 3246) ∨ (¬ p 2881) :=
  ElevenRUP.step114172 (p 2459) (p 2881) (p 3246) (p 3945) (h 23854) (derived92417 p h)

theorem derived114173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2449) ∨ (¬ p 2264) :=
  ElevenRUP.step114173 (p 2264) (p 2449) (p 2459) (p 3945) (derived100136 p h) (derived92417 p h)

theorem derived114174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3527) ∨ (p 3631) :=
  ElevenRUP.step114174 (p 2459) (p 3527) (p 3631) (p 3945) (derived101977 p h) (derived92417 p h)

theorem derived114175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (p 3434) :=
  ElevenRUP.step114175 (p 2459) (p 2717) (p 3434) (p 3945) (derived102152 p h) (derived92417 p h)

theorem derived114176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 3516) ∨ (¬ p 2341) :=
  ElevenRUP.step114176 (p 2341) (p 2459) (p 3516) (p 3945) (derived110099 p h) (derived92417 p h)

theorem derived114180 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2707) ∨ (¬ p 3527) ∨ (p 3434) :=
  ElevenRUP.step114180 (p 2459) (p 2707) (p 3434) (p 3527) (p 3945) (derived113557 p h) (derived92417 p h)

theorem derived114181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2761) ∨ (p 2528) ∨ (p 3266) :=
  ElevenRUP.step114181 (p 2459) (p 2528) (p 2761) (p 3266) (p 3945) (p 4420) (derived105707 p h) (derived79580 p h) (derived92417 p h)

theorem derived114182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2363) ∨ (¬ p 2761) ∨ (p 3266) :=
  ElevenRUP.step114182 (p 2363) (p 2459) (p 2761) (p 3266) (p 3945) (p 4133) (derived105712 p h) (derived79611 p h) (derived92417 p h)

theorem derived114185 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 3146) ∨ (¬ p 2761) ∨ (p 3266) :=
  ElevenRUP.step114185 (p 2459) (p 2761) (p 3146) (p 3266) (p 3945) (p 4902) (derived105456 p h) (derived98674 p h) (derived92417 p h)

theorem derived114188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2996) ∨ (¬ p 2641) ∨ (p 2449) ∨ (¬ p 2177) :=
  ElevenRUP.step114188 (p 2177) (p 2449) (p 2459) (p 2641) (p 2996) (p 3945) (derived99943 p h) (derived92417 p h)

theorem derived114193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 3631) ∨ (¬ p 3063) ∨ (p 3830) ∨ (¬ p 3093) :=
  ElevenRUP.step114193 (p 2459) (p 3063) (p 3093) (p 3631) (p 3830) (p 3945) (derived110533 p h) (derived92417 p h)

theorem derived114194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2449) ∨ (¬ p 5284) ∨ (¬ p 2177) ∨ (¬ p 2761) :=
  ElevenRUP.step114194 (p 2177) (p 2449) (p 2459) (p 2761) (p 3945) (p 5284) (derived110905 p h) (derived92417 p h)

theorem derived114199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3276) ∨ (p 3266) ∨ (¬ p 4636) ∨ (p 3146) :=
  ElevenRUP.step114199 (p 2459) (p 3146) (p 3266) (p 3276) (p 3945) (p 4636) (p 4902) (derived105456 p h) (derived79572 p h) (derived92417 p h)

theorem derived114213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2264) ∨ (p 2553) ∨ (¬ p 3073) ∨ (p 2573) ∨ (p 3256) ∨ (¬ p 3449) ∨ (p 2396) :=
  ElevenRUP.step114213 (p 2264) (p 2396) (p 2459) (p 2553) (p 2573) (p 3073) (p 3256) (p 3449) (p 3945) (derived112930 p h) (derived92417 p h)

theorem derived114227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2860) ∨ (¬ p 3276) ∨ (p 3266) ∨ (p 2829) ∨ (¬ p 2341) ∨ (p 3105) ∨ (p 2608) ∨ (¬ p 4636) ∨ (¬ p 5059) :=
  ElevenRUP.step114227 (p 2341) (p 2459) (p 2608) (p 2829) (p 2860) (p 3105) (p 3266) (p 3276) (p 3945) (p 4636) (p 5059) (derived113547 p h) (derived92417 p h)

theorem derived114228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3609) ∨ (¬ p 2774) ∨ (p 3367) ∨ (p 2807) ∨ (p 2363) ∨ (p 2449) ∨ (¬ p 2663) ∨ (¬ p 3363) ∨ (¬ p 4861) :=
  ElevenRUP.step114228 (p 2363) (p 2449) (p 2459) (p 2663) (p 2774) (p 2807) (p 3363) (p 3367) (p 3609) (p 3945) (p 4133) (p 4861) (derived105712 p h) (derived74994 p h) (derived92417 p h)

theorem derived114232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (p 2264) ∨ (p 3246) ∨ (¬ p 3005) ∨ (¬ p 2331) ∨ (p 2797) ∨ (p 2982) ∨ (p 3051) ∨ (¬ p 4117) ∨ (¬ p 3904) ∨ (¬ p 2427) :=
  ElevenRUP.step114232 (p 2264) (p 2331) (p 2427) (p 2459) (p 2797) (p 2982) (p 3005) (p 3051) (p 3246) (p 3904) (p 3945) (p 4117) (derived112960 p h) (derived92417 p h)

theorem derived114233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 4311) ∨ (p 2396) ∨ (p 2553) ∨ (p 2573) ∨ (p 3136) ∨ (¬ p 3005) ∨ (¬ p 2753) ∨ (¬ p 4117) ∨ (¬ p 3347) ∨ (¬ p 2946) :=
  ElevenRUP.step114233 (p 2396) (p 2459) (p 2553) (p 2573) (p 2753) (p 2946) (p 3005) (p 3136) (p 3347) (p 3945) (p 4117) (p 4311) (p 4902) (derived105456 p h) (derived100781 p h) (derived92417 p h)

theorem derived114238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2417) ∨ (p 3631) :=
  ElevenRUP.step114238 (p 2417) (p 2922) (p 2933) (p 3631) (derived95529 p h) (derived96902 p h)

theorem derived114239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2911) ∨ (p 3527) :=
  ElevenRUP.step114239 (p 2911) (p 2922) (p 2933) (p 3527) (derived95532 p h) (derived96902 p h)

theorem derived114240 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3547) ∨ (¬ p 4710) :=
  ElevenRUP.step114240 (p 2922) (p 2933) (p 3547) (p 4710) (h 32859) (derived96902 p h)

theorem derived114241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3571) ∨ (¬ p 3569) :=
  ElevenRUP.step114241 (p 2922) (p 2933) (p 3569) (p 3571) (h 5198) (derived96902 p h)

theorem derived114245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2881) ∨ (p 3527) ∨ (¬ p 3569) :=
  ElevenRUP.step114245 (p 2881) (p 2922) (p 2933) (p 3527) (p 3569) (derived95544 p h) (derived96902 p h)

theorem derived114247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2717) ∨ (p 3389) ∨ (¬ p 5085) ∨ (p 3527) :=
  ElevenRUP.step114247 (p 2717) (p 2922) (p 2933) (p 3389) (p 3527) (p 5085) (derived76885 p h) (derived96902 p h)

theorem derived114250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 4909) ∨ (¬ p 2230) ∨ (p 3389) ∨ (¬ p 2870) :=
  ElevenRUP.step114250 (p 2230) (p 2870) (p 2922) (p 2933) (p 3389) (p 4909) (derived107326 p h) (derived96902 p h)

theorem derived114251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3399) ∨ (p 2437) ∨ (p 3379) :=
  ElevenRUP.step114251 (p 2437) (p 2922) (p 2933) (p 3379) (p 3399) (p 4814) (derived105440 p h) (derived95506 p h) (derived96902 p h)

theorem derived114252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2761) ∨ (¬ p 2417) ∨ (p 3379) ∨ (¬ p 3399) :=
  ElevenRUP.step114252 (p 2417) (p 2761) (p 2922) (p 2933) (p 3379) (p 3399) (derived95508 p h) (derived96902 p h)

theorem derived114254 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3399) ∨ (p 3379) ∨ (¬ p 2911) ∨ (¬ p 2459) :=
  ElevenRUP.step114254 (p 2459) (p 2911) (p 2922) (p 2933) (p 3379) (p 3399) (derived95512 p h) (derived96902 p h)

theorem derived114255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3399) ∨ (p 3201) ∨ (p 3379) :=
  ElevenRUP.step114255 (p 2922) (p 2933) (p 3201) (p 3379) (p 3399) (p 5217) (derived105493 p h) (derived95514 p h) (derived96902 p h)

theorem derived114258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2881) ∨ (p 3527) ∨ (p 3389) ∨ (¬ p 2230) :=
  ElevenRUP.step114258 (p 2230) (p 2881) (p 2922) (p 2933) (p 3389) (p 3527) (derived99995 p h) (derived96902 p h)

theorem derived114260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3527) ∨ (¬ p 5693) ∨ (¬ p 2881) ∨ (¬ p 3941) :=
  ElevenRUP.step114260 (p 2881) (p 2922) (p 2933) (p 3527) (p 3941) (p 5693) (derived112243 p h) (derived96902 p h)

theorem derived114268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2441) ∨ (¬ p 3246) ∨ (¬ p 2563) ∨ (p 3631) :=
  ElevenRUP.step114268 (p 2441) (p 2563) (p 2922) (p 2933) (p 3246) (p 3631) (p 4555) (derived105542 p h) (derived95541 p h) (derived96902 p h)

theorem derived114271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2122) ∨ (p 3631) ∨ (p 3389) ∨ (¬ p 4375) ∨ (¬ p 3434) :=
  ElevenRUP.step114271 (p 2122) (p 2922) (p 2933) (p 3389) (p 3434) (p 3631) (p 4375) (derived111337 p h) (derived96902 p h)

theorem derived114281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2668) ∨ (p 3527) ∨ (p 3073) ∨ (¬ p 3256) ∨ (¬ p 2440) ∨ (¬ p 3019) :=
  ElevenRUP.step114281 (p 2440) (p 2668) (p 2922) (p 2933) (p 3019) (p 3073) (p 3256) (p 3527) (derived112841 p h) (derived96902 p h)

theorem derived114287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 4322) ∨ (¬ p 3399) ∨ (p 3379) ∨ (p 2132) ∨ (p 3105) ∨ (¬ p 3366) ∨ (¬ p 3868) :=
  ElevenRUP.step114287 (p 2132) (p 2922) (p 2933) (p 3105) (p 3366) (p 3379) (p 3399) (p 3868) (p 4322) (p 4376) (p 4826) (derived106320 p h) (derived105444 p h) (derived84505 p h) (derived96902 p h)

theorem derived114288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2417) ∨ (p 2619) ∨ (p 3146) ∨ (¬ p 3399) ∨ (p 3379) ∨ (p 2132) ∨ (¬ p 3366) ∨ (¬ p 3950) :=
  ElevenRUP.step114288 (p 2132) (p 2417) (p 2619) (p 2922) (p 2933) (p 3146) (p 3366) (p 3379) (p 3399) (p 3950) (p 4376) (derived106320 p h) (derived84743 p h) (derived96902 p h)

theorem derived114289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2417) ∨ (p 3256) ∨ (¬ p 3399) ∨ (¬ p 3950) ∨ (p 2696) ∨ (p 3005) ∨ (¬ p 3366) ∨ (p 3379) :=
  ElevenRUP.step114289 (p 2417) (p 2696) (p 2922) (p 2933) (p 3005) (p 3256) (p 3366) (p 3379) (p 3399) (p 3950) (p 4376) (derived106320 p h) (derived95507 p h) (derived96902 p h)

theorem derived114292 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 2911) ∨ (¬ p 3399) ∨ (p 2774) ∨ (¬ p 3366) ∨ (p 3379) :=
  ElevenRUP.step114292 (p 2122) (p 2396) (p 2774) (p 2911) (p 2922) (p 2933) (p 3366) (p 3379) (p 3399) (p 4376) (p 4666) (derived105658 p h) (derived106320 p h) (derived97894 p h) (derived96902 p h)

theorem derived114294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3105) ∨ (p 3670) ∨ (¬ p 2417) ∨ (¬ p 3461) ∨ (¬ p 3366) ∨ (¬ p 4032) ∨ (p 2241) ∨ (¬ p 3399) ∨ (¬ p 2136) :=
  ElevenRUP.step114294 (p 2136) (p 2241) (p 2417) (p 2922) (p 2933) (p 3105) (p 3366) (p 3399) (p 3461) (p 3670) (p 4032) (derived109442 p h) (derived96902 p h)

theorem derived114302 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3016) ∨ (¬ p 3920) :=
  ElevenRUP.step114302 (p 2437) (p 3016) (p 3740) (p 3920) (derived113975 p h) (derived96076 p h)

theorem derived114304 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 3699) ∨ (¬ p 4001) :=
  ElevenRUP.step114304 (p 2437) (p 3699) (p 3740) (p 4001) (h 34280) (derived96076 p h)

theorem derived114305 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2911) ∨ (¬ p 2264) :=
  ElevenRUP.step114305 (p 2264) (p 2437) (p 2911) (p 3740) (derived76191 p h) (derived96076 p h)

theorem derived114306 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2449) ∨ (p 2417) :=
  ElevenRUP.step114306 (p 2417) (p 2437) (p 2449) (p 3740) (derived82164 p h) (derived96076 p h)

theorem derived114307 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3921) ∨ (p 2298) :=
  ElevenRUP.step114307 (p 2298) (p 2437) (p 3740) (p 3921) (h 25743) (derived96076 p h)

theorem derived114308 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 3575) ∨ (¬ p 4066) :=
  ElevenRUP.step114308 (p 2437) (p 3575) (p 3740) (p 4066) (h 23380) (derived96076 p h)

theorem derived114317 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2996) ∨ (¬ p 2727) ∨ (¬ p 3201) :=
  ElevenRUP.step114317 (p 2437) (p 2727) (p 2996) (p 3201) (p 3740) (p 4753) (derived105514 p h) (derived41264 p h) (derived96076 p h)

theorem derived114318 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2996) ∨ (¬ p 2608) ∨ (p 2241) ∨ (p 2911) :=
  ElevenRUP.step114318 (p 2241) (p 2437) (p 2608) (p 2911) (p 2996) (p 3740) (derived80782 p h) (derived96076 p h)

theorem derived114319 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2996) ∨ (¬ p 3389) ∨ (¬ p 2727) :=
  ElevenRUP.step114319 (p 2437) (p 2665) (p 2727) (p 2996) (p 3389) (p 3740) (derived105373 p h) (derived48358 p h) (derived96076 p h)

theorem derived114324 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2807) ∨ (p 2911) ∨ (p 2630) ∨ (¬ p 2651) :=
  ElevenRUP.step114324 (p 2437) (p 2630) (p 2651) (p 2807) (p 2911) (p 3740) (derived99184 p h) (derived96076 p h)

theorem derived114325 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2911) ∨ (p 2727) ∨ (p 2807) ∨ (¬ p 2651) :=
  ElevenRUP.step114325 (p 2437) (p 2651) (p 2727) (p 2807) (p 2911) (p 3740) (derived99187 p h) (derived96076 p h)

theorem derived114326 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2553) ∨ (p 2685) ∨ (¬ p 2630) ∨ (¬ p 3016) :=
  ElevenRUP.step114326 (p 2437) (p 2553) (p 2630) (p 2685) (p 3016) (p 3740) (derived109152 p h) (derived96076 p h)

theorem derived114327 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2449) ∨ (p 2396) ∨ (p 2807) ∨ (¬ p 3286) :=
  ElevenRUP.step114327 (p 2396) (p 2437) (p 2449) (p 2807) (p 3286) (p 3740) (derived110665 p h) (derived96076 p h)

theorem derived114329 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3921) ∨ (p 2807) ∨ (¬ p 2331) ∨ (¬ p 2274) :=
  ElevenRUP.step114329 (p 2274) (p 2331) (p 2437) (p 2807) (p 3740) (p 3921) (p 4564) (derived105401 p h) (derived75829 p h) (derived96076 p h)

theorem derived114330 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2881) ∨ (¬ p 2264) ∨ (¬ p 3519) ∨ (¬ p 3389) ∨ (p 2406) :=
  ElevenRUP.step114330 (p 2264) (p 2406) (p 2437) (p 2881) (p 3389) (p 3519) (p 3740) (derived75830 p h) (derived96076 p h)

theorem derived114332 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2996) ∨ (¬ p 2656) ∨ (¬ p 2230) ∨ (¬ p 2727) :=
  ElevenRUP.step114332 (p 2230) (p 2437) (p 2656) (p 2727) (p 2996) (p 3740) (p 4644) (derived105411 p h) (derived49913 p h) (derived96076 p h)

theorem derived114335 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2685) ∨ (¬ p 2630) ∨ (¬ p 2230) ∨ (¬ p 2656) :=
  ElevenRUP.step114335 (p 2230) (p 2437) (p 2630) (p 2656) (p 2685) (p 3740) (p 4644) (derived105411 p h) (derived87076 p h) (derived96076 p h)

theorem derived114338 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 3399) ∨ (¬ p 3032) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step114338 (p 2406) (p 2437) (p 3032) (p 3379) (p 3399) (p 3740) (p 4644) (derived105411 p h) (derived91048 p h) (derived96076 p h)

theorem derived114340 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2417) ∨ (p 2807) ∨ (¬ p 2396) ∨ (¬ p 2252) ∨ (¬ p 2727) :=
  ElevenRUP.step114340 (p 2252) (p 2396) (p 2417) (p 2437) (p 2727) (p 2807) (p 3740) (derived99172 p h) (derived96076 p h)

theorem derived114364 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3073) ∨ (¬ p 5693) ∨ (¬ p 3389) ∨ (¬ p 2264) ∨ (p 3830) ∨ (¬ p 2663) ∨ (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2459) :=
  ElevenRUP.step114364 (p 2246) (p 2264) (p 2437) (p 2459) (p 2608) (p 2663) (p 3073) (p 3389) (p 3740) (p 3830) (p 5693) (derived110493 p h) (derived96076 p h)

theorem derived114370 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 2352) ∨ (¬ p 3990) :=
  ElevenRUP.step114370 (p 2352) (p 3564) (p 3746) (p 3990) (derived111505 p h) (derived102055 p h)

theorem derived114371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 4042) ∨ (¬ p 3550) :=
  ElevenRUP.step114371 (p 2187) (p 3550) (p 4042) (p 4441) (h 28032) (derived93560 p h)

theorem derived114372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 3146) ∨ (¬ p 2363) :=
  ElevenRUP.step114372 (p 2187) (p 2363) (p 3146) (p 4441) (derived97002 p h) (derived93560 p h)

theorem derived114374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2619) ∨ (p 2860) ∨ (p 3125) :=
  ElevenRUP.step114374 (p 2187) (p 2619) (p 2860) (p 3125) (p 4441) (derived107135 p h) (derived93560 p h)

theorem derived114375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2860) ∨ (¬ p 2619) ∨ (p 2383) :=
  ElevenRUP.step114375 (p 2187) (p 2383) (p 2619) (p 2860) (p 4441) (derived83353 p h) (derived93560 p h)

theorem derived114377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (¬ p 2373) ∨ (p 2383) :=
  ElevenRUP.step114377 (p 2187) (p 2373) (p 2383) (p 2563) (p 4441) (derived98393 p h) (derived93560 p h)

theorem derived114379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2274) ∨ (p 2284) ∨ (¬ p 3156) :=
  ElevenRUP.step114379 (p 2187) (p 2274) (p 2284) (p 3156) (p 4405) (p 4441) (derived105512 p h) (derived77997 p h) (derived93560 p h)

theorem derived114380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 3146) ∨ (¬ p 2459) ∨ (¬ p 2307) ∨ (p 2383) :=
  ElevenRUP.step114380 (p 2187) (p 2307) (p 2383) (p 2459) (p 3146) (p 4441) (derived78401 p h) (derived93560 p h)

theorem derived114384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2619) ∨ (¬ p 2295) ∨ (p 2860) ∨ (p 2668) :=
  ElevenRUP.step114384 (p 2187) (p 2295) (p 2619) (p 2668) (p 2860) (p 4441) (derived79418 p h) (derived93560 p h)

theorem derived114387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2166) ∨ (¬ p 2563) ∨ (p 2192) ∨ (¬ p 2363) :=
  ElevenRUP.step114387 (p 2166) (p 2187) (p 2192) (p 2363) (p 2563) (p 4441) (derived80059 p h) (derived93560 p h)

theorem derived114388 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2192) ∨ (p 2352) ∨ (¬ p 2166) :=
  ElevenRUP.step114388 (p 2166) (p 2187) (p 2192) (p 2352) (p 3958) (p 4441) (derived105378 p h) (derived80060 p h) (derived93560 p h)

theorem derived114389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2274) ∨ (¬ p 2166) ∨ (p 2192) :=
  ElevenRUP.step114389 (p 2166) (p 2187) (p 2192) (p 2274) (p 4405) (p 4441) (derived105512 p h) (derived80062 p h) (derived93560 p h)

theorem derived114390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2619) ∨ (p 2860) ∨ (p 2274) :=
  ElevenRUP.step114390 (p 2187) (p 2274) (p 2619) (p 2860) (p 4405) (p 4441) (derived105512 p h) (derived83305 p h) (derived93560 p h)

theorem derived114391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2220) ∨ (¬ p 2363) ∨ (¬ p 2563) ∨ (p 2156) :=
  ElevenRUP.step114391 (p 2156) (p 2187) (p 2220) (p 2363) (p 2563) (p 4441) (derived85391 p h) (derived93560 p h)

theorem derived114393 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2274) ∨ (p 2156) ∨ (¬ p 2220) :=
  ElevenRUP.step114393 (p 2156) (p 2187) (p 2220) (p 2274) (p 4405) (p 4441) (derived105512 p h) (derived85419 p h) (derived93560 p h)

theorem derived114395 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (¬ p 2373) ∨ (¬ p 4889) ∨ (p 2819) :=
  ElevenRUP.step114395 (p 2187) (p 2373) (p 2563) (p 2819) (p 4441) (p 4889) (derived93426 p h) (derived93560 p h)

theorem derived114397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (¬ p 2373) ∨ (p 2668) :=
  ElevenRUP.step114397 (p 2187) (p 2373) (p 2563) (p 2668) (p 4441) (p 4564) (derived105401 p h) (derived98551 p h) (derived93560 p h)

theorem derived114399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2284) ∨ (¬ p 3156) ∨ (p 2352) :=
  ElevenRUP.step114399 (p 2187) (p 2284) (p 2352) (p 3156) (p 3958) (p 4441) (derived105378 p h) (derived98698 p h) (derived93560 p h)

theorem derived114401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3923) ∨ (¬ p 2373) ∨ (¬ p 3309) ∨ (p 2563) :=
  ElevenRUP.step114401 (p 2187) (p 2373) (p 2563) (p 3309) (p 3923) (p 4441) (derived98743 p h) (derived93560 p h)

theorem derived114402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2373) ∨ (p 2459) ∨ (¬ p 2363) ∨ (p 2440) :=
  ElevenRUP.step114402 (p 2187) (p 2363) (p 2373) (p 2440) (p 2459) (p 4441) (derived98761 p h) (derived93560 p h)

theorem derived114404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3868) ∨ (¬ p 5562) ∨ (¬ p 5568) ∨ (p 2911) :=
  ElevenRUP.step114404 (p 2187) (p 2911) (p 3868) (p 4133) (p 4441) (p 5562) (p 5568) (derived105712 p h) (derived76644 p h) (derived93560 p h)

theorem derived114408 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 3146) ∨ (¬ p 2911) ∨ (¬ p 2459) ∨ (¬ p 3955) :=
  ElevenRUP.step114408 (p 2187) (p 2459) (p 2911) (p 3146) (p 3955) (p 4441) (p 4712) (derived105422 p h) (derived82406 p h) (derived93560 p h)

theorem derived114409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 3105) ∨ (¬ p 3949) ∨ (¬ p 2459) ∨ (¬ p 2619) :=
  ElevenRUP.step114409 (p 2187) (p 2459) (p 2619) (p 3105) (p 3949) (p 4133) (p 4441) (derived105712 p h) (derived84475 p h) (derived93560 p h)

theorem derived114410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2553) ∨ (¬ p 2220) ∨ (p 2156) ∨ (¬ p 4203) :=
  ElevenRUP.step114410 (p 2156) (p 2187) (p 2220) (p 2553) (p 4203) (p 4405) (p 4441) (derived105512 p h) (derived85554 p h) (derived93560 p h)

theorem derived114411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 5660) ∨ (¬ p 3550) ∨ (p 2870) ∨ (¬ p 2619) :=
  ElevenRUP.step114411 (p 2187) (p 2619) (p 2870) (p 3550) (p 4441) (p 5559) (p 5660) (derived106189 p h) (derived86789 p h) (derived93560 p h)

theorem derived114415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (¬ p 2373) ∨ (¬ p 2156) ∨ (¬ p 2363) ∨ (¬ p 4399) :=
  ElevenRUP.step114415 (p 2156) (p 2187) (p 2363) (p 2373) (p 2563) (p 4399) (p 4441) (derived98195 p h) (derived93560 p h)

theorem derived114421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (p 3309) ∨ (¬ p 2373) ∨ (¬ p 4356) ∨ (¬ p 5016) :=
  ElevenRUP.step114421 (p 2187) (p 2373) (p 2563) (p 3309) (p 4356) (p 4405) (p 4441) (p 5016) (derived105512 p h) (derived91794 p h) (derived93560 p h)

theorem derived114423 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 5472) ∨ (¬ p 4393) ∨ (¬ p 2957) ∨ (¬ p 3955) ∨ (p 2156) ∨ (¬ p 3156) :=
  ElevenRUP.step114423 (p 2156) (p 2187) (p 2957) (p 3156) (p 3955) (p 4393) (p 4441) (p 5472) (derived96114 p h) (derived93560 p h)

theorem derived114428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3737) ∨ (¬ p 4329) ∨ (¬ p 3156) ∨ (¬ p 2563) ∨ (¬ p 4328) ∨ (¬ p 4153) ∨ (¬ p 3955) :=
  ElevenRUP.step114428 (p 2187) (p 2563) (p 3156) (p 3737) (p 3955) (p 4153) (p 4328) (p 4329) (p 4441) (derived46089 p h) (derived93560 p h)

theorem derived114431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (¬ p 2373) ∨ (¬ p 2156) ∨ (p 2264) ∨ (¬ p 2996) ∨ (p 2241) ∨ (¬ p 4521) :=
  ElevenRUP.step114431 (p 2156) (p 2187) (p 2241) (p 2264) (p 2373) (p 2563) (p 2996) (p 4133) (p 4441) (p 4521) (derived105712 p h) (derived80868 p h) (derived93560 p h)

theorem derived114432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2563) ∨ (p 2717) ∨ (¬ p 4521) ∨ (p 2707) ∨ (¬ p 2156) ∨ (¬ p 2373) ∨ (p 2608) :=
  ElevenRUP.step114432 (p 2156) (p 2187) (p 2373) (p 2563) (p 2608) (p 2707) (p 2717) (p 4133) (p 4441) (p 4521) (derived105712 p h) (derived88270 p h) (derived93560 p h)

theorem derived114433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2284) ∨ (¬ p 3156) ∨ (¬ p 2156) ∨ (p 2598) ∨ (p 2911) ∨ (p 3201) ∨ (¬ p 2139) :=
  ElevenRUP.step114433 (p 2139) (p 2156) (p 2187) (p 2284) (p 2598) (p 2911) (p 3156) (p 3201) (p 4133) (p 4441) (derived105712 p h) (derived95651 p h) (derived93560 p h)

theorem derived114434 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2098) ∨ (¬ p 2156) ∨ (¬ p 2373) ∨ (¬ p 2459) ∨ (p 3609) ∨ (p 2563) ∨ (¬ p 2139) :=
  ElevenRUP.step114434 (p 2098) (p 2139) (p 2156) (p 2187) (p 2373) (p 2459) (p 2563) (p 3609) (p 4133) (p 4441) (derived105712 p h) (derived97141 p h) (derived93560 p h)

theorem derived114439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 3266) ∨ (¬ p 4512) ∨ (p 3146) ∨ (¬ p 2911) ∨ (p 3425) ∨ (¬ p 2753) ∨ (p 2383) ∨ (¬ p 3204) ∨ (¬ p 5503) ∨ (¬ p 4253) :=
  ElevenRUP.step114439 (p 2187) (p 2383) (p 2753) (p 2911) (p 3146) (p 3204) (p 3266) (p 3425) (p 4253) (p 4441) (p 4512) (p 4877) (p 5503) (derived105451 p h) (derived76538 p h) (derived93560 p h)

theorem derived114440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3868) ∨ (p 3266) ∨ (p 3146) ∨ (p 2383) ∨ (¬ p 3201) ∨ (¬ p 2753) ∨ (¬ p 2598) ∨ (¬ p 4512) ∨ (¬ p 3204) :=
  ElevenRUP.step114440 (p 2187) (p 2383) (p 2598) (p 2753) (p 3146) (p 3201) (p 3204) (p 3266) (p 3868) (p 4441) (p 4512) (p 4826) (p 4877) (derived105451 p h) (derived105444 p h) (derived77235 p h) (derived93560 p h)

theorem derived114441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2459) ∨ (p 2528) ∨ (p 3389) ∨ (p 2860) ∨ (¬ p 2156) ∨ (¬ p 2753) ∨ (¬ p 2655) ∨ (¬ p 2619) ∨ (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 4186) :=
  ElevenRUP.step114441 (p 2144) (p 2156) (p 2187) (p 2252) (p 2459) (p 2528) (p 2619) (p 2655) (p 2750) (p 2753) (p 2860) (p 3389) (p 4133) (p 4186) (p 4441) (derived106345 p h) (derived105712 p h) (derived101671 p h) (derived93560 p h)

theorem derived114442 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 4383) ∨ (¬ p 3693) :=
  ElevenRUP.step114442 (p 2881) (p 3693) (p 4132) (p 4383) (h 35557) (derived95081 p h)

theorem derived114443 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2459) ∨ (¬ p 3146) :=
  ElevenRUP.step114443 (p 2459) (p 2881) (p 3146) (p 4132) (derived113021 p h) (derived95081 p h)

theorem derived114445 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2166) ∨ (¬ p 2341) ∨ (¬ p 2891) :=
  ElevenRUP.step114445 (p 2166) (p 2341) (p 2881) (p 2891) (p 4132) (derived75967 p h) (derived95081 p h)

theorem derived114446 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2373) ∨ (¬ p 2341) ∨ (¬ p 2427) :=
  ElevenRUP.step114446 (p 2341) (p 2373) (p 2427) (p 2881) (p 4132) (derived78906 p h) (derived95081 p h)

theorem derived114449 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2373) ∨ (¬ p 2911) ∨ (¬ p 3741) :=
  ElevenRUP.step114449 (p 2373) (p 2881) (p 2911) (p 3741) (p 4132) (derived101897 p h) (derived95081 p h)

theorem derived114452 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2166) ∨ (¬ p 2264) ∨ (¬ p 2891) :=
  ElevenRUP.step114452 (p 2166) (p 2264) (p 2881) (p 2891) (p 4132) (p 4362) (derived106173 p h) (derived75971 p h) (derived95081 p h)

theorem derived114453 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2166) ∨ (¬ p 2177) ∨ (¬ p 2891) :=
  ElevenRUP.step114453 (p 2166) (p 2177) (p 2881) (p 2891) (p 4132) (p 4556) (derived105399 p h) (derived75982 p h) (derived95081 p h)

theorem derived114454 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3246) ∨ (p 2166) ∨ (¬ p 2891) :=
  ElevenRUP.step114454 (p 2166) (p 2881) (p 2891) (p 3246) (p 4132) (p 4668) (derived105414 p h) (derived75985 p h) (derived95081 p h)

theorem derived114455 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2459) ∨ (p 2166) ∨ (p 2427) ∨ (¬ p 2891) :=
  ElevenRUP.step114455 (p 2166) (p 2427) (p 2459) (p 2881) (p 2891) (p 4132) (derived75989 p h) (derived95081 p h)

theorem derived114456 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2373) ∨ (¬ p 3246) ∨ (¬ p 2427) :=
  ElevenRUP.step114456 (p 2373) (p 2427) (p 2881) (p 3246) (p 4132) (p 4668) (derived105414 p h) (derived78901 p h) (derived95081 p h)

theorem derived114457 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2373) ∨ (¬ p 2427) ∨ (¬ p 2177) :=
  ElevenRUP.step114457 (p 2177) (p 2373) (p 2427) (p 2881) (p 4132) (p 4556) (derived105399 p h) (derived78904 p h) (derived95081 p h)

theorem derived114458 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2373) ∨ (¬ p 2264) ∨ (¬ p 2427) :=
  ElevenRUP.step114458 (p 2264) (p 2373) (p 2427) (p 2881) (p 4132) (p 4362) (derived106173 p h) (derived78905 p h) (derived95081 p h)

theorem derived114460 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 5564) ∨ (¬ p 4129) ∨ (p 3156) ∨ (¬ p 2901) :=
  ElevenRUP.step114460 (p 2881) (p 2901) (p 3156) (p 4129) (p 4132) (p 5564) (derived79045 p h) (derived95081 p h)

theorem derived114461 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 3156) ∨ (¬ p 2177) ∨ (¬ p 2901) :=
  ElevenRUP.step114461 (p 2177) (p 2881) (p 2901) (p 3156) (p 4132) (p 4556) (derived105399 p h) (derived79089 p h) (derived95081 p h)

theorem derived114462 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 2911) ∨ (p 3156) ∨ (¬ p 2901) :=
  ElevenRUP.step114462 (p 2881) (p 2901) (p 2911) (p 3156) (p 4132) (p 4647) (derived105412 p h) (derived79104 p h) (derived95081 p h)

theorem derived114463 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 5564) ∨ (¬ p 4129) ∨ (p 2220) ∨ (¬ p 3051) :=
  ElevenRUP.step114463 (p 2220) (p 2881) (p 3051) (p 4129) (p 4132) (p 5564) (derived80272 p h) (derived95081 p h)

theorem derived114464 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2619) ∨ (¬ p 2911) ∨ (¬ p 2870) :=
  ElevenRUP.step114464 (p 2619) (p 2870) (p 2881) (p 2911) (p 4132) (p 4647) (derived105412 p h) (derived84619 p h) (derived95081 p h)

theorem derived114465 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2459) ∨ (¬ p 2870) ∨ (p 3051) ∨ (p 2619) :=
  ElevenRUP.step114465 (p 2459) (p 2619) (p 2870) (p 2881) (p 3051) (p 4132) (derived84620 p h) (derived95081 p h)

theorem derived114466 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2619) ∨ (¬ p 2177) ∨ (¬ p 2870) :=
  ElevenRUP.step114466 (p 2177) (p 2619) (p 2870) (p 2881) (p 4132) (p 4556) (derived105399 p h) (derived84775 p h) (derived95081 p h)

theorem derived114467 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 2717) ∨ (p 3156) ∨ (¬ p 2901) :=
  ElevenRUP.step114467 (p 2717) (p 2881) (p 2901) (p 3156) (p 4132) (p 4898) (derived105455 p h) (derived89264 p h) (derived95081 p h)

theorem derived114468 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3051) ∨ (p 2220) ∨ (¬ p 2177) :=
  ElevenRUP.step114468 (p 2177) (p 2220) (p 2881) (p 3051) (p 4132) (p 4556) (derived105399 p h) (derived92454 p h) (derived95081 p h)

theorem derived114469 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2220) ∨ (¬ p 2911) ∨ (¬ p 3051) :=
  ElevenRUP.step114469 (p 2220) (p 2881) (p 2911) (p 3051) (p 4132) (p 4647) (derived105412 p h) (derived92456 p h) (derived95081 p h)

theorem derived114470 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 5693) ∨ (¬ p 3969) ∨ (¬ p 2210) ∨ (p 3449) :=
  ElevenRUP.step114470 (p 2210) (p 2881) (p 3449) (p 3969) (p 4132) (p 5693) (derived94221 p h) (derived95081 p h)

theorem derived114473 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 3246) ∨ (p 2619) ∨ (¬ p 2177) ∨ (¬ p 3105) :=
  ElevenRUP.step114473 (p 2177) (p 2619) (p 2881) (p 3105) (p 3246) (p 4132) (derived111070 p h) (derived95081 p h)

theorem derived114477 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 3156) ∨ (¬ p 2341) ∨ (¬ p 2901) ∨ (¬ p 3575) :=
  ElevenRUP.step114477 (p 2341) (p 2881) (p 2901) (p 3156) (p 3575) (p 4132) (p 4647) (derived105412 p h) (derived79080 p h) (derived95081 p h)

theorem derived114480 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3516) ∨ (p 2619) ∨ (¬ p 2870) ∨ (¬ p 3691) :=
  ElevenRUP.step114480 (p 2619) (p 2870) (p 2881) (p 3516) (p 3691) (p 4132) (p 4668) (derived105414 p h) (derived84621 p h) (derived95081 p h)

theorem derived114483 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 2449) ∨ (¬ p 5600) ∨ (¬ p 3969) ∨ (¬ p 3919) :=
  ElevenRUP.step114483 (p 2449) (p 2881) (p 3919) (p 3969) (p 4132) (p 4668) (p 5600) (derived105414 p h) (derived56563 p h) (derived95081 p h)

theorem derived114486 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3146) ∨ (¬ p 2177) ∨ (¬ p 3919) ∨ (p 3073) ∨ (¬ p 4288) :=
  ElevenRUP.step114486 (p 2177) (p 2881) (p 3073) (p 3146) (p 3919) (p 4132) (p 4288) (derived93663 p h) (derived95081 p h)

theorem derived114488 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3246) ∨ (¬ p 3051) ∨ (p 3156) ∨ (¬ p 2951) :=
  ElevenRUP.step114488 (p 2881) (p 2951) (p 3051) (p 3156) (p 3246) (p 4132) (p 4668) (derived105414 p h) (derived98239 p h) (derived95081 p h)

theorem derived114489 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 5564) ∨ (¬ p 4063) ∨ (p 2088) ∨ (¬ p 3146) ∨ (¬ p 3961) :=
  ElevenRUP.step114489 (p 2088) (p 2881) (p 3146) (p 3961) (p 4063) (p 4132) (p 5564) (derived98445 p h) (derived95081 p h)

theorem derived114490 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 3969) ∨ (¬ p 4445) ∨ (p 3434) ∨ (¬ p 2717) :=
  ElevenRUP.step114490 (p 2717) (p 2881) (p 3434) (p 3969) (p 4132) (p 4445) (p 5122) (derived105483 p h) (derived102382 p h) (derived95081 p h)

theorem derived114494 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2264) ∨ (¬ p 5107) ∨ (¬ p 3189) ∨ (¬ p 3146) ∨ (¬ p 3848) :=
  ElevenRUP.step114494 (p 2264) (p 2881) (p 3146) (p 3189) (p 3848) (p 4132) (p 5107) (derived112912 p h) (derived95081 p h)

theorem derived114510 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 4435) ∨ (¬ p 5254) ∨ (¬ p 3146) ∨ (p 3093) ∨ (¬ p 3266) ∨ (¬ p 3543) ∨ (¬ p 2341) ∨ (¬ p 2608) :=
  ElevenRUP.step114510 (p 2341) (p 2608) (p 2881) (p 3093) (p 3146) (p 3266) (p 3543) (p 4132) (p 4435) (p 4793) (p 5254) (derived105438 p h) (derived96704 p h) (derived95081 p h)

theorem derived114513 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 4228) ∨ (¬ p 3146) ∨ (¬ p 5254) ∨ (p 2797) ∨ (¬ p 3266) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 2341) ∨ (¬ p 4988) ∨ (p 2696) :=
  ElevenRUP.step114513 (p 2341) (p 2696) (p 2797) (p 2881) (p 3146) (p 3266) (p 3366) (p 3370) (p 4132) (p 4228) (p 4988) (p 5254) (derived110237 p h) (derived95081 p h)

theorem derived114514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4683) ∨ (¬ p 5866) ∨ (¬ p 2509) :=
  ElevenRUP.step114514 (p 2509) (p 4370) (p 4683) (p 5866) (derived113023 p h) (h 7549)

theorem derived114515 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 3201) ∨ (¬ p 3641) :=
  ElevenRUP.step114515 (p 2911) (p 3201) (p 3641) (p 4186) (derived77349 p h) (derived91169 p h)

theorem derived114516 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2470) ∨ (p 3389) :=
  ElevenRUP.step114516 (p 2470) (p 2911) (p 3389) (p 4186) (derived77493 p h) (derived91169 p h)

theorem derived114517 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2922) ∨ (¬ p 2518) :=
  ElevenRUP.step114517 (p 2518) (p 2911) (p 2922) (p 4186) (h 35053) (derived91169 p h)

theorem derived114518 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3083) ∨ (p 2437) :=
  ElevenRUP.step114518 (p 2437) (p 2911) (p 3083) (p 4186) (derived97015 p h) (derived91169 p h)

theorem derived114519 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 3573) ∨ (¬ p 3581) :=
  ElevenRUP.step114519 (p 2911) (p 3573) (p 3581) (p 4186) (h 32074) (derived91169 p h)

theorem derived114520 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 4607) ∨ (¬ p 2441) :=
  ElevenRUP.step114520 (p 2441) (p 2911) (p 4186) (p 4607) (h 40662) (derived91169 p h)

theorem derived114521 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (p 4635) :=
  ElevenRUP.step114521 (p 2528) (p 2911) (p 4186) (p 4635) (derived112465 p h) (derived91169 p h)

theorem derived114526 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 4149) ∨ (¬ p 3941) ∨ (p 2459) ∨ (p 3389) :=
  ElevenRUP.step114526 (p 2459) (p 2911) (p 3389) (p 3941) (p 4149) (p 4186) (derived89935 p h) (derived91169 p h)

theorem derived114527 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 2341) :=
  ElevenRUP.step114527 (p 2341) (p 2459) (p 2528) (p 2911) (p 4186) (p 5203) (derived105490 p h) (derived101666 p h) (derived91169 p h)

theorem derived114528 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 2573) ∨ (p 3389) :=
  ElevenRUP.step114528 (p 2459) (p 2528) (p 2573) (p 2911) (p 3389) (p 4186) (derived101669 p h) (derived91169 p h)

theorem derived114529 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (p 3201) ∨ (p 2598) ∨ (¬ p 2459) :=
  ElevenRUP.step114529 (p 2459) (p 2528) (p 2598) (p 2911) (p 3201) (p 4186) (derived101681 p h) (derived91169 p h)

theorem derived114530 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (¬ p 2459) ∨ (p 2437) ∨ (p 2651) :=
  ElevenRUP.step114530 (p 2437) (p 2459) (p 2528) (p 2651) (p 2911) (p 4186) (derived101685 p h) (derived91169 p h)

theorem derived114532 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3641) ∨ (¬ p 3609) ∨ (p 2528) ∨ (p 2922) :=
  ElevenRUP.step114532 (p 2528) (p 2911) (p 2922) (p 3609) (p 3641) (p 4186) (derived110399 p h) (derived91169 p h)

theorem derived114533 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3641) ∨ (¬ p 4019) ∨ (p 4149) ∨ (p 2850) :=
  ElevenRUP.step114533 (p 2850) (p 2911) (p 3641) (p 4019) (p 4149) (p 4186) (derived110401 p h) (derived91169 p h)

theorem derived114534 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3363) ∨ (p 2528) ∨ (p 3389) ∨ (p 3367) ∨ (¬ p 2459) :=
  ElevenRUP.step114534 (p 2459) (p 2528) (p 2911) (p 3363) (p 3367) (p 3389) (p 4186) (derived75572 p h) (derived91169 p h)

theorem derived114536 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2088) ∨ (¬ p 2881) ∨ (¬ p 3960) ∨ (p 2528) :=
  ElevenRUP.step114536 (p 2088) (p 2528) (p 2881) (p 2911) (p 3960) (p 4186) (p 4277) (derived105380 p h) (derived78463 p h) (derived91169 p h)

theorem derived114537 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3156) ∨ (p 2528) ∨ (¬ p 3146) ∨ (¬ p 2441) :=
  ElevenRUP.step114537 (p 2441) (p 2528) (p 2911) (p 3146) (p 3156) (p 4186) (p 4705) (derived106238 p h) (derived78773 p h) (derived91169 p h)

theorem derived114538 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 4688) ∨ (¬ p 3073) ∨ (p 2528) ∨ (p 2437) :=
  ElevenRUP.step114538 (p 2437) (p 2528) (p 2911) (p 3073) (p 4186) (p 4688) (p 4814) (derived105440 p h) (derived80174 p h) (derived91169 p h)

theorem derived114540 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 3146) ∨ (¬ p 2459) ∨ (p 2440) ∨ (p 2437) ∨ (¬ p 3693) :=
  ElevenRUP.step114540 (p 2437) (p 2440) (p 2459) (p 2911) (p 3146) (p 3693) (p 4186) (derived83110 p h) (derived91169 p h)

theorem derived114543 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3083) ∨ (p 2707) ∨ (¬ p 3367) ∨ (¬ p 4106) :=
  ElevenRUP.step114543 (p 2707) (p 2911) (p 3083) (p 3367) (p 4106) (p 4186) (p 4750) (derived105433 p h) (derived101321 p h) (derived91169 p h)

theorem derived114544 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 4442) ∨ (¬ p 3868) ∨ (p 2528) ∨ (¬ p 2363) ∨ (¬ p 4105) :=
  ElevenRUP.step114544 (p 2363) (p 2528) (p 2911) (p 3868) (p 4105) (p 4186) (p 4442) (derived101498 p h) (derived91169 p h)

theorem derived114545 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 3389) ∨ (p 2528) ∨ (¬ p 2662) ∨ (p 2727) ∨ (¬ p 2459) :=
  ElevenRUP.step114545 (p 2459) (p 2528) (p 2662) (p 2727) (p 2911) (p 3389) (p 4186) (derived101664 p h) (derived91169 p h)

theorem derived114547 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3641) ∨ (¬ p 2098) ∨ (p 2437) ∨ (p 2440) ∨ (p 2598) :=
  ElevenRUP.step114547 (p 2098) (p 2437) (p 2440) (p 2598) (p 2911) (p 3641) (p 4186) (derived111134 p h) (derived91169 p h)

theorem derived114554 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3998) ∨ (p 3654) ∨ (p 4149) ∨ (¬ p 4710) ∨ (¬ p 4114) ∨ (¬ p 4620) :=
  ElevenRUP.step114554 (p 2911) (p 3654) (p 3998) (p 4114) (p 4149) (p 4186) (p 4620) (p 4710) (derived89956 p h) (derived91169 p h)

theorem derived114564 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (p 3389) ∨ (¬ p 2459) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 2619) :=
  ElevenRUP.step114564 (p 2459) (p 2528) (p 2608) (p 2619) (p 2839) (p 2911) (p 3389) (p 4186) (p 4902) (p 5193) (derived105456 p h) (derived105488 p h) (derived83767 p h) (derived91169 p h)

theorem derived114565 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (¬ p 2132) ∨ (p 3389) ∨ (¬ p 2187) ∨ (¬ p 2459) ∨ (¬ p 2860) :=
  ElevenRUP.step114565 (p 2132) (p 2187) (p 2459) (p 2528) (p 2860) (p 2911) (p 3389) (p 4133) (p 4186) (p 4729) (derived105712 p h) (derived105429 p h) (derived90692 p h) (derived91169 p h)

theorem derived114567 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 2819) ∨ (p 3389) ∨ (¬ p 2829) ∨ (¬ p 2608) :=
  ElevenRUP.step114567 (p 2459) (p 2528) (p 2608) (p 2819) (p 2829) (p 2911) (p 3389) (p 4133) (p 4186) (p 5193) (derived105488 p h) (derived105712 p h) (derived95245 p h) (derived91169 p h)

theorem derived114568 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2166) ∨ (p 2528) ∨ (¬ p 2210) ∨ (p 3389) ∨ (¬ p 3347) ∨ (p 2608) ∨ (¬ p 2459) :=
  ElevenRUP.step114568 (p 2166) (p 2210) (p 2459) (p 2528) (p 2608) (p 2911) (p 3347) (p 3389) (p 4186) (p 4902) (derived105456 p h) (derived101672 p h) (derived91169 p h)

theorem derived114572 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2459) ∨ (¬ p 3156) ∨ (p 2528) ∨ (p 3389) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 2753) ∨ (¬ p 3347) :=
  ElevenRUP.step114572 (p 2459) (p 2528) (p 2696) (p 2753) (p 2911) (p 3136) (p 3156) (p 3347) (p 3389) (p 4186) (p 4902) (derived105456 p h) (derived84323 p h) (derived91169 p h)

theorem derived114581 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2727) ∨ (¬ p 4311) ∨ (p 2528) ∨ (p 3389) ∨ (p 3136) ∨ (¬ p 2246) ∨ (¬ p 3005) ∨ (¬ p 3347) ∨ (¬ p 2946) ∨ (¬ p 2459) :=
  ElevenRUP.step114581 (p 2246) (p 2459) (p 2528) (p 2727) (p 2911) (p 2946) (p 3005) (p 3136) (p 3347) (p 3389) (p 4186) (p 4311) (derived108386 p h) (derived91169 p h)

theorem derived114584 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (p 2528) ∨ (p 3389) ∨ (p 2608) ∨ (¬ p 2655) ∨ (¬ p 2252) ∨ (¬ p 3322) ∨ (¬ p 2459) :=
  ElevenRUP.step114584 (p 2252) (p 2459) (p 2528) (p 2608) (p 2655) (p 2750) (p 2911) (p 3093) (p 3319) (p 3322) (p 3389) (p 4133) (p 4186) (derived106345 p h) (derived105712 p h) (derived91871 p h) (derived91169 p h)

theorem derived114586 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2187) ∨ (¬ p 2459) ∨ (p 2528) ∨ (p 3389) ∨ (p 2860) ∨ (¬ p 2156) ∨ (¬ p 2753) ∨ (¬ p 2655) ∨ (¬ p 2619) ∨ (¬ p 2144) ∨ (¬ p 2252) :=
  ElevenRUP.step114586 (p 2144) (p 2156) (p 2187) (p 2252) (p 2459) (p 2528) (p 2619) (p 2655) (p 2753) (p 2860) (p 2911) (p 3389) (p 4186) (derived114441 p h) (derived91169 p h)

theorem derived114588 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2922) ∨ (¬ p 3590) :=
  ElevenRUP.step114588 (p 2922) (p 3201) (p 3590) (p 4106) (derived111394 p h) (derived97816 p h)

theorem derived114589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2482) ∨ (¬ p 2584) :=
  ElevenRUP.step114589 (p 2383) (p 2482) (p 2584) (p 4114) (h 18921) (derived96434 p h)

theorem derived114590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3178) ∨ (¬ p 3987) :=
  ElevenRUP.step114590 (p 2383) (p 3178) (p 3987) (p 4114) (h 19439) (derived96434 p h)

theorem derived114593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 4113) ∨ (p 2307) ∨ (¬ p 3955) :=
  ElevenRUP.step114593 (p 2307) (p 2383) (p 3955) (p 4113) (p 4114) (derived78487 p h) (derived96434 p h)

theorem derived114596 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2088) ∨ (p 2307) ∨ (p 2363) :=
  ElevenRUP.step114596 (p 2088) (p 2307) (p 2363) (p 2383) (p 4114) (p 4405) (derived105512 p h) (derived78456 p h) (derived96434 p h)

theorem derived114598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2363) ∨ (p 2819) ∨ (¬ p 2088) :=
  ElevenRUP.step114598 (p 2088) (p 2363) (p 2383) (p 2788) (p 2819) (p 4114) (derived105375 p h) (derived93333 p h) (derived96434 p h)

theorem derived114599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2363) ∨ (¬ p 3923) ∨ (¬ p 2088) :=
  ElevenRUP.step114599 (p 2088) (p 2363) (p 2383) (p 3923) (p 4114) (p 5022) (derived105470 p h) (derived96163 p h) (derived96434 p h)

theorem derived114602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2352) ∨ (p 2363) ∨ (¬ p 5016) ∨ (¬ p 2507) ∨ (¬ p 2088) :=
  ElevenRUP.step114602 (p 2088) (p 2352) (p 2363) (p 2383) (p 2507) (p 4114) (p 5016) (derived78452 p h) (derived96434 p h)

theorem derived114604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2363) ∨ (¬ p 2088) ∨ (¬ p 3955) ∨ (p 2295) :=
  ElevenRUP.step114604 (p 2088) (p 2295) (p 2363) (p 2383) (p 3955) (p 4114) (p 4584) (derived105406 p h) (derived78468 p h) (derived96434 p h)

theorem derived114605 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3743) ∨ (¬ p 2088) ∨ (p 2363) ∨ (p 2274) :=
  ElevenRUP.step114605 (p 2088) (p 2274) (p 2363) (p 2383) (p 3743) (p 4114) (p 4405) (derived105512 p h) (derived78469 p h) (derived96434 p h)

theorem derived114606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2363) ∨ (¬ p 2088) ∨ (p 2274) ∨ (¬ p 3955) :=
  ElevenRUP.step114606 (p 2088) (p 2274) (p 2363) (p 2383) (p 3955) (p 4114) (p 4489) (derived105390 p h) (derived78470 p h) (derived96434 p h)

theorem derived114613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2829) ∨ (p 2608) ∨ (p 2819) ∨ (¬ p 4113) ∨ (¬ p 5017) :=
  ElevenRUP.step114613 (p 2383) (p 2608) (p 2819) (p 2829) (p 4113) (p 4114) (p 5017) (derived90577 p h) (derived96434 p h)

theorem derived114614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2797) ∨ (¬ p 2088) ∨ (p 2363) ∨ (p 2630) ∨ (¬ p 3567) :=
  ElevenRUP.step114614 (p 2088) (p 2363) (p 2383) (p 2630) (p 2797) (p 3567) (p 4114) (derived92262 p h) (derived96434 p h)

theorem derived114615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 4364) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 3567) ∨ (¬ p 2630) :=
  ElevenRUP.step114615 (p 2088) (p 2383) (p 2630) (p 3567) (p 3609) (p 4114) (p 4364) (derived107419 p h) (derived96434 p h)

theorem derived114617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3256) ∨ (¬ p 2088) ∨ (p 3189) ∨ (¬ p 3987) :=
  ElevenRUP.step114617 (p 2088) (p 2255) (p 2383) (p 3189) (p 3256) (p 3987) (p 4114) (derived105367 p h) (derived100548 p h) (derived96434 p h)

theorem derived114618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3189) ∨ (¬ p 2088) ∨ (p 3073) ∨ (¬ p 3567) ∨ (¬ p 2797) :=
  ElevenRUP.step114618 (p 2088) (p 2383) (p 2797) (p 3073) (p 3189) (p 3567) (p 4114) (derived110255 p h) (derived96434 p h)

theorem derived114620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2668) ∨ (¬ p 2088) ∨ (¬ p 2578) ∨ (p 2553) ∨ (p 3256) :=
  ElevenRUP.step114620 (p 2088) (p 2383) (p 2553) (p 2578) (p 2668) (p 3256) (p 4114) (derived112355 p h) (derived96434 p h)

theorem derived114629 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3073) ∨ (¬ p 2088) ∨ (¬ p 2891) ∨ (¬ p 3743) ∨ (¬ p 4492) :=
  ElevenRUP.step114629 (p 2088) (p 2383) (p 2891) (p 3073) (p 3743) (p 4114) (p 4492) (p 4558) (derived105400 p h) (derived94605 p h) (derived96434 p h)

theorem derived114640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2911) ∨ (¬ p 3998) ∨ (p 3654) ∨ (p 4149) ∨ (¬ p 4710) ∨ (¬ p 4620) :=
  ElevenRUP.step114640 (p 2383) (p 2911) (p 3654) (p 3998) (p 4114) (p 4149) (p 4620) (p 4710) (derived114554 p h) (derived96434 p h)

theorem derived114644 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2619) ∨ (¬ p 3537) ∨ (p 3073) ∨ (¬ p 2088) ∨ (¬ p 3096) ∨ (¬ p 2578) ∨ (¬ p 2870) :=
  ElevenRUP.step114644 (p 2088) (p 2383) (p 2578) (p 2619) (p 2870) (p 3073) (p 3096) (p 3537) (p 4114) (derived112000 p h) (derived96434 p h)

theorem derived114648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2707) ∨ (p 3537) ∨ (p 2901) ∨ (p 2946) ∨ (p 2881) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 5020) :=
  ElevenRUP.step114648 (p 2088) (p 2254) (p 2383) (p 2707) (p 2881) (p 2901) (p 2946) (p 3537) (p 3609) (p 4114) (p 5020) (derived105366 p h) (derived78489 p h) (derived96434 p h)

theorem derived114650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2088) ∨ (p 2992) ∨ (¬ p 2779) ∨ (p 2363) ∨ (¬ p 2829) ∨ (¬ p 2748) ∨ (p 3156) ∨ (p 2696) :=
  ElevenRUP.step114650 (p 2088) (p 2363) (p 2383) (p 2696) (p 2748) (p 2779) (p 2829) (p 2992) (p 3156) (p 4114) (p 4134) (derived105379 p h) (derived95716 p h) (derived96434 p h)

theorem derived114652 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2619) ∨ (p 3156) ∨ (p 3609) ∨ (¬ p 5017) ∨ (¬ p 2088) ∨ (¬ p 2870) ∨ (¬ p 2190) ∨ (p 2992) ∨ (p 2241) :=
  ElevenRUP.step114652 (p 2088) (p 2190) (p 2241) (p 2383) (p 2619) (p 2870) (p 2992) (p 3156) (p 3609) (p 4114) (p 5017) (derived112008 p h) (derived96434 p h)

theorem derived114656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2363) ∨ (p 2922) ∨ (p 2911) ∨ (¬ p 2641) ∨ (¬ p 2088) ∨ (¬ p 3567) ∨ (¬ p 3487) ∨ (p 2651) :=
  ElevenRUP.step114656 (p 2088) (p 2249) (p 2363) (p 2383) (p 2641) (p 2651) (p 2911) (p 2922) (p 3487) (p 3567) (p 4114) (p 4133) (derived105712 p h) (derived106513 p h) (derived98180 p h) (derived96434 p h)

theorem derived114663 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 5580) ∨ (¬ p 3998) ∨ (p 2881) ∨ (¬ p 2797) ∨ (p 3201) ∨ (¬ p 3567) ∨ (¬ p 2363) ∨ (p 2651) ∨ (¬ p 4001) ∨ (¬ p 2252) ∨ (¬ p 3683) :=
  ElevenRUP.step114663 (p 2252) (p 2363) (p 2383) (p 2651) (p 2745) (p 2797) (p 2881) (p 3201) (p 3567) (p 3683) (p 3998) (p 4001) (p 4114) (p 5580) (derived105523 p h) (derived101488 p h) (derived96434 p h)

theorem derived114667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2482) ∨ (¬ p 5201) :=
  ElevenRUP.step114667 (p 2341) (p 2482) (p 4590) (p 5201) (h 22275) (derived96447 p h)

theorem derived114668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 4238) ∨ (¬ p 4988) :=
  ElevenRUP.step114668 (p 2341) (p 4238) (p 4590) (p 4988) (h 40137) (derived96447 p h)

theorem derived114669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 5242) ∨ (¬ p 3545) :=
  ElevenRUP.step114669 (p 2341) (p 3545) (p 4590) (p 5242) (h 25582) (derived96447 p h)

theorem derived114672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2717) ∨ (¬ p 3577) ∨ (¬ p 4403) :=
  ElevenRUP.step114672 (p 2341) (p 2717) (p 3577) (p 4403) (p 4590) (derived95778 p h) (derived96447 p h)

theorem derived114673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 5558) ∨ (¬ p 3998) ∨ (p 2911) :=
  ElevenRUP.step114673 (p 2341) (p 2911) (p 3998) (p 4590) (p 5203) (p 5558) (derived105490 p h) (derived89418 p h) (derived96447 p h)

theorem derived114674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3819) ∨ (¬ p 2088) ∨ (p 3609) ∨ (p 3537) :=
  ElevenRUP.step114674 (p 2088) (p 2341) (p 3537) (p 3609) (p 3819) (p 4590) (derived89904 p h) (derived96447 p h)

theorem derived114676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2459) ∨ (¬ p 2088) ∨ (¬ p 5261) ∨ (p 2717) :=
  ElevenRUP.step114676 (p 2088) (p 2341) (p 2459) (p 2717) (p 4590) (p 5261) (derived95332 p h) (derived96447 p h)

theorem derived114677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2459) ∨ (¬ p 2088) ∨ (¬ p 4854) ∨ (p 2264) :=
  ElevenRUP.step114677 (p 2088) (p 2264) (p 2341) (p 2459) (p 4590) (p 4854) (derived96664 p h) (derived96447 p h)

theorem derived114679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 3998) ∨ (p 3516) ∨ (¬ p 5558) :=
  ElevenRUP.step114679 (p 2341) (p 2396) (p 3516) (p 3998) (p 4590) (p 5558) (derived101550 p h) (derived96447 p h)

theorem derived114681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4391) ∨ (¬ p 2088) ∨ (p 2459) ∨ (¬ p 4066) :=
  ElevenRUP.step114681 (p 2088) (p 2341) (p 2459) (p 4066) (p 4391) (p 4590) (p 5559) (derived106189 p h) (derived74612 p h) (derived96447 p h)

theorem derived114684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2088) ∨ (¬ p 3577) ∨ (¬ p 2707) ∨ (p 2459) ∨ (p 2737) :=
  ElevenRUP.step114684 (p 2088) (p 2341) (p 2459) (p 2707) (p 2737) (p 3577) (p 4590) (derived81306 p h) (derived96447 p h)

theorem derived114687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4492) ∨ (¬ p 2088) ∨ (¬ p 2427) ∨ (p 3073) ∨ (¬ p 3691) :=
  ElevenRUP.step114687 (p 2088) (p 2341) (p 2427) (p 3073) (p 3691) (p 4492) (p 4590) (derived107422 p h) (derived96447 p h)

theorem derived114689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3189) ∨ (p 3256) ∨ (¬ p 2088) ∨ (¬ p 4104) :=
  ElevenRUP.step114689 (p 2088) (p 2255) (p 2341) (p 3189) (p 3256) (p 4104) (p 4590) (derived105367 p h) (derived100549 p h) (derived96447 p h)

theorem derived114702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4364) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 4066) ∨ (p 2996) :=
  ElevenRUP.step114702 (p 2088) (p 2341) (p 2751) (p 2996) (p 3609) (p 4066) (p 4364) (p 4590) (derived106343 p h) (derived82146 p h) (derived96447 p h)

theorem derived114703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2619) ∨ (¬ p 4115) ∨ (p 3516) ∨ (¬ p 3741) ∨ (¬ p 2417) :=
  ElevenRUP.step114703 (p 2341) (p 2417) (p 2619) (p 3516) (p 3741) (p 4115) (p 4590) (p 4882) (derived105453 p h) (derived84795 p h) (derived96447 p h)

theorem derived114705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4371) ∨ (p 3073) ∨ (¬ p 2274) ∨ (¬ p 2312) ∨ (¬ p 2088) ∨ (¬ p 4514) :=
  ElevenRUP.step114705 (p 2088) (p 2274) (p 2312) (p 2341) (p 3073) (p 4371) (p 4514) (p 4590) (derived87556 p h) (derived96447 p h)

theorem derived114709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3073) ∨ (¬ p 2088) ∨ (¬ p 4757) ∨ (¬ p 2312) ∨ (¬ p 4371) ∨ (¬ p 2295) :=
  ElevenRUP.step114709 (p 2088) (p 2295) (p 2312) (p 2341) (p 3073) (p 4371) (p 4590) (p 4757) (derived91826 p h) (derived96447 p h)

theorem derived114713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3189) ∨ (¬ p 2088) ∨ (p 3073) ∨ (¬ p 4066) ∨ (¬ p 2727) ∨ (¬ p 4650) :=
  ElevenRUP.step114713 (p 2088) (p 2341) (p 2727) (p 3073) (p 3189) (p 4066) (p 4590) (p 4650) (derived110251 p h) (derived96447 p h)

theorem derived114715 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3189) ∨ (¬ p 2088) ∨ (p 3073) ∨ (¬ p 2951) ∨ (¬ p 4988) ∨ (¬ p 3136) :=
  ElevenRUP.step114715 (p 2088) (p 2341) (p 2951) (p 3073) (p 3136) (p 3189) (p 4590) (p 4988) (derived110257 p h) (derived96447 p h)

theorem derived114731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2619) ∨ (p 3609) ∨ (p 2493) ∨ (p 3379) ∨ (¬ p 2860) ∨ (¬ p 2088) ∨ (¬ p 3660) ∨ (p 2427) :=
  ElevenRUP.step114731 (p 2088) (p 2341) (p 2427) (p 2493) (p 2619) (p 2860) (p 3379) (p 3609) (p 3660) (p 4590) (derived112009 p h) (derived96447 p h)

theorem derived114743 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3654) ∨ (p 3483) :=
  ElevenRUP.step114743 (p 2774) (p 2779) (p 3483) (p 3654) (h 6560) (derived96911 p h)

theorem derived114744 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2819) ∨ (¬ p 2383) :=
  ElevenRUP.step114744 (p 2383) (p 2774) (p 2779) (p 2819) (derived95713 p h) (derived96911 p h)

theorem derived114745 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 4390) ∨ (¬ p 2386) :=
  ElevenRUP.step114745 (p 2386) (p 2774) (p 2779) (p 4390) (h 21431) (derived96911 p h)

theorem derived114746 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2307) ∨ (p 2122) :=
  ElevenRUP.step114746 (p 2122) (p 2307) (p 2774) (p 2779) (derived95727 p h) (derived96911 p h)

theorem derived114747 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3325) ∨ (¬ p 2307) ∨ (p 2819) :=
  ElevenRUP.step114747 (p 2307) (p 2774) (p 2779) (p 2819) (p 3325) (derived95718 p h) (derived96911 p h)

theorem derived114753 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2829) ∨ (¬ p 2177) ∨ (p 2737) ∨ (¬ p 2307) :=
  ElevenRUP.step114753 (p 2177) (p 2307) (p 2737) (p 2774) (p 2779) (p 2829) (derived81293 p h) (derived96911 p h)

theorem derived114759 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3461) ∨ (¬ p 3654) ∨ (p 2737) ∨ (¬ p 2829) :=
  ElevenRUP.step114759 (p 2737) (p 2774) (p 2779) (p 2829) (p 3461) (p 3654) (derived95711 p h) (derived96911 p h)

theorem derived114760 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2307) ∨ (p 2553) ∨ (p 3367) ∨ (¬ p 2829) :=
  ElevenRUP.step114760 (p 2307) (p 2553) (p 2774) (p 2779) (p 2829) (p 3367) (derived95719 p h) (derived96911 p h)

theorem derived114764 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2761) ∨ (¬ p 2396) ∨ (¬ p 2829) ∨ (¬ p 2307) :=
  ElevenRUP.step114764 (p 2307) (p 2396) (p 2761) (p 2774) (p 2779) (p 2829) (derived46120 p h) (derived96911 p h)

theorem derived114765 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3979) ∨ (¬ p 2383) ∨ (p 2122) ∨ (¬ p 5558) :=
  ElevenRUP.step114765 (p 2122) (p 2383) (p 2774) (p 2779) (p 3979) (p 5558) (derived97902 p h) (derived96911 p h)

theorem derived114766 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2383) ∨ (¬ p 2829) ∨ (p 2839) ∨ (¬ p 2363) :=
  ElevenRUP.step114766 (p 2363) (p 2383) (p 2774) (p 2779) (p 2829) (p 2839) (derived101494 p h) (derived96911 p h)

theorem derived114767 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2363) ∨ (¬ p 3979) ∨ (¬ p 3917) ∨ (¬ p 2383) :=
  ElevenRUP.step114767 (p 2363) (p 2383) (p 2774) (p 2779) (p 3917) (p 3979) (derived111684 p h) (derived96911 p h)

theorem derived114770 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3516) ∨ (¬ p 2319) ∨ (¬ p 2829) ∨ (p 2396) ∨ (¬ p 2177) :=
  ElevenRUP.step114770 (p 2177) (p 2319) (p 2396) (p 2774) (p 2779) (p 2829) (p 3516) (derived86910 p h) (derived96911 p h)

theorem derived114773 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2563) ∨ (¬ p 4356) ∨ (p 2839) ∨ (¬ p 2829) ∨ (¬ p 4885) :=
  ElevenRUP.step114773 (p 2563) (p 2774) (p 2779) (p 2829) (p 2839) (p 4356) (p 4885) (derived95700 p h) (derived96911 p h)

theorem derived114774 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3923) ∨ (¬ p 4842) ∨ (¬ p 2383) ∨ (¬ p 3953) ∨ (¬ p 2737) :=
  ElevenRUP.step114774 (p 2383) (p 2737) (p 2774) (p 2779) (p 3923) (p 3953) (p 4842) (derived42325 p h) (derived96911 p h)

theorem derived114775 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3953) ∨ (¬ p 2307) ∨ (¬ p 4842) ∨ (¬ p 2737) ∨ (p 3309) :=
  ElevenRUP.step114775 (p 2307) (p 2737) (p 2774) (p 2779) (p 3309) (p 3953) (p 4842) (derived95707 p h) (derived96911 p h)

theorem derived114781 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2829) ∨ (p 3367) ∨ (¬ p 2553) ∨ (¬ p 2386) ∨ (¬ p 2177) :=
  ElevenRUP.step114781 (p 2177) (p 2386) (p 2553) (p 2774) (p 2779) (p 2829) (p 3367) (derived95729 p h) (derived96911 p h)

theorem derived114783 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2437) ∨ (¬ p 2386) ∨ (p 2819) ∨ (¬ p 4710) ∨ (p 3016) :=
  ElevenRUP.step114783 (p 2386) (p 2437) (p 2774) (p 2779) (p 2819) (p 3016) (p 4710) (derived98082 p h) (derived96911 p h)

theorem derived114804 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2829) ∨ (¬ p 2177) ∨ (¬ p 2307) ∨ (p 2696) ∨ (p 3083) ∨ (¬ p 2748) ∨ (p 2727) :=
  ElevenRUP.step114804 (p 2177) (p 2307) (p 2696) (p 2727) (p 2748) (p 2774) (p 2779) (p 2829) (p 3083) (derived107583 p h) (derived96911 p h)

theorem derived114807 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2829) ∨ (¬ p 2307) ∨ (¬ p 2396) ∨ (p 2406) ∨ (p 2598) ∨ (p 2982) ∨ (¬ p 4030) :=
  ElevenRUP.step114807 (p 2307) (p 2396) (p 2406) (p 2598) (p 2774) (p 2779) (p 2829) (p 2982) (p 3951) (p 4030) (derived106536 p h) (derived81118 p h) (derived96911 p h)

theorem derived114808 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 3256) ∨ (¬ p 2307) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (p 2696) ∨ (¬ p 2748) ∨ (¬ p 2829) ∨ (p 3189) :=
  ElevenRUP.step114808 (p 2307) (p 2396) (p 2696) (p 2748) (p 2774) (p 2779) (p 2829) (p 3189) (p 3256) (p 3950) (derived82717 p h) (derived96911 p h)

theorem derived114810 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2860) ∨ (¬ p 3564) ∨ (¬ p 2696) ∨ (p 2274) ∨ (p 2598) ∨ (¬ p 3125) ∨ (¬ p 5160) ∨ (¬ p 2307) :=
  ElevenRUP.step114810 (p 2274) (p 2307) (p 2598) (p 2696) (p 2774) (p 2779) (p 2860) (p 3125) (p 3564) (p 5160) (derived113540 p h) (derived96911 p h)

theorem derived114811 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2860) ∨ (¬ p 2417) ∨ (¬ p 5160) ∨ (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3654) ∨ (¬ p 2696) ∨ (p 2598) :=
  ElevenRUP.step114811 (p 2417) (p 2598) (p 2696) (p 2761) (p 2774) (p 2779) (p 2860) (p 3461) (p 3654) (p 5160) (derived113541 p h) (derived96911 p h)

theorem derived114813 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2383) ∨ (¬ p 2088) ∨ (p 2992) ∨ (p 2363) ∨ (¬ p 2829) ∨ (¬ p 2748) ∨ (p 3156) ∨ (p 2696) :=
  ElevenRUP.step114813 (p 2088) (p 2363) (p 2383) (p 2696) (p 2748) (p 2774) (p 2779) (p 2829) (p 2992) (p 3156) (derived114650 p h) (derived96911 p h)

theorem derived114823 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2363) ∨ (¬ p 2088) :=
  ElevenRUP.step114823 (p 2088) (p 2363) (p 2383) (p 3322) (derived112711 p h) (derived96437 p h)

theorem derived114825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2992) ∨ (p 2727) :=
  ElevenRUP.step114825 (p 2440) (p 2727) (p 2992) (p 4700) (derived81805 p h) (derived100363 p h)

theorem derived114826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2946) ∨ (p 2651) :=
  ElevenRUP.step114826 (p 2440) (p 2651) (p 2946) (p 4700) (derived83037 p h) (derived100363 p h)

theorem derived114828 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 3878) ∨ (¬ p 3661) :=
  ElevenRUP.step114828 (p 2440) (p 3661) (p 3878) (p 4700) (h 32126) (derived100363 p h)

theorem derived114829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3136) ∨ (p 2630) :=
  ElevenRUP.step114829 (p 2440) (p 2630) (p 3136) (p 4700) (derived84307 p h) (derived100363 p h)

theorem derived114831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 5062) :=
  ElevenRUP.step114831 (p 2440) (p 4700) (p 5008) (p 5062) (derived105469 p h) (h 31515) (derived100363 p h)

theorem derived114836 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 6116) ∨ (¬ p 5740) ∨ (¬ p 3016) :=
  ElevenRUP.step114836 (p 2440) (p 3016) (p 4700) (p 5740) (p 6116) (derived110778 p h) (derived100363 p h)

theorem derived114841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 3156) ∨ (¬ p 2373) ∨ (¬ p 2850) :=
  ElevenRUP.step114841 (p 2373) (p 2440) (p 2850) (p 3156) (p 4700) (p 4753) (derived105514 p h) (derived79139 p h) (derived100363 p h)

theorem derived114842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3564) ∨ (p 2284) ∨ (p 3125) ∨ (p 2553) :=
  ElevenRUP.step114842 (p 2284) (p 2440) (p 2553) (p 3125) (p 3564) (p 4700) (derived79507 p h) (derived100363 p h)

theorem derived114843 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2284) ∨ (p 2241) ∨ (¬ p 2563) ∨ (p 2727) :=
  ElevenRUP.step114843 (p 2241) (p 2284) (p 2440) (p 2563) (p 2727) (p 4700) (derived80838 p h) (derived100363 p h)

theorem derived114845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2563) ∨ (p 2727) ∨ (¬ p 2427) ∨ (p 2901) :=
  ElevenRUP.step114845 (p 2427) (p 2440) (p 2563) (p 2727) (p 2901) (p 4700) (derived83044 p h) (derived100363 p h)

theorem derived114846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2284) ∨ (¬ p 2437) ∨ (¬ p 2563) :=
  ElevenRUP.step114846 (p 2284) (p 2437) (p 2440) (p 2563) (p 4646) (p 4700) (derived105534 p h) (derived83046 p h) (derived100363 p h)

theorem derived114847 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 3156) ∨ (¬ p 2373) ∨ (¬ p 3016) :=
  ElevenRUP.step114847 (p 2373) (p 2440) (p 3016) (p 3156) (p 4700) (p 4717) (derived105424 p h) (derived83047 p h) (derived100363 p h)

theorem derived114848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2284) ∨ (¬ p 3343) ∨ (¬ p 2563) ∨ (¬ p 4953) :=
  ElevenRUP.step114848 (p 2284) (p 2440) (p 2563) (p 3343) (p 4700) (p 4953) (derived83052 p h) (derived100363 p h)

theorem derived114849 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 4365) ∨ (p 3115) ∨ (¬ p 2972) ∨ (p 2641) :=
  ElevenRUP.step114849 (p 2440) (p 2641) (p 2972) (p 3115) (p 4365) (p 4700) (derived107266 p h) (derived100363 p h)

theorem derived114850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3051) ∨ (p 2331) ∨ (p 2901) ∨ (¬ p 2958) :=
  ElevenRUP.step114850 (p 2331) (p 2440) (p 2901) (p 2958) (p 3051) (p 4700) (derived107328 p h) (derived100363 p h)

theorem derived114851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 3156) ∨ (p 2331) ∨ (¬ p 2220) ∨ (¬ p 2958) :=
  ElevenRUP.step114851 (p 2220) (p 2331) (p 2440) (p 2958) (p 3156) (p 4700) (derived107330 p h) (derived100363 p h)

theorem derived114854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2284) ∨ (¬ p 2509) ∨ (¬ p 3083) ∨ (¬ p 2563) :=
  ElevenRUP.step114854 (p 2284) (p 2440) (p 2509) (p 2563) (p 3083) (p 4700) (derived98823 p h) (derived100363 p h)

theorem derived114855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2619) ∨ (p 3156) ∨ (¬ p 4313) ∨ (p 2797) :=
  ElevenRUP.step114855 (p 2440) (p 2619) (p 2797) (p 3156) (p 4313) (p 4700) (derived107359 p h) (derived100363 p h)

theorem derived114857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 4228) ∨ (¬ p 3888) ∨ (¬ p 4153) ∨ (¬ p 3422) :=
  ElevenRUP.step114857 (p 2440) (p 3422) (p 3888) (p 4153) (p 4228) (p 4700) (derived110225 p h) (derived100363 p h)

theorem derived114861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2901) ∨ (p 2727) ∨ (¬ p 4313) ∨ (¬ p 2870) :=
  ElevenRUP.step114861 (p 2440) (p 2727) (p 2745) (p 2870) (p 2901) (p 4313) (p 4700) (derived105523 p h) (derived82523 p h) (derived100363 p h)

theorem derived114866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2156) ∨ (p 2284) ∨ (¬ p 4109) ∨ (¬ p 2406) :=
  ElevenRUP.step114866 (p 2156) (p 2284) (p 2406) (p 2440) (p 4109) (p 4700) (p 4814) (derived105440 p h) (derived83054 p h) (derived100363 p h)

theorem derived114867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2284) ∨ (¬ p 2156) ∨ (¬ p 2850) ∨ (¬ p 4109) :=
  ElevenRUP.step114867 (p 2156) (p 2284) (p 2440) (p 2850) (p 4109) (p 4700) (p 4753) (derived105514 p h) (derived83056 p h) (derived100363 p h)

theorem derived114868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3051) ∨ (p 2901) ∨ (¬ p 4109) ∨ (¬ p 2406) :=
  ElevenRUP.step114868 (p 2406) (p 2440) (p 2901) (p 3051) (p 4109) (p 4700) (p 4814) (derived105440 p h) (derived83062 p h) (derived100363 p h)

theorem derived114870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3051) ∨ (¬ p 4109) ∨ (p 2901) ∨ (¬ p 2850) :=
  ElevenRUP.step114870 (p 2440) (p 2850) (p 2901) (p 3051) (p 4109) (p 4700) (p 4753) (derived105514 p h) (derived83066 p h) (derived100363 p h)

theorem derived114872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 4313) ∨ (¬ p 2957) ∨ (p 3051) ∨ (¬ p 2870) ∨ (p 2797) :=
  ElevenRUP.step114872 (p 2440) (p 2797) (p 2870) (p 2957) (p 3051) (p 4313) (p 4700) (derived107398 p h) (derived100363 p h)

theorem derived114873 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 3115) ∨ (¬ p 4313) ∨ (p 2727) ∨ (¬ p 3105) :=
  ElevenRUP.step114873 (p 2440) (p 2727) (p 2745) (p 3105) (p 3115) (p 4313) (p 4700) (derived105523 p h) (derived87195 p h) (derived100363 p h)

theorem derived114875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2957) ∨ (p 3051) ∨ (¬ p 2427) ∨ (¬ p 2850) :=
  ElevenRUP.step114875 (p 2427) (p 2440) (p 2850) (p 2957) (p 3051) (p 4700) (p 4753) (derived105514 p h) (derived87770 p h) (derived100363 p h)

theorem derived114877 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2166) ∨ (¬ p 4365) ∨ (p 3156) ∨ (¬ p 3016) ∨ (¬ p 2241) :=
  ElevenRUP.step114877 (p 2166) (p 2241) (p 2440) (p 3016) (p 3156) (p 4365) (p 4700) (derived92344 p h) (derived100363 p h)

theorem derived114879 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2220) ∨ (¬ p 2156) ∨ (¬ p 4506) ∨ (p 2284) ∨ (p 2363) :=
  ElevenRUP.step114879 (p 2156) (p 2220) (p 2284) (p 2363) (p 2440) (p 4506) (p 4700) (derived92465 p h) (derived100363 p h)

theorem derived114883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3051) ∨ (p 2901) ∨ (¬ p 3016) ∨ (¬ p 4109) :=
  ElevenRUP.step114883 (p 2440) (p 2901) (p 3016) (p 3051) (p 4109) (p 4700) (p 4717) (derived105424 p h) (derived98215 p h) (derived100363 p h)

theorem derived114886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 6116) ∨ (¬ p 5740) ∨ (¬ p 4236) ∨ (p 2651) ∨ (p 2563) :=
  ElevenRUP.step114886 (p 2440) (p 2563) (p 2651) (p 4236) (p 4700) (p 5740) (p 6116) (derived110782 p h) (derived100363 p h)

theorem derived114887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3136) ∨ (¬ p 2839) ∨ (p 2737) ∨ (p 2685) ∨ (¬ p 4650) :=
  ElevenRUP.step114887 (p 2440) (p 2685) (p 2737) (p 2839) (p 3136) (p 4650) (p 4700) (derived112623 p h) (derived100363 p h)

theorem derived114888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3136) ∨ (¬ p 2132) ∨ (p 2797) ∨ (p 2696) ∨ (¬ p 4972) :=
  ElevenRUP.step114888 (p 2132) (p 2440) (p 2696) (p 2797) (p 3136) (p 4700) (p 4972) (derived112629 p h) (derived100363 p h)

theorem derived114893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3051) ∨ (p 2901) ∨ (¬ p 3083) ∨ (¬ p 4610) ∨ (¬ p 2137) ∨ (¬ p 3698) :=
  ElevenRUP.step114893 (p 2137) (p 2440) (p 2901) (p 3051) (p 3083) (p 3698) (p 4610) (p 4700) (derived90176 p h) (derived100363 p h)

theorem derived114896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 4198) ∨ (¬ p 2578) ∨ (¬ p 3422) ∨ (¬ p 3051) ∨ (p 2901) :=
  ElevenRUP.step114896 (p 2440) (p 2578) (p 2901) (p 3051) (p 3422) (p 4198) (p 4700) (p 4753) (derived105514 p h) (derived98219 p h) (derived100363 p h)

theorem derived114906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 3246) ∨ (¬ p 2761) ∨ (p 2493) ∨ (p 3379) ∨ (¬ p 3051) ∨ (¬ p 5514) :=
  ElevenRUP.step114906 (p 2493) (p 2761) (p 3051) (p 3246) (p 3379) (p 3461) (p 5254) (p 5514) (derived107504 p h) (derived102364 p h)

theorem derived114907 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 4228) ∨ (¬ p 2761) ∨ (p 2641) ∨ (p 3425) ∨ (¬ p 3434) ∨ (p 2241) :=
  ElevenRUP.step114907 (p 2241) (p 2641) (p 2761) (p 3425) (p 3434) (p 3461) (p 4228) (p 5254) (derived110230 p h) (derived102364 p h)

theorem derived114908 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 3193) ∨ (¬ p 3276) ∨ (¬ p 3379) ∨ (p 2946) ∨ (p 2284) ∨ (¬ p 4393) :=
  ElevenRUP.step114908 (p 2254) (p 2284) (p 2946) (p 3193) (p 3276) (p 3379) (p 3461) (p 4393) (p 5254) (derived105366 p h) (derived81648 p h) (derived102364 p h)

theorem derived114909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 3399) ∨ (¬ p 2761) ∨ (p 2860) ∨ (¬ p 3631) ∨ (¬ p 4393) ∨ (p 2132) :=
  ElevenRUP.step114909 (p 2132) (p 2761) (p 2860) (p 3399) (p 3461) (p 3631) (p 4393) (p 4736) (p 5254) (derived105431 p h) (derived83261 p h) (derived102364 p h)

theorem derived114911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 4329) ∨ (¬ p 2449) ∨ (¬ p 2761) ∨ (p 2829) ∨ (¬ p 2807) ∨ (p 2608) :=
  ElevenRUP.step114911 (p 2248) (p 2449) (p 2608) (p 2761) (p 2807) (p 2829) (p 3461) (p 4329) (p 5254) (derived105365 p h) (derived90502 p h) (derived102364 p h)

theorem derived114913 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (p 2493) ∨ (p 3379) ∨ (¬ p 3166) ∨ (¬ p 5514) :=
  ElevenRUP.step114913 (p 2248) (p 2493) (p 3166) (p 3256) (p 3266) (p 3379) (p 3461) (p 5254) (p 5514) (derived105365 p h) (derived94706 p h) (derived102364 p h)

theorem derived114914 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 5514) ∨ (¬ p 2449) ∨ (¬ p 2807) ∨ (p 3379) ∨ (¬ p 2761) ∨ (p 2493) :=
  ElevenRUP.step114914 (p 2248) (p 2449) (p 2493) (p 2761) (p 2807) (p 3379) (p 3461) (p 5254) (p 5514) (derived105365 p h) (derived94708 p h) (derived102364 p h)

theorem derived114915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 4393) ∨ (p 2284) ∨ (¬ p 2341) ∨ (p 2946) ∨ (¬ p 2459) ∨ (¬ p 3266) ∨ (¬ p 4850) :=
  ElevenRUP.step114915 (p 2284) (p 2341) (p 2459) (p 2946) (p 3266) (p 3461) (p 4393) (p 4850) (p 5254) (derived94710 p h) (derived102364 p h)

theorem derived114916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 3422) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (¬ p 3166) ∨ (¬ p 5514) ∨ (p 2598) :=
  ElevenRUP.step114916 (p 2598) (p 3166) (p 3256) (p 3266) (p 3422) (p 3461) (p 4786) (p 5254) (p 5514) (derived106425 p h) (derived94714 p h) (derived102364 p h)

theorem derived114917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 4393) ∨ (¬ p 2761) ∨ (p 2860) ∨ (¬ p 2417) ∨ (p 2132) ∨ (¬ p 4419) ∨ (¬ p 3389) :=
  ElevenRUP.step114917 (p 2132) (p 2417) (p 2761) (p 2860) (p 3389) (p 3461) (p 4393) (p 4419) (p 5254) (derived96101 p h) (derived102364 p h)

end ElevenLogic
