import SunPrize.Certificate.Derived035
import SunPrize.Certificate.Logic036
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived78732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3661) ∨ (p 3256) ∨ (¬ p 2284) ∨ (¬ p 3146) :=
  ElevenRUP.step78732 (p 2284) (p 3146) (p 3256) (p 3661) (p 4118) (derived73520 p h) (derived69478 p h)

theorem derived78733 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3661) ∨ (¬ p 5053) ∨ (¬ p 2619) ∨ (¬ p 3146) :=
  ElevenRUP.step78733 (p 2619) (p 3146) (p 3256) (p 3661) (p 4118) (p 5053) (derived73520 p h) (derived41764 p h)

theorem derived78734 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2881) ∨ (¬ p 4559) ∨ (p 2459) ∨ (¬ p 3146) :=
  ElevenRUP.step78734 (p 2396) (p 2459) (p 2881) (p 3146) (p 4107) (p 4559) (p 4665) (p 4903) (derived73514 p h) (derived73820 p h) (derived73696 p h) (derived65751 p h)

theorem derived78738 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3747) ∨ (¬ p 4445) ∨ (p 3246) ∨ (¬ p 3146) :=
  ElevenRUP.step78738 (p 3146) (p 3246) (p 3690) (p 3747) (p 4445) (derived73446 p h) (h 39274)

theorem derived78739 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3747) ∨ (p 2459) ∨ (¬ p 3146) ∨ (¬ p 4277) :=
  ElevenRUP.step78739 (p 2459) (p 2911) (p 3146) (p 3644) (p 3747) (p 4277) (p 4348) (derived73434 p h) (derived73562 p h) (derived59137 p h)

theorem derived78741 (p : Nat → Prop) (h : Inputs p) :
    (p 2177) ∨ (¬ p 3747) ∨ (¬ p 3146) ∨ (p 2459) ∨ (¬ p 4559) :=
  ElevenRUP.step78741 (p 2177) (p 2299) (p 2459) (p 3146) (p 3747) (p 4348) (p 4559) (derived73234 p h) (derived73562 p h) (derived41325 p h)

theorem derived78742 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (p 2528) ∨ (¬ p 4370) ∨ (¬ p 3146) ∨ (¬ p 3379) :=
  ElevenRUP.step78742 (p 2528) (p 2534) (p 3146) (p 3379) (p 3449) (p 3860) (p 4370) (derived73482 p h) (derived73268 p h) (derived54888 p h)

theorem derived78744 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 4905) ∨ (¬ p 4445) ∨ (¬ p 2177) ∨ (¬ p 3146) :=
  ElevenRUP.step78744 (p 2177) (p 2396) (p 3146) (p 4107) (p 4445) (p 4905) (derived73514 p h) (derived41698 p h)

theorem derived78747 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2946) ∨ (¬ p 3146) ∨ (p 2459) :=
  ElevenRUP.step78747 (p 2459) (p 2946) (p 3146) (p 3156) (p 4348) (derived73562 p h) (derived44634 p h)

theorem derived78749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3412) ∨ (p 2641) ∨ (¬ p 2166) ∨ (¬ p 2946) ∨ (¬ p 3146) ∨ (p 2396) ∨ (¬ p 4669) ∨ (p 2307) ∨ (¬ p 2667) ∨ (¬ p 2255) :=
  ElevenRUP.step78749 (p 2166) (p 2255) (p 2307) (p 2313) (p 2396) (p 2641) (p 2667) (p 2946) (p 3146) (p 3412) (p 4107) (p 4154) (p 4669) (derived73526 p h) (derived73514 p h) (derived73238 p h) (derived56041 p h)

theorem derived78750 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3146) ∨ (¬ p 2166) ∨ (¬ p 4669) ∨ (p 2651) ∨ (p 2437) ∨ (¬ p 2210) ∨ (¬ p 2254) :=
  ElevenRUP.step78750 (p 2166) (p 2210) (p 2254) (p 2417) (p 2437) (p 2651) (p 2657) (p 3146) (p 3742) (p 4278) (p 4669) (derived73546 p h) (derived73288 p h) (derived73452 p h) (derived51955 p h)

theorem derived78754 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2264) ∨ (¬ p 3146) ∨ (¬ p 4445) ∨ (¬ p 4905) :=
  ElevenRUP.step78754 (p 2264) (p 2449) (p 3146) (p 3947) (p 4445) (p 4905) (derived73494 p h) (derived41890 p h)

theorem derived78755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3747) ∨ (p 2284) ∨ (p 2459) ∨ (¬ p 3146) :=
  ElevenRUP.step78755 (p 2284) (p 2459) (p 2901) (p 3146) (p 3747) (p 3952) (p 4348) (derived73496 p h) (derived73562 p h) (derived58062 p h)

theorem derived78756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (¬ p 3146) ∨ (¬ p 2563) :=
  ElevenRUP.step78756 (p 2284) (p 2563) (p 3146) (p 3156) (p 3952) (derived73496 p h) (derived47230 p h)

theorem derived78757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 2427) ∨ (p 3051) :=
  ElevenRUP.step78757 (p 2427) (p 2957) (p 3051) (p 3146) (p 3156) (p 3556) (derived73414 p h) (derived57945 p h)

theorem derived78758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (p 2363) ∨ (¬ p 2946) ∨ (¬ p 3156) :=
  ElevenRUP.step78758 (p 2363) (p 2946) (p 3146) (p 3156) (p 4347) (derived73560 p h) (derived43214 p h)

theorem derived78760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2668) ∨ (¬ p 4134) ∨ (p 2295) ∨ (p 2528) ∨ (¬ p 3146) ∨ (p 2470) ∨ (¬ p 2781) ∨ (¬ p 3905) :=
  ElevenRUP.step78760 (p 2295) (p 2307) (p 2470) (p 2476) (p 2528) (p 2534) (p 2668) (p 2781) (p 3146) (p 3568) (p 3905) (p 4134) (derived73416 p h) (derived73268 p h) (derived73250 p h) (derived58989 p h)

theorem derived78761 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 4236) ∨ (¬ p 3146) ∨ (p 3083) ∨ (p 2651) :=
  ElevenRUP.step78761 (p 2528) (p 2534) (p 2651) (p 2657) (p 3083) (p 3146) (p 4236) (p 4256) (derived73268 p h) (derived73542 p h) (derived73288 p h) (derived45656 p h)

theorem derived78762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4157) ∨ (p 2528) ∨ (¬ p 3923) ∨ (¬ p 3922) ∨ (¬ p 2190) ∨ (¬ p 3146) ∨ (¬ p 4564) :=
  ElevenRUP.step78762 (p 2190) (p 2528) (p 2534) (p 3146) (p 3922) (p 3923) (p 4157) (p 4564) (derived73268 p h) (derived57566 p h)

theorem derived78763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (p 2241) ∨ (¬ p 3366) ∨ (¬ p 2744) ∨ (¬ p 4134) ∨ (p 2470) ∨ (p 2528) ∨ (¬ p 3146) ∨ (¬ p 3905) ∨ (¬ p 3093) :=
  ElevenRUP.step78763 (p 2241) (p 2247) (p 2470) (p 2476) (p 2528) (p 2534) (p 2744) (p 3063) (p 3093) (p 3146) (p 3366) (p 3905) (p 4134) (derived73226 p h) (derived73250 p h) (derived73268 p h) (derived52998 p h)

theorem derived78767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 4733) ∨ (¬ p 3146) ∨ (¬ p 2177) ∨ (p 2528) ∨ (¬ p 4108) ∨ (p 2470) ∨ (¬ p 4905) :=
  ElevenRUP.step78767 (p 2122) (p 2177) (p 2470) (p 2476) (p 2528) (p 2534) (p 2774) (p 3146) (p 4108) (p 4733) (p 4905) (derived73268 p h) (derived73250 p h) (derived64084 p h)

theorem derived78770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4607) ∨ (¬ p 3146) ∨ (p 2528) ∨ (¬ p 4539) ∨ (¬ p 2220) :=
  ElevenRUP.step78770 (p 2220) (p 2528) (p 2534) (p 3146) (p 4539) (p 4607) (derived73268 p h) (derived50820 p h)

theorem derived78773 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3146) ∨ (¬ p 4186) ∨ (¬ p 4705) ∨ (¬ p 3156) ∨ (¬ p 2441) :=
  ElevenRUP.step78773 (p 2441) (p 2528) (p 2534) (p 3146) (p 3156) (p 4186) (p 4705) (derived73268 p h) (derived58446 p h)

theorem derived78774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2528) ∨ (p 2470) ∨ (¬ p 2177) ∨ (¬ p 4905) ∨ (¬ p 4786) ∨ (¬ p 3146) ∨ (¬ p 2331) ∨ (¬ p 3905) :=
  ElevenRUP.step78774 (p 2177) (p 2295) (p 2331) (p 2470) (p 2476) (p 2528) (p 2534) (p 3146) (p 3905) (p 4786) (p 4905) (derived73268 p h) (derived73250 p h) (derived52115 p h)

theorem derived78775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 2528) ∨ (¬ p 3146) ∨ (¬ p 2406) :=
  ElevenRUP.step78775 (p 2406) (p 2509) (p 2528) (p 2534) (p 3146) (derived73268 p h) (derived48987 p h)

theorem derived78777 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 4171) ∨ (¬ p 3146) ∨ (¬ p 2352) ∨ (¬ p 4134) :=
  ElevenRUP.step78777 (p 2352) (p 3146) (p 3564) (p 4134) (p 4137) (p 4171) (derived73524 p h) (derived41591 p h)

theorem derived78779 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2363) ∨ (¬ p 3146) ∨ (p 2668) :=
  ElevenRUP.step78779 (p 2295) (p 2363) (p 2668) (p 3146) (p 3324) (p 4347) (derived73560 p h) (derived73386 p h) (derived43295 p h)

theorem derived78783 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3146) ∨ (¬ p 2190) ∨ (p 2668) ∨ (¬ p 4564) :=
  ElevenRUP.step78783 (p 2190) (p 2363) (p 2668) (p 3146) (p 3324) (p 4347) (p 4564) (derived73560 p h) (derived73386 p h) (derived55133 p h)

theorem derived78787 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3146) ∨ (¬ p 2373) ∨ (¬ p 2230) :=
  ElevenRUP.step78787 (p 2230) (p 2363) (p 2373) (p 3146) (p 4347) (derived73560 p h) (derived42647 p h)

theorem derived78791 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3266) ∨ (¬ p 4905) ∨ (¬ p 3657) ∨ (¬ p 3146) ∨ (¬ p 4623) :=
  ElevenRUP.step78791 (p 3146) (p 3266) (p 3461) (p 3657) (p 4191) (p 4623) (p 4905) (derived73530 p h) (derived41401 p h)

theorem derived78793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 2641) ∨ (¬ p 3156) ∨ (p 2383) ∨ (¬ p 2667) ∨ (¬ p 2255) ∨ (¬ p 2946) ∨ (¬ p 5118) ∨ (¬ p 3146) :=
  ElevenRUP.step78793 (p 2255) (p 2383) (p 2387) (p 2641) (p 2667) (p 2946) (p 3146) (p 3156) (p 4154) (p 5118) (p 5580) (derived73526 p h) (derived73246 p h) (derived49676 p h)

theorem derived78795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3146) ∨ (p 2470) ∨ (¬ p 2241) ∨ (¬ p 5193) ∨ (¬ p 4134) ∨ (p 2528) :=
  ElevenRUP.step78795 (p 2241) (p 2470) (p 2476) (p 2528) (p 2534) (p 2641) (p 2668) (p 3146) (p 4134) (p 5193) (derived73250 p h) (derived73268 p h) (derived50284 p h)

theorem derived78796 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2459) ∨ (¬ p 3146) ∨ (p 2427) :=
  ElevenRUP.step78796 (p 2373) (p 2427) (p 2459) (p 3146) (p 4235) (p 4348) (derived73562 p h) (derived73536 p h) (derived45390 p h)

theorem derived78798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2427) ∨ (¬ p 3146) ∨ (¬ p 3266) :=
  ElevenRUP.step78798 (p 2373) (p 2427) (p 3146) (p 3266) (p 4235) (derived73536 p h) (derived60656 p h)

theorem derived78800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2651) ∨ (¬ p 3146) ∨ (¬ p 2440) ∨ (¬ p 4607) ∨ (p 2528) :=
  ElevenRUP.step78800 (p 2190) (p 2440) (p 2528) (p 2534) (p 2651) (p 2657) (p 3146) (p 4607) (derived73288 p h) (derived73268 p h) (derived61893 p h)

theorem derived78801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 4607) ∨ (p 2528) ∨ (¬ p 2427) ∨ (¬ p 4558) ∨ (¬ p 3146) :=
  ElevenRUP.step78801 (p 2190) (p 2427) (p 2528) (p 2534) (p 3146) (p 4558) (p 4607) (derived73268 p h) (derived50585 p h)

theorem derived78802 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3146) ∨ (¬ p 4669) ∨ (p 2922) ∨ (¬ p 2248) ∨ (p 2417) ∨ (¬ p 3156) ∨ (¬ p 2946) :=
  ElevenRUP.step78802 (p 2248) (p 2417) (p 2922) (p 2928) (p 2946) (p 3146) (p 3156) (p 3379) (p 3452) (p 4278) (p 4669) (derived73394 p h) (derived73320 p h) (derived73546 p h) (derived48416 p h)

theorem derived78803 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3146) ∨ (¬ p 2946) ∨ (¬ p 4604) ∨ (p 3564) ∨ (¬ p 3156) ∨ (p 2493) ∨ (¬ p 2248) :=
  ElevenRUP.step78803 (p 2248) (p 2493) (p 2499) (p 2946) (p 3146) (p 3156) (p 3379) (p 3452) (p 3564) (p 4137) (p 4604) (derived73394 p h) (derived73524 p h) (derived73260 p h) (derived48608 p h)

theorem derived78804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2088) ∨ (¬ p 3177) ∨ (p 3189) ∨ (¬ p 3146) :=
  ElevenRUP.step78804 (p 2088) (p 2992) (p 3146) (p 3177) (p 3189) (p 3857) (p 4360) (derived73480 p h) (derived73566 p h) (derived43771 p h)

theorem derived78806 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3146) ∨ (¬ p 2220) ∨ (p 2156) :=
  ElevenRUP.step78806 (p 2156) (p 2220) (p 2363) (p 3146) (p 3646) (p 4347) (derived73560 p h) (derived73436 p h) (derived46856 p h)

theorem derived78808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3201) ∨ (¬ p 4133) ∨ (p 2363) ∨ (¬ p 3146) ∨ (¬ p 3698) ∨ (p 2598) ∨ (p 2563) ∨ (p 2911) :=
  ElevenRUP.step78808 (p 2363) (p 2563) (p 2598) (p 2619) (p 2911) (p 3055) (p 3146) (p 3201) (p 3644) (p 3698) (p 3876) (p 4110) (p 4133) (p 4347) (derived73486 p h) (derived73560 p h) (derived73350 p h) (derived73516 p h) (derived73434 p h) (derived57508 p h)

theorem derived78811 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (p 2685) ∨ (¬ p 4419) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 2230) ∨ (p 2696) ∨ (¬ p 4669) :=
  ElevenRUP.step78811 (p 2230) (p 2373) (p 2449) (p 2685) (p 2696) (p 3146) (p 3365) (p 3572) (p 3947) (p 4419) (p 4669) (derived73494 p h) (derived73420 p h) (derived73390 p h) (derived52128 p h)

theorem derived78815 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3146) ∨ (p 2922) ∨ (¬ p 4133) ∨ (¬ p 2220) ∨ (p 2363) ∨ (¬ p 4521) ∨ (p 2911) :=
  ElevenRUP.step78815 (p 2220) (p 2363) (p 2911) (p 2922) (p 2928) (p 3146) (p 3379) (p 3452) (p 3644) (p 4133) (p 4347) (p 4521) (derived73394 p h) (derived73320 p h) (derived73560 p h) (derived73434 p h) (derived42437 p h)

theorem derived78818 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2417) ∨ (¬ p 4669) ∨ (¬ p 3156) ∨ (p 2598) ∨ (¬ p 4786) ∨ (p 3201) ∨ (¬ p 3146) :=
  ElevenRUP.step78818 (p 2417) (p 2598) (p 2946) (p 3055) (p 3146) (p 3156) (p 3201) (p 3876) (p 4278) (p 4669) (p 4786) (derived73546 p h) (derived73350 p h) (derived73486 p h) (derived41187 p h)

theorem derived78822 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3201) ∨ (¬ p 2958) ∨ (¬ p 2190) ∨ (¬ p 4786) ∨ (p 2598) ∨ (¬ p 2156) ∨ (p 2911) ∨ (¬ p 3146) ∨ (¬ p 4133) :=
  ElevenRUP.step78822 (p 2156) (p 2190) (p 2363) (p 2598) (p 2911) (p 2958) (p 3055) (p 3146) (p 3201) (p 3644) (p 3876) (p 4133) (p 4347) (p 4786) (derived73560 p h) (derived73486 p h) (derived73350 p h) (derived73434 p h) (derived42350 p h)

theorem derived78823 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 3201) ∨ (¬ p 2166) ∨ (¬ p 3146) ∨ (¬ p 4669) ∨ (¬ p 4736) ∨ (¬ p 2210) ∨ (p 2598) :=
  ElevenRUP.step78823 (p 2166) (p 2210) (p 2417) (p 2598) (p 3055) (p 3146) (p 3201) (p 3876) (p 4278) (p 4669) (p 4736) (derived73546 p h) (derived73486 p h) (derived73350 p h) (derived52145 p h)

theorem derived78829 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 2727) ∨ (¬ p 2946) ∨ (¬ p 3412) ∨ (p 3389) ∨ (¬ p 2255) ∨ (¬ p 2166) ∨ (¬ p 4669) ∨ (¬ p 3146) ∨ (¬ p 2662) :=
  ElevenRUP.step78829 (p 2166) (p 2255) (p 2417) (p 2662) (p 2727) (p 2946) (p 3146) (p 3389) (p 3412) (p 3540) (p 4111) (p 4278) (p 4669) (derived73546 p h) (derived73518 p h) (derived73402 p h) (derived48523 p h)

theorem derived78830 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2655) ∨ (¬ p 3361) ∨ (¬ p 4418) ∨ (¬ p 3146) ∨ (p 3389) ∨ (p 2737) ∨ (¬ p 2166) ∨ (¬ p 2132) ∨ (¬ p 4669) :=
  ElevenRUP.step78830 (p 2132) (p 2166) (p 2417) (p 2655) (p 2737) (p 2743) (p 3146) (p 3361) (p 3389) (p 3540) (p 4278) (p 4418) (p 4669) (derived73546 p h) (derived73402 p h) (derived73298 p h) (derived71402 p h)

theorem derived78832 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2651) ∨ (¬ p 3146) ∨ (¬ p 2156) ∨ (¬ p 2190) ∨ (p 2363) ∨ (¬ p 2144) ∨ (¬ p 4789) ∨ (¬ p 4133) ∨ (p 2911) :=
  ElevenRUP.step78832 (p 2144) (p 2156) (p 2190) (p 2363) (p 2437) (p 2651) (p 2657) (p 2911) (p 3146) (p 3644) (p 3742) (p 4133) (p 4347) (p 4789) (derived73452 p h) (derived73288 p h) (derived73560 p h) (derived73434 p h) (derived48187 p h)

theorem derived78834 (p : Nat → Prop) (h : Inputs p) :
    (p 2088) ∨ (p 3005) ∨ (¬ p 3146) ∨ (¬ p 2797) ∨ (¬ p 3177) :=
  ElevenRUP.step78834 (p 2088) (p 2797) (p 3005) (p 3146) (p 3177) (p 3857) (p 3877) (derived73480 p h) (derived73488 p h) (derived45973 p h)

theorem derived78846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 3093) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 2946) ∨ (¬ p 5118) ∨ (¬ p 3923) ∨ (¬ p 2248) :=
  ElevenRUP.step78846 (p 2248) (p 2946) (p 3093) (p 3146) (p 3156) (p 3591) (p 3923) (p 5118) (p 5580) (derived73432 p h) (derived56236 p h)

theorem derived78851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 3661) ∨ (¬ p 4558) ∨ (¬ p 2901) ∨ (¬ p 3146) ∨ (p 3256) :=
  ElevenRUP.step78851 (p 2190) (p 2901) (p 3146) (p 3256) (p 3661) (p 4118) (p 4558) (derived73520 p h) (derived54929 p h)

theorem derived78852 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 3146) ∨ (¬ p 4492) ∨ (¬ p 4558) ∨ (¬ p 3858) ∨ (p 2088) ∨ (¬ p 2891) :=
  ElevenRUP.step78852 (p 2088) (p 2190) (p 2891) (p 3146) (p 3857) (p 3858) (p 4492) (p 4558) (derived73480 p h) (derived49678 p h)

theorem derived78853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2363) ∨ (¬ p 4383) ∨ (¬ p 2156) ∨ (p 3083) ∨ (¬ p 3146) ∨ (p 3389) ∨ (¬ p 4133) ∨ (¬ p 2144) ∨ (¬ p 4729) ∨ (¬ p 2437) :=
  ElevenRUP.step78853 (p 2144) (p 2156) (p 2190) (p 2363) (p 2437) (p 3083) (p 3146) (p 3389) (p 3540) (p 4133) (p 4256) (p 4347) (p 4383) (p 4729) (derived73560 p h) (derived73542 p h) (derived73402 p h) (derived50981 p h)

theorem derived78855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 2619) ∨ (¬ p 4241) ∨ (¬ p 4885) ∨ (¬ p 3661) ∨ (p 3256) :=
  ElevenRUP.step78855 (p 2619) (p 3146) (p 3256) (p 3661) (p 4118) (p 4241) (p 4885) (derived73520 p h) (derived55098 p h)

theorem derived78857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2254) ∨ (¬ p 3661) ∨ (¬ p 2177) ∨ (p 2946) ∨ (¬ p 3146) ∨ (¬ p 3093) ∨ (¬ p 4905) ∨ (p 3256) :=
  ElevenRUP.step78857 (p 2177) (p 2254) (p 2946) (p 2952) (p 3093) (p 3146) (p 3256) (p 3309) (p 3661) (p 4118) (p 4905) (derived73330 p h) (derived73520 p h) (derived55479 p h)

theorem derived78858 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3661) ∨ (¬ p 4960) ∨ (¬ p 2166) ∨ (¬ p 3146) :=
  ElevenRUP.step78858 (p 2166) (p 3146) (p 3256) (p 3661) (p 4118) (p 4960) (derived73520 p h) (derived41513 p h)

theorem derived78861 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (p 2295) ∨ (¬ p 2166) ∨ (¬ p 2254) ∨ (¬ p 3146) ∨ (¬ p 2210) ∨ (p 2396) ∨ (¬ p 4669) :=
  ElevenRUP.step78861 (p 2166) (p 2210) (p 2254) (p 2295) (p 2331) (p 2396) (p 2963) (p 3146) (p 3568) (p 4107) (p 4669) (derived73338 p h) (derived73416 p h) (derived73514 p h) (derived51958 p h)

theorem derived78864 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3146) ∨ (¬ p 3905) ∨ (¬ p 4786) ∨ (¬ p 3156) ∨ (¬ p 2946) ∨ (¬ p 3461) ∨ (¬ p 4604) ∨ (¬ p 3346) :=
  ElevenRUP.step78864 (p 2946) (p 3146) (p 3156) (p 3276) (p 3346) (p 3461) (p 3905) (p 4425) (p 4604) (p 4786) (derived73578 p h) (derived52151 p h)

theorem derived78868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2901) ∨ (¬ p 3146) ∨ (p 2459) :=
  ElevenRUP.step78868 (p 2459) (p 2901) (p 3146) (p 3156) (p 4320) (p 4348) (derived73552 p h) (derived73562 p h) (derived61879 p h)

theorem derived78869 (p : Nat → Prop) (h : Inputs p) :
    (p 2901) ∨ (¬ p 3156) ∨ (¬ p 3146) ∨ (¬ p 3051) ∨ (¬ p 2958) :=
  ElevenRUP.step78869 (p 2901) (p 2958) (p 3051) (p 3146) (p 3156) (p 4320) (derived73552 p h) (derived45824 p h)

theorem derived78870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3146) ∨ (p 2230) ∨ (¬ p 2531) ∨ (p 2440) :=
  ElevenRUP.step78870 (p 2230) (p 2440) (p 2470) (p 2531) (p 2542) (p 2589) (p 3146) (derived73284 p h) (derived73270 p h) (derived47109 p h)

theorem derived78872 (p : Nat → Prop) (h : Inputs p) :
    (p 2532) ∨ (¬ p 3146) :=
  ElevenRUP.step78872 (p 2532) (p 3146) (p 5057) (derived73898 p h) (h 8477)

theorem derived78875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (p 5059) :=
  ElevenRUP.step78875 (p 3146) (p 5057) (p 5059) (derived73898 p h) (h 8481)

theorem derived78878 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (p 4608) :=
  ElevenRUP.step78878 (p 2373) (p 4606) (p 4608) (derived73664 p h) (h 7344)

theorem derived78879 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) ∨ (p 2373) :=
  ElevenRUP.step78879 (p 2373) (p 4158) (p 4606) (derived73664 p h) (h 7345)

theorem derived78880 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2509) ∨ (¬ p 2563) ∨ (¬ p 2493) :=
  ElevenRUP.step78880 (p 2373) (p 2493) (p 2509) (p 2563) (p 4606) (p 4716) (derived73664 p h) (derived73722 p h) (derived69484 p h)

theorem derived78881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3083) ∨ (p 2373) :=
  ElevenRUP.step78881 (p 2373) (p 3083) (p 3156) (p 3497) (p 4256) (p 4606) (derived73542 p h) (derived73664 p h) (derived73399 p h) (derived67220 p h)

theorem derived78882 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (p 3146) ∨ (¬ p 2563) ∨ (¬ p 2459) :=
  ElevenRUP.step78882 (p 2373) (p 2459) (p 2563) (p 3146) (p 3692) (p 3880) (derived73490 p h) (derived73448 p h) (derived43908 p h)

theorem derived78884 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2373) ∨ (¬ p 3904) ∨ (p 3146) ∨ (¬ p 2427) :=
  ElevenRUP.step78884 (p 2373) (p 2427) (p 3051) (p 3146) (p 3556) (p 3692) (p 3880) (p 3904) (derived73414 p h) (derived73490 p h) (derived73448 p h) (derived44779 p h)

theorem derived78885 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2373) ∨ (¬ p 2829) ∨ (¬ p 2819) ∨ (¬ p 2427) ∨ (¬ p 2608) ∨ (¬ p 4134) :=
  ElevenRUP.step78885 (p 2373) (p 2427) (p 2608) (p 2819) (p 2829) (p 3051) (p 3556) (p 3880) (p 4134) (p 4524) (derived73414 p h) (derived73490 p h) (derived72962 p h) (derived52243 p h)

theorem derived78889 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 3379) ∨ (¬ p 2363) ∨ (¬ p 4905) ∨ (¬ p 2641) ∨ (p 2373) ∨ (¬ p 2668) ∨ (p 2459) :=
  ElevenRUP.step78889 (p 2363) (p 2373) (p 2406) (p 2459) (p 2641) (p 2668) (p 3238) (p 3379) (p 3452) (p 3880) (p 4348) (p 4905) (derived73374 p h) (derived73394 p h) (derived73490 p h) (derived73562 p h) (derived54102 p h)

theorem derived78892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3747) ∨ (p 2373) ∨ (¬ p 2427) :=
  ElevenRUP.step78892 (p 2373) (p 2427) (p 3747) (p 3880) (derived73490 p h) (h 20076)

theorem derived78898 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 3146) ∨ (p 2406) ∨ (p 2373) :=
  ElevenRUP.step78898 (p 2373) (p 2406) (p 3146) (p 3238) (p 3379) (p 3452) (p 3692) (p 3880) (derived73394 p h) (derived73448 p h) (derived73374 p h) (derived73490 p h) (derived43534 p h)

theorem derived78899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3146) ∨ (¬ p 4330) ∨ (¬ p 2241) ∨ (¬ p 5193) ∨ (¬ p 2641) ∨ (p 2373) ∨ (p 2230) :=
  ElevenRUP.step78899 (p 2230) (p 2241) (p 2373) (p 2589) (p 2641) (p 3146) (p 3323) (p 3692) (p 3880) (p 4330) (p 5193) (derived73448 p h) (derived73490 p h) (derived73284 p h) (derived50275 p h)

theorem derived78901 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2373) ∨ (¬ p 4132) ∨ (¬ p 4668) ∨ (¬ p 2427) :=
  ElevenRUP.step78901 (p 2373) (p 2427) (p 3246) (p 3880) (p 4132) (p 4668) (derived73490 p h) (derived49775 p h)

theorem derived78903 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (p 3146) ∨ (¬ p 2563) ∨ (¬ p 2363) :=
  ElevenRUP.step78903 (p 2363) (p 2373) (p 2563) (p 3146) (p 3692) (p 3880) (derived73490 p h) (derived73448 p h) (derived43375 p h)

theorem derived78904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 4132) ∨ (¬ p 4556) ∨ (p 2373) ∨ (¬ p 2177) :=
  ElevenRUP.step78904 (p 2177) (p 2373) (p 2427) (p 3880) (p 4132) (p 4556) (derived73490 p h) (derived50154 p h)

theorem derived78905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2264) ∨ (¬ p 4132) ∨ (¬ p 4362) ∨ (p 2373) :=
  ElevenRUP.step78905 (p 2264) (p 2373) (p 2427) (p 3880) (p 4132) (p 4362) (derived73490 p h) (derived64694 p h)

theorem derived78906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2373) ∨ (¬ p 4132) ∨ (¬ p 2427) :=
  ElevenRUP.step78906 (p 2341) (p 2373) (p 2427) (p 3880) (p 4132) (derived73490 p h) (derived68265 p h)

theorem derived78908 (p : Nat → Prop) (h : Inputs p) :
    (p 2088) ∨ (¬ p 2532) ∨ (¬ p 4529) ∨ (¬ p 2982) ∨ (p 2373) :=
  ElevenRUP.step78908 (p 2088) (p 2373) (p 2532) (p 2982) (p 3857) (p 3880) (p 4529) (derived73480 p h) (derived73490 p h) (derived42146 p h)

theorem derived78909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 3073) ∨ (¬ p 2532) ∨ (p 2373) ∨ (¬ p 4494) :=
  ElevenRUP.step78909 (p 2373) (p 2532) (p 2982) (p 3073) (p 3880) (p 4261) (p 4494) (derived73544 p h) (derived73490 p h) (derived63955 p h)

theorem derived78911 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2373) ∨ (¬ p 2459) ∨ (p 2230) :=
  ElevenRUP.step78911 (p 2230) (p 2373) (p 2459) (p 2589) (p 3146) (p 3692) (p 3880) (derived73448 p h) (derived73490 p h) (derived73284 p h) (derived44763 p h)

theorem derived78912 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2373) ∨ (¬ p 2563) :=
  ElevenRUP.step78912 (p 2190) (p 2373) (p 2563) (p 3880) (p 4110) (derived73490 p h) (derived73515 p h) (h 6279)

theorem derived78920 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2145) ∨ (p 2685) ∨ (p 2156) ∨ (¬ p 2807) ∨ (¬ p 3005) ∨ (¬ p 2563) ∨ (¬ p 4117) ∨ (¬ p 5063) :=
  ElevenRUP.step78920 (p 2145) (p 2156) (p 2373) (p 2563) (p 2685) (p 2807) (p 3005) (p 3572) (p 3646) (p 3880) (p 4117) (p 5063) (derived73490 p h) (derived73420 p h) (derived73436 p h) (derived55295 p h)

theorem derived78921 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 3309) ∨ (¬ p 4506) ∨ (¬ p 3743) ∨ (¬ p 3204) ∨ (¬ p 2563) :=
  ElevenRUP.step78921 (p 2373) (p 2563) (p 3204) (p 3309) (p 3743) (p 3880) (p 4506) (derived73490 p h) (derived71403 p h)

theorem derived78922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4237) ∨ (p 2373) ∨ (¬ p 4705) ∨ (p 3146) :=
  ElevenRUP.step78922 (p 2373) (p 3146) (p 3256) (p 3692) (p 3880) (p 4237) (p 4705) (derived73490 p h) (derived73448 p h) (derived41999 p h)

theorem derived78923 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3413) ∨ (p 2406) ∨ (p 2373) ∨ (¬ p 4811) :=
  ElevenRUP.step78923 (p 2373) (p 2406) (p 3156) (p 3238) (p 3413) (p 3880) (p 4811) (derived73374 p h) (derived73490 p h) (derived48791 p h)

theorem derived78925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3879) ∨ (¬ p 3156) ∨ (p 2373) :=
  ElevenRUP.step78925 (p 2373) (p 3156) (p 3879) (p 3880) (derived73490 p h) (h 5740)

theorem derived78927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5590) ∨ (¬ p 3979) ∨ (¬ p 3325) ∨ (¬ p 4115) ∨ (¬ p 2563) ∨ (p 2373) :=
  ElevenRUP.step78927 (p 2373) (p 2563) (p 3325) (p 3880) (p 3979) (p 4115) (p 5590) (derived73490 p h) (derived46694 p h)

theorem derived78930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 4399) ∨ (p 2406) ∨ (p 2373) ∨ (¬ p 5194) :=
  ElevenRUP.step78930 (p 2220) (p 2373) (p 2406) (p 3238) (p 3880) (p 4399) (p 5194) (derived73374 p h) (derived73490 p h) (derived49536 p h)

theorem derived78931 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 4399) ∨ (¬ p 4236) ∨ (¬ p 3366) ∨ (¬ p 2563) ∨ (¬ p 2220) ∨ (¬ p 4391) ∨ (¬ p 3519) ∨ (¬ p 4067) ∨ (p 2396) ∨ (p 2373) ∨ (¬ p 4376) ∨ (p 2331) :=
  ElevenRUP.step78931 (p 2220) (p 2331) (p 2373) (p 2396) (p 2563) (p 2963) (p 3366) (p 3519) (p 3791) (p 3880) (p 4067) (p 4107) (p 4236) (p 4376) (p 4391) (p 4399) (derived73514 p h) (derived73490 p h) (derived73338 p h) (derived47187 p h)

theorem derived78932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3755) ∨ (p 3830) ∨ (¬ p 4399) ∨ (¬ p 3847) ∨ (¬ p 3519) ∨ (¬ p 2427) ∨ (¬ p 2220) ∨ (p 2373) ∨ (p 3005) ∨ (¬ p 4376) ∨ (¬ p 2608) :=
  ElevenRUP.step78932 (p 2220) (p 2373) (p 2427) (p 2608) (p 3005) (p 3519) (p 3755) (p 3830) (p 3834) (p 3847) (p 3877) (p 3880) (p 4376) (p 4399) (derived73474 p h) (derived73490 p h) (derived73488 p h) (derived47184 p h)

theorem derived78933 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 2373) ∨ (p 2230) :=
  ElevenRUP.step78933 (p 2230) (p 2373) (p 2573) (p 2589) (p 3880) (derived73490 p h) (derived73284 p h) (derived67013 p h)

theorem derived78936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 2440) ∨ (¬ p 4203) ∨ (p 2373) :=
  ElevenRUP.step78936 (p 2373) (p 2440) (p 3016) (p 3880) (p 4203) (derived73490 p h) (derived69486 p h)

theorem derived78937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2750) ∨ (p 2651) ∨ (p 2608) ∨ (¬ p 3527) ∨ (¬ p 2440) ∨ (¬ p 4905) ∨ (¬ p 3399) ∨ (¬ p 2252) ∨ (p 2373) :=
  ElevenRUP.step78937 (p 2252) (p 2373) (p 2440) (p 2608) (p 2651) (p 2657) (p 2750) (p 3399) (p 3527) (p 3880) (p 3954) (p 4905) (derived73288 p h) (derived73498 p h) (derived73490 p h) (derived41579 p h)

theorem derived78942 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 3146) ∨ (p 2373) ∨ (p 2850) :=
  ElevenRUP.step78942 (p 2373) (p 2850) (p 3146) (p 3266) (p 3684) (p 3692) (p 3880) (p 4444) (derived73580 p h) (derived73448 p h) (derived73490 p h) (derived73442 p h) (derived46051 p h)

theorem derived78943 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2264) ∨ (p 2373) ∨ (¬ p 2241) ∨ (p 2996) ∨ (¬ p 5193) ∨ (p 2230) ∨ (p 3146) :=
  ElevenRUP.step78943 (p 2230) (p 2241) (p 2264) (p 2373) (p 2589) (p 2996) (p 3027) (p 3146) (p 3266) (p 3692) (p 3880) (p 4444) (p 5193) (derived73580 p h) (derived73490 p h) (derived73340 p h) (derived73284 p h) (derived73448 p h) (derived50421 p h)

theorem derived78944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 2598) ∨ (¬ p 2166) ∨ (p 2373) ∨ (¬ p 3366) ∨ (¬ p 2563) :=
  ElevenRUP.step78944 (p 2166) (p 2373) (p 2563) (p 2598) (p 3055) (p 3366) (p 3371) (p 3880) (derived73350 p h) (derived73490 p h) (derived47257 p h)

theorem derived78945 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 3146) ∨ (¬ p 3379) ∨ (p 2373) ∨ (¬ p 4034) :=
  ElevenRUP.step78945 (p 2210) (p 2373) (p 3146) (p 3379) (p 3555) (p 3692) (p 3880) (p 4034) (derived73412 p h) (derived73448 p h) (derived73490 p h) (derived47709 p h)

theorem derived78950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 3115) ∨ (p 2373) ∨ (p 3136) :=
  ElevenRUP.step78950 (p 2373) (p 2982) (p 3115) (p 3136) (p 3880) (p 4208) (p 4315) (derived73534 p h) (derived73490 p h) (derived73550 p h) (derived60139 p h)

theorem derived78951 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 4335) ∨ (p 2373) :=
  ElevenRUP.step78951 (p 2373) (p 2982) (p 3880) (p 4335) (derived73490 p h) (h 38570)

theorem derived78955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 4399) ∨ (p 2373) ∨ (p 2573) ∨ (¬ p 2493) :=
  ElevenRUP.step78955 (p 2220) (p 2373) (p 2493) (p 2573) (p 2579) (p 3880) (p 4399) (derived73490 p h) (derived73274 p h) (derived45458 p h)

theorem derived78956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 4399) ∨ (¬ p 4715) ∨ (p 2373) ∨ (p 2573) :=
  ElevenRUP.step78956 (p 2220) (p 2373) (p 2573) (p 2579) (p 3880) (p 4399) (p 4715) (derived73490 p h) (derived73274 p h) (derived53239 p h)

theorem derived78957 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2651) ∨ (p 2373) ∨ (¬ p 2440) :=
  ElevenRUP.step78957 (p 2373) (p 2440) (p 2651) (p 2657) (p 3146) (p 3692) (p 3880) (derived73448 p h) (derived73288 p h) (derived73490 p h) (derived46838 p h)

theorem derived78960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2373) ∨ (¬ p 4558) ∨ (¬ p 2427) ∨ (p 2156) :=
  ElevenRUP.step78960 (p 2156) (p 2220) (p 2373) (p 2427) (p 3646) (p 3880) (p 4558) (derived73490 p h) (derived73436 p h) (derived52131 p h)

theorem derived78963 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2727) ∨ (¬ p 2662) ∨ (p 2230) ∨ (p 2373) :=
  ElevenRUP.step78963 (p 2230) (p 2373) (p 2589) (p 2662) (p 2727) (p 3146) (p 3692) (p 3880) (p 4111) (derived73448 p h) (derived73518 p h) (derived73284 p h) (derived73490 p h) (derived55718 p h)

theorem derived78965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (p 3146) ∨ (p 2230) ∨ (p 2630) ∨ (p 2373) :=
  ElevenRUP.step78965 (p 2230) (p 2373) (p 2589) (p 2630) (p 2662) (p 2810) (p 3146) (p 3692) (p 3880) (derived73448 p h) (derived73284 p h) (derived73316 p h) (derived73490 p h) (derived45982 p h)

theorem derived78967 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3950) ∨ (¬ p 2449) ∨ (¬ p 5193) ∨ (p 2230) ∨ (¬ p 2241) ∨ (p 2996) ∨ (p 2373) :=
  ElevenRUP.step78967 (p 2230) (p 2241) (p 2373) (p 2449) (p 2589) (p 2996) (p 3027) (p 3146) (p 3692) (p 3880) (p 3950) (p 5193) (derived73448 p h) (derived73284 p h) (derived73340 p h) (derived73490 p h) (derived51411 p h)

theorem derived78970 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3073) ∨ (¬ p 4632) ∨ (p 2373) ∨ (¬ p 4496) :=
  ElevenRUP.step78970 (p 2373) (p 3073) (p 3146) (p 3692) (p 3880) (p 4496) (p 4632) (derived73448 p h) (derived73490 p h) (derived48376 p h)

theorem derived78972 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 3146) ∨ (p 2373) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3950) ∨ (¬ p 3347) ∨ (p 2230) :=
  ElevenRUP.step78972 (p 2230) (p 2373) (p 2589) (p 2608) (p 3146) (p 3347) (p 3399) (p 3631) (p 3692) (p 3880) (p 3950) (p 3954) (derived73498 p h) (derived73448 p h) (derived73490 p h) (derived73284 p h) (derived71404 p h)

theorem derived78976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3156) ∨ (p 2373) ∨ (¬ p 2946) :=
  ElevenRUP.step78976 (p 2373) (p 2440) (p 2946) (p 3156) (p 3880) (derived73490 p h) (derived54568 p h)

theorem derived78977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2946) ∨ (p 2651) ∨ (p 2373) :=
  ElevenRUP.step78977 (p 2373) (p 2651) (p 2657) (p 2946) (p 3156) (p 3880) (derived73288 p h) (derived73490 p h) (derived45241 p h)

theorem derived78980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2373) ∨ (p 2192) ∨ (¬ p 2427) ∨ (¬ p 4558) :=
  ElevenRUP.step78980 (p 2166) (p 2192) (p 2373) (p 2427) (p 3880) (p 4173) (p 4558) (derived73490 p h) (derived73528 p h) (derived56966 p h)

theorem derived78986 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 2982) ∨ (¬ p 5063) ∨ (p 2373) ∨ (¬ p 2532) :=
  ElevenRUP.step78986 (p 2373) (p 2532) (p 2982) (p 3256) (p 3880) (p 4118) (p 5063) (derived73520 p h) (derived73490 p h) (derived49767 p h)

theorem derived78988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (p 2651) ∨ (¬ p 5063) ∨ (p 2373) ∨ (¬ p 3487) ∨ (p 2406) :=
  ElevenRUP.step78988 (p 2373) (p 2406) (p 2651) (p 2657) (p 3166) (p 3238) (p 3487) (p 3880) (p 5063) (derived73288 p h) (derived73490 p h) (derived73374 p h) (derived60111 p h)

theorem derived78989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 5118) ∨ (p 2373) ∨ (¬ p 2532) ∨ (¬ p 2982) :=
  ElevenRUP.step78989 (p 2373) (p 2532) (p 2982) (p 3880) (p 5118) (p 5568) (derived73490 p h) (derived56967 p h)

theorem derived78991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 3115) ∨ (p 2373) ∨ (¬ p 3156) :=
  ElevenRUP.step78991 (p 2373) (p 3115) (p 3156) (p 3880) (p 4208) (p 4322) (derived73534 p h) (derived73490 p h) (derived59234 p h)

theorem derived78994 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3413) ∨ (¬ p 4715) ∨ (p 2373) ∨ (p 3016) :=
  ElevenRUP.step78994 (p 2373) (p 3016) (p 3156) (p 3413) (p 3574) (p 3880) (p 4715) (derived73490 p h) (derived73422 p h) (derived62561 p h)

theorem derived78996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3660) ∨ (p 2264) ∨ (¬ p 2553) ∨ (¬ p 2220) ∨ (p 2373) ∨ (p 2274) ∨ (p 2685) ∨ (¬ p 2139) ∨ (p 2696) :=
  ElevenRUP.step78996 (p 2139) (p 2220) (p 2264) (p 2274) (p 2373) (p 2553) (p 2685) (p 2696) (p 3097) (p 3365) (p 3553) (p 3572) (p 3660) (p 3880) (derived73410 p h) (derived73490 p h) (derived73352 p h) (derived73420 p h) (derived73390 p h) (derived55921 p h)

theorem derived78997 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2982) ∨ (¬ p 2139) ∨ (¬ p 2220) ∨ (p 2696) ∨ (p 2373) ∨ (p 2685) ∨ (¬ p 4395) :=
  ElevenRUP.step78997 (p 2139) (p 2220) (p 2373) (p 2449) (p 2685) (p 2696) (p 2982) (p 3365) (p 3572) (p 3880) (p 3947) (p 4395) (derived73494 p h) (derived73390 p h) (derived73490 p h) (derived73420 p h) (derived55248 p h)

theorem derived78998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2668) ∨ (¬ p 2363) ∨ (p 2850) ∨ (p 2373) ∨ (¬ p 2331) ∨ (p 2598) ∨ (¬ p 4786) :=
  ElevenRUP.step78998 (p 2331) (p 2363) (p 2373) (p 2598) (p 2668) (p 2850) (p 3055) (p 3684) (p 3880) (p 4786) (p 5568) (derived73442 p h) (derived73490 p h) (derived73350 p h) (derived47022 p h)

theorem derived78999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 3146) ∨ (¬ p 3366) ∨ (p 2230) ∨ (¬ p 3905) ∨ (p 2373) ∨ (p 2241) ∨ (¬ p 3950) ∨ (¬ p 3631) ∨ (¬ p 2744) :=
  ElevenRUP.step78999 (p 2230) (p 2241) (p 2247) (p 2373) (p 2589) (p 2744) (p 3146) (p 3366) (p 3399) (p 3631) (p 3692) (p 3880) (p 3905) (p 3950) (derived73448 p h) (derived73284 p h) (derived73490 p h) (derived73226 p h) (derived56823 p h)

theorem derived79001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4040) ∨ (¬ p 3136) ∨ (p 3755) ∨ (¬ p 2982) ∨ (p 2373) :=
  ElevenRUP.step79001 (p 2373) (p 2982) (p 3136) (p 3755) (p 3880) (p 4035) (p 4040) (derived73506 p h) (derived73490 p h) (derived46460 p h)

theorem derived79003 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 3156) ∨ (¬ p 2992) ∨ (¬ p 2563) :=
  ElevenRUP.step79003 (p 2373) (p 2563) (p 2992) (p 3156) (p 3880) (derived73490 p h) (derived45048 p h)

theorem derived79004 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2220) ∨ (p 2373) ∨ (p 2274) :=
  ElevenRUP.step79004 (p 2156) (p 2220) (p 2274) (p 2373) (p 3097) (p 3646) (p 3880) (derived73436 p h) (derived73490 p h) (derived73352 p h) (derived45266 p h)

theorem derived79005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2274) ∨ (p 2373) ∨ (¬ p 3660) ∨ (¬ p 2166) :=
  ElevenRUP.step79005 (p 2166) (p 2274) (p 2373) (p 2553) (p 3097) (p 3660) (p 3880) (derived73352 p h) (derived73490 p h) (derived47259 p h)

theorem derived79006 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2166) ∨ (¬ p 3379) ∨ (¬ p 3948) ∨ (¬ p 2563) :=
  ElevenRUP.step79006 (p 2166) (p 2373) (p 2563) (p 3379) (p 3880) (p 3948) (derived73490 p h) (derived43174 p h)

theorem derived79007 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2459) ∨ (p 2373) ∨ (¬ p 2098) ∨ (¬ p 2563) ∨ (p 2156) ∨ (¬ p 2145) ∨ (¬ p 4905) :=
  ElevenRUP.step79007 (p 2098) (p 2145) (p 2156) (p 2373) (p 2459) (p 2563) (p 3609) (p 3646) (p 3880) (p 4348) (p 4905) (derived73562 p h) (derived73490 p h) (derived73436 p h) (derived62744 p h)

theorem derived79008 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2192) ∨ (¬ p 2563) ∨ (¬ p 4506) ∨ (p 2373) :=
  ElevenRUP.step79008 (p 2192) (p 2363) (p 2373) (p 2563) (p 3880) (p 4173) (p 4347) (p 4506) (derived73560 p h) (derived73528 p h) (derived73490 p h) (derived48308 p h)

theorem derived79011 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2668) ∨ (p 2295) ∨ (¬ p 2563) ∨ (¬ p 4506) :=
  ElevenRUP.step79011 (p 2295) (p 2373) (p 2563) (p 2668) (p 3568) (p 3880) (p 4506) (derived73490 p h) (derived73416 p h) (derived48803 p h)

theorem derived79012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2373) ∨ (¬ p 4506) ∨ (¬ p 4603) ∨ (¬ p 2563) :=
  ElevenRUP.step79012 (p 2373) (p 2563) (p 3125) (p 3880) (p 4506) (p 4603) (derived73490 p h) (derived56404 p h)

theorem derived79014 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2383) ∨ (¬ p 2563) ∨ (¬ p 4489) ∨ (¬ p 4506) :=
  ElevenRUP.step79014 (p 2373) (p 2383) (p 2563) (p 3880) (p 4489) (p 4506) (derived73490 p h) (derived49218 p h)

theorem derived79015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (p 2373) ∨ (¬ p 3093) ∨ (p 2230) ∨ (¬ p 3905) ∨ (p 3146) ∨ (¬ p 3950) ∨ (¬ p 4736) :=
  ElevenRUP.step79015 (p 2230) (p 2373) (p 2396) (p 2589) (p 3093) (p 3146) (p 3309) (p 3692) (p 3880) (p 3905) (p 3950) (p 4736) (derived73490 p h) (derived73284 p h) (derived73448 p h) (derived55813 p h)

theorem derived79017 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2220) ∨ (¬ p 2274) ∨ (¬ p 2563) :=
  ElevenRUP.step79017 (p 2220) (p 2274) (p 2373) (p 2563) (p 3880) (derived73490 p h) (derived53925 p h)

theorem derived79019 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 4446) ∨ (¬ p 4993) ∨ (¬ p 2668) ∨ (¬ p 2563) :=
  ElevenRUP.step79019 (p 2373) (p 2563) (p 2668) (p 3880) (p 4446) (p 4560) (p 4993) (derived73490 p h) (derived72955 p h) (derived51218 p h)

theorem derived79023 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3146) ∨ (¬ p 2284) ∨ (¬ p 2528) :=
  ElevenRUP.step79023 (p 2284) (p 2528) (p 3146) (p 3156) (p 3497) (p 3692) (derived73400 p h) (derived73448 p h) (derived44220 p h)

theorem derived79024 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3156) ∨ (¬ p 2284) ∨ (¬ p 2363) :=
  ElevenRUP.step79024 (p 2284) (p 2363) (p 3146) (p 3156) (p 3497) (p 3692) (derived73448 p h) (derived73400 p h) (derived45906 p h)

theorem derived79025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 3156) ∨ (¬ p 2284) :=
  ElevenRUP.step79025 (p 2190) (p 2284) (p 3156) (p 3497) (derived73400 p h) (h 5078)

theorem derived79026 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2220) ∨ (¬ p 2284) ∨ (p 3051) :=
  ElevenRUP.step79026 (p 2220) (p 2284) (p 3051) (p 3156) (p 3497) (p 3556) (derived73400 p h) (derived73414 p h) (derived44601 p h)

theorem derived79027 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2220) ∨ (p 3051) ∨ (¬ p 4555) ∨ (¬ p 2284) :=
  ElevenRUP.step79027 (p 2220) (p 2284) (p 3051) (p 3156) (p 3497) (p 3556) (p 4555) (derived73400 p h) (derived73414 p h) (derived48082 p h)

theorem derived79029 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 3156) ∨ (¬ p 2373) ∨ (¬ p 2651) :=
  ElevenRUP.step79029 (p 2373) (p 2651) (p 2946) (p 2952) (p 3156) (p 3497) (derived73330 p h) (derived73400 p h) (derived44202 p h)

theorem derived79030 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3156) ∨ (¬ p 3361) ∨ (p 2946) ∨ (p 2737) :=
  ElevenRUP.step79030 (p 2737) (p 2743) (p 2946) (p 2952) (p 3146) (p 3156) (p 3361) (p 3497) (p 3692) (derived73448 p h) (derived73400 p h) (derived73330 p h) (derived73298 p h) (derived46821 p h)

theorem derived79032 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2946) ∨ (¬ p 2331) ∨ (¬ p 2220) :=
  ElevenRUP.step79032 (p 2220) (p 2331) (p 2946) (p 2952) (p 3156) (p 3497) (derived73400 p h) (derived73330 p h) (derived57578 p h)

theorem derived79033 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2274) ∨ (¬ p 2284) ∨ (¬ p 4506) :=
  ElevenRUP.step79033 (p 2274) (p 2284) (p 3156) (p 3497) (p 4506) (derived73400 p h) (derived71406 p h)

theorem derived79034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3146) ∨ (¬ p 2459) ∨ (p 3156) :=
  ElevenRUP.step79034 (p 2459) (p 2901) (p 3146) (p 3156) (p 3497) (p 3692) (derived73448 p h) (derived73400 p h) (derived46088 p h)

theorem derived79035 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3146) ∨ (p 3051) ∨ (p 3156) :=
  ElevenRUP.step79035 (p 2901) (p 3051) (p 3146) (p 3156) (p 3497) (p 3556) (p 3692) (derived73448 p h) (derived73414 p h) (derived73400 p h) (derived47945 p h)

theorem derived79036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3370) ∨ (¬ p 4632) ∨ (p 2427) ∨ (¬ p 2220) ∨ (p 3156) :=
  ElevenRUP.step79036 (p 2220) (p 2427) (p 2901) (p 3156) (p 3370) (p 3497) (p 4235) (p 4632) (derived73536 p h) (derived73400 p h) (derived56444 p h)

theorem derived79037 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3146) ∨ (p 3156) ∨ (p 2870) :=
  ElevenRUP.step79037 (p 2870) (p 2901) (p 3146) (p 3156) (p 3497) (p 3692) (p 4244) (derived73448 p h) (derived73400 p h) (derived73540 p h) (derived59450 p h)

theorem derived79038 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2210) ∨ (¬ p 2284) ∨ (p 2192) :=
  ElevenRUP.step79038 (p 2192) (p 2210) (p 2284) (p 3156) (p 3497) (p 3555) (p 4173) (derived73400 p h) (derived73412 p h) (derived73528 p h) (derived46244 p h)

theorem derived79039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 3156) ∨ (¬ p 2373) ∨ (¬ p 2230) :=
  ElevenRUP.step79039 (p 2230) (p 2284) (p 2373) (p 3156) (p 3497) (derived73400 p h) (derived44915 p h)

theorem derived79040 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 3156) ∨ (¬ p 2373) ∨ (p 2563) :=
  ElevenRUP.step79040 (p 2373) (p 2563) (p 2946) (p 2952) (p 3156) (p 3497) (p 4110) (derived73330 p h) (derived73400 p h) (derived73516 p h) (derived46840 p h)

theorem derived79045 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 5564) ∨ (p 3156) ∨ (¬ p 2901) ∨ (¬ p 4132) :=
  ElevenRUP.step79045 (p 2901) (p 3156) (p 3497) (p 4129) (p 4132) (p 5564) (derived73400 p h) (derived42637 p h)

theorem derived79051 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 3156) ∨ (¬ p 2901) ∨ (¬ p 2156) :=
  ElevenRUP.step79051 (p 2156) (p 2901) (p 3051) (p 3156) (p 3497) (p 3556) (derived73414 p h) (derived73400 p h) (derived43030 p h)

theorem derived79053 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3246) ∨ (¬ p 2901) ∨ (p 3156) :=
  ElevenRUP.step79053 (p 2417) (p 2901) (p 3156) (p 3246) (p 3497) (p 4278) (derived73546 p h) (derived73400 p h) (derived58968 p h)

theorem derived79054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3156) ∨ (¬ p 2166) ∨ (¬ p 2210) :=
  ElevenRUP.step79054 (p 2166) (p 2210) (p 2901) (p 3156) (p 3497) (derived73400 p h) (derived64038 p h)

theorem derived79055 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2241) ∨ (¬ p 4365) ∨ (¬ p 2166) ∨ (¬ p 2284) :=
  ElevenRUP.step79055 (p 2166) (p 2241) (p 2284) (p 3156) (p 3497) (p 4365) (derived73400 p h) (derived55280 p h)

theorem derived79056 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2210) ∨ (¬ p 2166) ∨ (¬ p 2284) :=
  ElevenRUP.step79056 (p 2166) (p 2210) (p 2284) (p 3156) (p 3497) (derived73400 p h) (derived45846 p h)

theorem derived79062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (p 3156) ∨ (¬ p 3986) ∨ (p 2946) :=
  ElevenRUP.step79062 (p 2331) (p 2946) (p 2952) (p 3156) (p 3497) (p 3986) (derived73400 p h) (derived73330 p h) (derived69487 p h)

theorem derived79064 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2619) ∨ (p 3156) ∨ (p 2946) :=
  ElevenRUP.step79064 (p 2619) (p 2860) (p 2946) (p 2952) (p 3156) (p 3497) (p 3758) (derived73456 p h) (derived73400 p h) (derived73330 p h) (derived42885 p h)

theorem derived79065 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3146) ∨ (p 2860) ∨ (¬ p 2284) :=
  ElevenRUP.step79065 (p 2284) (p 2860) (p 3146) (p 3156) (p 3497) (p 3692) (p 3758) (derived73400 p h) (derived73448 p h) (derived73456 p h) (derived58134 p h)

theorem derived79067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3156) ∨ (¬ p 3379) ∨ (p 3051) ∨ (¬ p 2352) ∨ (¬ p 4134) ∨ (¬ p 2493) :=
  ElevenRUP.step79067 (p 2352) (p 2493) (p 2901) (p 3051) (p 3156) (p 3379) (p 3497) (p 3556) (p 4134) (p 4524) (derived73400 p h) (derived72962 p h) (derived73414 p h) (derived52085 p h)

theorem derived79069 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2241) ∨ (¬ p 4446) ∨ (¬ p 2284) ∨ (¬ p 3449) :=
  ElevenRUP.step79069 (p 2241) (p 2247) (p 2284) (p 3156) (p 3449) (p 3497) (p 4446) (derived73400 p h) (derived73226 p h) (derived46589 p h)

theorem derived79072 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2274) ∨ (¬ p 2220) ∨ (¬ p 4198) ∨ (p 2307) :=
  ElevenRUP.step79072 (p 2220) (p 2274) (p 2307) (p 2313) (p 3156) (p 3497) (p 4198) (derived73400 p h) (derived73238 p h) (derived48471 p h)

theorem derived79073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2284) ∨ (p 3156) ∨ (¬ p 4718) ∨ (¬ p 4506) :=
  ElevenRUP.step79073 (p 2284) (p 2352) (p 3156) (p 3497) (p 4506) (p 4718) (derived73400 p h) (derived60936 p h)

theorem derived79076 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2946) ∨ (¬ p 2363) ∨ (p 3156) :=
  ElevenRUP.step79076 (p 2363) (p 2946) (p 2952) (p 3146) (p 3156) (p 3497) (p 3692) (derived73448 p h) (derived73330 p h) (derived73400 p h) (derived56680 p h)

theorem derived79079 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3156) ∨ (¬ p 2459) ∨ (p 3136) :=
  ElevenRUP.step79079 (p 2459) (p 3136) (p 3146) (p 3156) (p 3497) (p 3692) (p 4315) (derived73448 p h) (derived73400 p h) (derived73550 p h) (derived44799 p h)

theorem derived79080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2341) ∨ (¬ p 4647) ∨ (¬ p 3575) ∨ (¬ p 4132) ∨ (p 3156) :=
  ElevenRUP.step79080 (p 2341) (p 2901) (p 3156) (p 3497) (p 3575) (p 4132) (p 4647) (derived73400 p h) (derived49371 p h)

theorem derived79086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2307) ∨ (¬ p 4185) ∨ (¬ p 4336) ∨ (¬ p 2785) ∨ (p 3156) :=
  ElevenRUP.step79086 (p 2295) (p 2307) (p 2313) (p 2785) (p 3156) (p 3497) (p 4185) (p 4336) (derived73238 p h) (derived73400 p h) (derived69489 p h)

theorem derived79087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 2528) ∨ (¬ p 4158) ∨ (p 3156) ∨ (¬ p 2532) :=
  ElevenRUP.step79087 (p 2528) (p 2532) (p 2534) (p 3115) (p 3156) (p 3497) (p 4158) (derived73268 p h) (derived73400 p h) (derived55170 p h)

theorem derived79089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 4132) ∨ (¬ p 4556) ∨ (p 3156) ∨ (¬ p 2177) :=
  ElevenRUP.step79089 (p 2177) (p 2901) (p 3156) (p 3497) (p 4132) (p 4556) (derived73400 p h) (derived50152 p h)

theorem derived79090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3156) ∨ (¬ p 2284) ∨ (¬ p 4489) ∨ (¬ p 4506) :=
  ElevenRUP.step79090 (p 2284) (p 2383) (p 3156) (p 3497) (p 4489) (p 4506) (derived73400 p h) (derived50482 p h)

theorem derived79092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5586) ∨ (p 3156) ∨ (¬ p 4506) ∨ (¬ p 3737) ∨ (¬ p 2284) :=
  ElevenRUP.step79092 (p 2284) (p 3156) (p 3497) (p 3737) (p 4506) (p 5586) (derived73400 p h) (derived42210 p h)

theorem derived79098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4503) ∨ (¬ p 2950) ∨ (p 2156) ∨ (¬ p 2922) ∨ (¬ p 4506) ∨ (¬ p 2911) ∨ (¬ p 3379) ∨ (¬ p 2284) ∨ (¬ p 2254) ∨ (p 3156) :=
  ElevenRUP.step79098 (p 2156) (p 2254) (p 2284) (p 2911) (p 2922) (p 2950) (p 3156) (p 3379) (p 3497) (p 3646) (p 4503) (p 4506) (derived73436 p h) (derived73400 p h) (derived62373 p h)

theorem derived79099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 3146) ∨ (¬ p 3950) ∨ (¬ p 3093) ∨ (p 2946) ∨ (p 3156) ∨ (¬ p 2254) ∨ (¬ p 2396) :=
  ElevenRUP.step79099 (p 2254) (p 2396) (p 2946) (p 2952) (p 3093) (p 3146) (p 3156) (p 3309) (p 3497) (p 3692) (p 3950) (derived73448 p h) (derived73330 p h) (derived73400 p h) (derived49063 p h)

theorem derived79104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2901) ∨ (¬ p 4647) ∨ (¬ p 4132) ∨ (p 3156) :=
  ElevenRUP.step79104 (p 2901) (p 2911) (p 3156) (p 3497) (p 4132) (p 4647) (derived73400 p h) (derived49826 p h)

theorem derived79108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3156) ∨ (p 2427) ∨ (¬ p 2563) :=
  ElevenRUP.step79108 (p 2427) (p 2563) (p 2901) (p 3156) (p 3497) (p 4235) (derived73400 p h) (derived73536 p h) (derived69490 p h)

theorem derived79109 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2220) ∨ (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 2958) ∨ (¬ p 2284) :=
  ElevenRUP.step79109 (p 2220) (p 2284) (p 2737) (p 2811) (p 2958) (p 3156) (p 3497) (derived73400 p h) (derived44260 p h)

theorem derived79114 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 4365) ∨ (¬ p 2742) ∨ (¬ p 2696) ∨ (¬ p 2166) ∨ (¬ p 2284) :=
  ElevenRUP.step79114 (p 2166) (p 2284) (p 2696) (p 2742) (p 3156) (p 3497) (p 4365) (derived73400 p h) (derived57421 p h)

theorem derived79115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2946) ∨ (¬ p 4313) ∨ (p 3156) :=
  ElevenRUP.step79115 (p 2619) (p 2946) (p 2952) (p 3156) (p 3497) (p 4313) (derived73330 p h) (derived73400 p h) (derived71410 p h)

theorem derived79117 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2417) ∨ (¬ p 3379) ∨ (¬ p 2254) ∨ (¬ p 2922) ∨ (p 2946) ∨ (p 3156) ∨ (¬ p 3950) :=
  ElevenRUP.step79117 (p 2254) (p 2417) (p 2922) (p 2946) (p 2952) (p 3146) (p 3156) (p 3379) (p 3497) (p 3692) (p 3950) (derived73448 p h) (derived73330 p h) (derived73400 p h) (derived59524 p h)

theorem derived79118 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 3389) ∨ (¬ p 2417) ∨ (¬ p 2249) ∨ (p 2946) ∨ (¬ p 2656) ∨ (¬ p 3950) ∨ (¬ p 2727) ∨ (p 3146) :=
  ElevenRUP.step79118 (p 2249) (p 2417) (p 2656) (p 2727) (p 2946) (p 2952) (p 3146) (p 3156) (p 3389) (p 3497) (p 3692) (p 3950) (derived73400 p h) (derived73330 p h) (derived73448 p h) (derived51866 p h)

theorem derived79120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 3146) ∨ (¬ p 3564) ∨ (¬ p 3422) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 4330) ∨ (p 3156) ∨ (¬ p 2598) ∨ (p 2946) :=
  ElevenRUP.step79120 (p 2252) (p 2598) (p 2750) (p 2753) (p 2946) (p 2952) (p 3146) (p 3156) (p 3422) (p 3497) (p 3564) (p 3692) (p 4330) (derived73448 p h) (derived73400 p h) (derived73330 p h) (derived64859 p h)

theorem derived79121 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3276) ∨ (p 3156) ∨ (¬ p 3362) ∨ (¬ p 4330) ∨ (¬ p 4789) ∨ (¬ p 3355) ∨ (p 2946) ∨ (p 3146) :=
  ElevenRUP.step79121 (p 2946) (p 2952) (p 3146) (p 3156) (p 3276) (p 3355) (p 3362) (p 3461) (p 3497) (p 3692) (p 4191) (p 4330) (p 4789) (derived73530 p h) (derived73400 p h) (derived73330 p h) (derived73448 p h) (derived64966 p h)

theorem derived79124 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3266) ∨ (p 2946) ∨ (p 3156) :=
  ElevenRUP.step79124 (p 2946) (p 2952) (p 3146) (p 3156) (p 3266) (p 3497) (p 3692) (p 4444) (derived73448 p h) (derived73580 p h) (derived73330 p h) (derived73400 p h) (derived45256 p h)

theorem derived79125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3125) ∨ (p 3156) :=
  ElevenRUP.step79125 (p 3125) (p 3156) (p 3323) (p 3497) (p 3744) (derived73454 p h) (derived73400 p h) (derived69773 p h)

theorem derived79127 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2992) ∨ (¬ p 2255) ∨ (¬ p 2220) ∨ (¬ p 2958) :=
  ElevenRUP.step79127 (p 2220) (p 2255) (p 2958) (p 2992) (p 3156) (p 3497) (p 3662) (derived73400 p h) (derived73440 p h) (derived59642 p h)

theorem derived79129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3156) ∨ (¬ p 2220) ∨ (p 2417) ∨ (p 2598) ∨ (¬ p 4395) ∨ (¬ p 2139) ∨ (p 3201) :=
  ElevenRUP.step79129 (p 2139) (p 2220) (p 2417) (p 2598) (p 3055) (p 3115) (p 3156) (p 3201) (p 3497) (p 3876) (p 4278) (p 4395) (derived73400 p h) (derived73546 p h) (derived73350 p h) (derived73486 p h) (derived61841 p h)

theorem derived79131 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2958) ∨ (p 2651) ∨ (p 3156) ∨ (¬ p 2220) :=
  ElevenRUP.step79131 (p 2220) (p 2651) (p 2657) (p 2958) (p 3156) (p 3497) (p 4704) (derived73288 p h) (derived73400 p h) (derived73046 p h) (derived41731 p h)

theorem derived79133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2122) ∨ (¬ p 2750) ∨ (p 2946) ∨ (¬ p 2252) ∨ (p 3156) ∨ (¬ p 3950) ∨ (p 3146) ∨ (¬ p 2753) ∨ (¬ p 2774) :=
  ElevenRUP.step79133 (p 2122) (p 2252) (p 2396) (p 2750) (p 2753) (p 2774) (p 2946) (p 2952) (p 3146) (p 3156) (p 3497) (p 3692) (p 3950) (derived73330 p h) (derived73400 p h) (derived73448 p h) (derived64857 p h)

theorem derived79134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3950) ∨ (p 3146) ∨ (¬ p 2252) ∨ (¬ p 2122) ∨ (p 2946) ∨ (¬ p 2750) ∨ (p 3156) ∨ (¬ p 2829) ∨ (¬ p 2396) :=
  ElevenRUP.step79134 (p 2122) (p 2252) (p 2396) (p 2750) (p 2829) (p 2946) (p 2952) (p 3146) (p 3156) (p 3497) (p 3692) (p 3950) (derived73448 p h) (derived73330 p h) (derived73400 p h) (derived57322 p h)

theorem derived79137 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3156) ∨ (¬ p 4241) ∨ (¬ p 2427) ∨ (¬ p 2459) :=
  ElevenRUP.step79137 (p 2427) (p 2459) (p 3146) (p 3156) (p 3497) (p 3692) (p 4241) (derived73448 p h) (derived73400 p h) (derived46173 p h)

theorem derived79139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4700) ∨ (p 3156) ∨ (¬ p 2850) ∨ (¬ p 2373) ∨ (¬ p 4753) :=
  ElevenRUP.step79139 (p 2373) (p 2850) (p 3156) (p 3497) (p 4700) (p 4753) (derived73400 p h) (derived42438 p h)

theorem derived79142 (p : Nat → Prop) (h : Inputs p) :
    (p 4355) ∨ (¬ p 2373) :=
  ElevenRUP.step79142 (p 2373) (p 4355) (p 5840) (derived74131 p h) (h 12036)

theorem derived79143 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (p 2284) ∨ (¬ p 4702) ∨ (p 2187) ∨ (¬ p 2563) ∨ (¬ p 2651) :=
  ElevenRUP.step79143 (p 2187) (p 2284) (p 2331) (p 2563) (p 2651) (p 2963) (p 3989) (p 4562) (p 4702) (derived73338 p h) (derived73638 p h) (derived73502 p h) (derived67099 p h)

theorem derived79151 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2946) ∨ (p 2187) ∨ (p 3136) ∨ (¬ p 3745) :=
  ElevenRUP.step79151 (p 2187) (p 2331) (p 2946) (p 2963) (p 3136) (p 3745) (p 3989) (p 4315) (derived73338 p h) (derived73502 p h) (derived73550 p h) (derived44992 p h)

theorem derived79154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4341) ∨ (p 2363) ∨ (p 2352) ∨ (¬ p 4976) :=
  ElevenRUP.step79154 (p 2352) (p 2363) (p 3256) (p 3956) (p 4341) (p 4347) (p 4976) (derived73560 p h) (derived73500 p h) (derived49461 p h)

theorem derived79157 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 5062) :=
  ElevenRUP.step79157 (p 3156) (p 5061) (p 5062) (derived73900 p h) (h 8491)

theorem derived79158 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 5063) :=
  ElevenRUP.step79158 (p 3156) (p 5061) (p 5063) (derived73900 p h) (h 8492)

theorem derived79159 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4241) ∨ (p 2284) ∨ (¬ p 2563) :=
  ElevenRUP.step79159 (p 2284) (p 2563) (p 3952) (p 4110) (p 4241) (derived73496 p h) (derived73515 p h) (h 6465)

theorem derived79163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4241) ∨ (p 2284) ∨ (¬ p 2563) :=
  ElevenRUP.step79163 (p 2284) (p 2563) (p 3952) (p 4241) (derived73496 p h) (h 27267)

theorem derived79165 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 4241) ∨ (¬ p 2459) ∨ (¬ p 2563) ∨ (¬ p 4119) ∨ (p 2901) :=
  ElevenRUP.step79165 (p 2459) (p 2563) (p 2901) (p 3146) (p 3692) (p 4119) (p 4241) (p 4320) (derived73448 p h) (derived73552 p h) (derived53338 p h)

theorem derived79166 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 4241) ∨ (¬ p 2662) ∨ (¬ p 4608) ∨ (¬ p 3136) ∨ (p 2630) :=
  ElevenRUP.step79166 (p 2470) (p 2476) (p 2630) (p 2662) (p 2810) (p 3136) (p 4241) (p 4608) (derived73250 p h) (derived73316 p h) (derived41367 p h)

theorem derived79167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (¬ p 2946) ∨ (¬ p 4241) ∨ (p 2230) :=
  ElevenRUP.step79167 (p 2230) (p 2589) (p 2655) (p 2946) (p 4241) (derived73284 p h) (h 20291)

theorem derived79168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2662) ∨ (¬ p 4715) ∨ (p 2573) ∨ (p 2630) ∨ (¬ p 4241) :=
  ElevenRUP.step79168 (p 2573) (p 2579) (p 2630) (p 2662) (p 2810) (p 3136) (p 4241) (p 4715) (derived73274 p h) (derived73316 p h) (derived54221 p h)

theorem derived79169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2449) ∨ (p 2573) ∨ (¬ p 4386) ∨ (¬ p 5201) ∨ (¬ p 4241) ∨ (¬ p 4715) :=
  ElevenRUP.step79169 (p 2449) (p 2573) (p 2579) (p 3516) (p 3947) (p 4241) (p 4386) (p 4715) (p 5201) (derived73494 p h) (derived73274 p h) (derived57716 p h)

theorem derived79172 (p : Nat → Prop) (h : Inputs p) :
    (p 4336) ∨ (¬ p 2284) :=
  ElevenRUP.step79172 (p 2284) (p 4336) (p 5822) (derived74107 p h) (h 11929)

theorem derived79173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2459) ∨ (¬ p 2363) ∨ (p 2295) :=
  ElevenRUP.step79173 (p 2295) (p 2363) (p 2459) (p 2668) (p 3568) (p 4348) (derived73562 p h) (derived73416 p h) (derived43461 p h)

theorem derived79175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2668) ∨ (p 2651) ∨ (p 2352) :=
  ElevenRUP.step79175 (p 2331) (p 2352) (p 2651) (p 2657) (p 2668) (p 3956) (derived73288 p h) (derived73500 p h) (derived43187 p h)

theorem derived79176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (p 2187) ∨ (¬ p 2274) :=
  ElevenRUP.step79176 (p 2187) (p 2274) (p 2641) (p 2668) (p 3989) (derived73502 p h) (derived45721 p h)

theorem derived79177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2363) ∨ (p 2651) ∨ (¬ p 2331) :=
  ElevenRUP.step79177 (p 2331) (p 2363) (p 2651) (p 2657) (p 2668) (derived73288 p h) (derived56486 p h)

theorem derived79178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (p 2727) ∨ (¬ p 2363) :=
  ElevenRUP.step79178 (p 2363) (p 2641) (p 2668) (p 2727) (p 4111) (derived73518 p h) (derived64593 p h)

theorem derived79180 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 2668) ∨ (¬ p 2363) ∨ (¬ p 4604) :=
  ElevenRUP.step79180 (p 2363) (p 2668) (p 3323) (p 4037) (p 4604) (derived73508 p h) (derived53146 p h)

theorem derived79182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2668) ∨ (p 2459) ∨ (¬ p 2363) :=
  ElevenRUP.step79182 (p 2331) (p 2363) (p 2459) (p 2668) (p 4348) (derived73562 p h) (derived45488 p h)

theorem derived79185 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2891) ∨ (¬ p 2797) ∨ (¬ p 4733) ∨ (p 2881) ∨ (¬ p 2696) ∨ (¬ p 2668) ∨ (¬ p 4133) :=
  ElevenRUP.step79185 (p 2210) (p 2668) (p 2696) (p 2797) (p 2881) (p 2891) (p 3486) (p 3555) (p 3570) (p 4133) (p 4733) (derived73412 p h) (derived73398 p h) (derived73418 p h) (derived50538 p h)

theorem derived79187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2668) ∨ (¬ p 2363) ∨ (p 2737) ∨ (¬ p 4328) :=
  ElevenRUP.step79187 (p 2363) (p 2668) (p 2737) (p 2743) (p 2829) (p 4328) (derived73298 p h) (derived45523 p h)

theorem derived79188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2274) ∨ (p 2187) ∨ (¬ p 2331) :=
  ElevenRUP.step79188 (p 2187) (p 2274) (p 2331) (p 2668) (p 3989) (derived73502 p h) (derived43283 p h)

theorem derived79193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2668) ∨ (p 2651) ∨ (p 2187) :=
  ElevenRUP.step79193 (p 2187) (p 2331) (p 2651) (p 2657) (p 2668) (p 3989) (derived73288 p h) (derived73502 p h) (derived53894 p h)

theorem derived79195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 2668) ∨ (p 2630) ∨ (p 2187) :=
  ElevenRUP.step79195 (p 2187) (p 2630) (p 2668) (p 2797) (p 2810) (p 3989) (derived73316 p h) (derived73502 p h) (derived47205 p h)

theorem derived79197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3146) ∨ (¬ p 3988) ∨ (¬ p 2363) :=
  ElevenRUP.step79197 (p 2363) (p 2668) (p 3146) (p 3692) (p 3988) (p 4560) (derived73448 p h) (derived72955 p h) (derived51558 p h)

theorem derived79202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3422) ∨ (¬ p 3019) ∨ (¬ p 4750) ∨ (p 2352) :=
  ElevenRUP.step79202 (p 2352) (p 2668) (p 3019) (p 3422) (p 3584) (p 3956) (p 4750) (derived73426 p h) (derived73500 p h) (derived51003 p h)

theorem derived79203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2295) ∨ (p 2352) ∨ (p 2573) :=
  ElevenRUP.step79203 (p 2295) (p 2352) (p 2573) (p 2579) (p 2668) (p 3568) (p 3956) (derived73416 p h) (derived73500 p h) (derived73274 p h) (derived45971 p h)

theorem derived79204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2295) ∨ (p 2352) ∨ (p 2493) :=
  ElevenRUP.step79204 (p 2295) (p 2352) (p 2493) (p 2499) (p 2668) (p 3568) (p 3956) (derived73416 p h) (derived73500 p h) (derived73260 p h) (derived43445 p h)

theorem derived79209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 4389) ∨ (p 2352) :=
  ElevenRUP.step79209 (p 2352) (p 2668) (p 3956) (p 4389) (derived73500 p h) (h 37130)

theorem derived79210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2528) ∨ (¬ p 4976) ∨ (¬ p 2363) ∨ (¬ p 3573) :=
  ElevenRUP.step79210 (p 2363) (p 2528) (p 2534) (p 2668) (p 3573) (p 4976) (derived73268 p h) (derived42052 p h)

theorem derived79212 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 2668) ∨ (¬ p 2573) ∨ (¬ p 4976) ∨ (¬ p 4432) :=
  ElevenRUP.step79212 (p 2470) (p 2476) (p 2573) (p 2668) (p 4432) (p 4976) (derived73250 p h) (derived59651 p h)

theorem derived79213 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 2668) ∨ (¬ p 2608) ∨ (¬ p 2246) ∨ (¬ p 2744) ∨ (¬ p 4669) ∨ (¬ p 2363) ∨ (p 3631) ∨ (¬ p 2331) :=
  ElevenRUP.step79213 (p 2246) (p 2331) (p 2363) (p 2608) (p 2668) (p 2744) (p 3399) (p 3631) (p 3817) (p 4366) (p 4669) (derived73570 p h) (derived73468 p h) (derived58006 p h)

theorem derived79216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2295) ∨ (¬ p 3550) ∨ (p 2881) ∨ (¬ p 4556) :=
  ElevenRUP.step79216 (p 2295) (p 2668) (p 2881) (p 3550) (p 3568) (p 3570) (p 4556) (derived73416 p h) (derived73418 p h) (derived50560 p h)

theorem derived79218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2668) ∨ (p 2352) ∨ (p 2493) :=
  ElevenRUP.step79218 (p 2352) (p 2493) (p 2499) (p 2668) (p 2922) (p 3956) (derived73500 p h) (derived73260 p h) (derived63465 p h)

theorem derived79222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2363) ∨ (¬ p 2331) ∨ (p 2132) ∨ (p 2870) ∨ (¬ p 4786) ∨ (¬ p 4669) ∨ (p 3246) :=
  ElevenRUP.step79222 (p 2132) (p 2138) (p 2331) (p 2363) (p 2668) (p 2870) (p 3246) (p 3690) (p 4244) (p 4669) (p 4786) (derived73214 p h) (derived73540 p h) (derived73446 p h) (derived54399 p h)

theorem derived79223 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2668) ∨ (¬ p 3958) ∨ (p 2352) ∨ (¬ p 2274) :=
  ElevenRUP.step79223 (p 2274) (p 2295) (p 2352) (p 2668) (p 3568) (p 3956) (p 3958) (derived73416 p h) (derived73500 p h) (derived51967 p h)

theorem derived79225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2383) ∨ (¬ p 2667) :=
  ElevenRUP.step79225 (p 2383) (p 2387) (p 2667) (p 2668) (derived73246 p h) (h 3461)

theorem derived79226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 2668) ∨ (¬ p 4108) ∨ (p 2870) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (p 2230) ∨ (p 2982) ∨ (¬ p 2363) :=
  ElevenRUP.step79226 (p 2230) (p 2248) (p 2331) (p 2363) (p 2589) (p 2668) (p 2870) (p 2982) (p 3105) (p 4108) (p 4244) (p 4948) (derived73540 p h) (derived73284 p h) (derived73846 p h) (derived49130 p h)

theorem derived79227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2573) ∨ (¬ p 2440) ∨ (¬ p 3019) ∨ (p 2352) :=
  ElevenRUP.step79227 (p 2352) (p 2440) (p 2573) (p 2579) (p 2668) (p 3019) (p 3956) (derived73274 p h) (derived73500 p h) (derived45863 p h)

theorem derived79228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2440) ∨ (¬ p 3019) ∨ (p 2493) ∨ (¬ p 4257) ∨ (p 2352) :=
  ElevenRUP.step79228 (p 2352) (p 2440) (p 2493) (p 2499) (p 2668) (p 3019) (p 3956) (p 4257) (derived73260 p h) (derived73500 p h) (derived55488 p h)

theorem derived79230 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 4171) ∨ (¬ p 2528) ∨ (¬ p 4384) ∨ (¬ p 2668) :=
  ElevenRUP.step79230 (p 2528) (p 2668) (p 3323) (p 4037) (p 4171) (p 4384) (derived73508 p h) (derived59372 p h)

theorem derived79234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5274) ∨ (¬ p 5284) ∨ (¬ p 3266) ∨ (p 2383) ∨ (¬ p 2668) :=
  ElevenRUP.step79234 (p 2383) (p 2387) (p 2668) (p 3266) (p 5274) (p 5284) (derived73246 p h) (derived46944 p h)

theorem derived79235 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2668) ∨ (¬ p 2363) ∨ (¬ p 2274) :=
  ElevenRUP.step79235 (p 2274) (p 2295) (p 2363) (p 2668) (p 3568) (derived73416 p h) (derived53623 p h)

theorem derived79236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 4336) ∨ (p 2383) ∨ (¬ p 4705) ∨ (p 2563) ∨ (¬ p 4356) :=
  ElevenRUP.step79236 (p 2383) (p 2387) (p 2563) (p 2668) (p 4110) (p 4336) (p 4356) (p 4705) (derived73246 p h) (derived73516 p h) (derived42053 p h)

theorem derived79238 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3564) ∨ (¬ p 4405) ∨ (¬ p 2668) ∨ (p 2553) :=
  ElevenRUP.step79238 (p 2553) (p 2588) (p 2668) (p 3323) (p 3564) (p 4037) (p 4405) (derived73508 p h) (derived73282 p h) (derived48135 p h)

theorem derived79243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2668) ∨ (¬ p 3979) ∨ (¬ p 4171) ∨ (p 3323) :=
  ElevenRUP.step79243 (p 2668) (p 3323) (p 3979) (p 4037) (p 4171) (p 5568) (derived73508 p h) (derived59756 p h)

theorem derived79246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (¬ p 2668) ∨ (p 2295) ∨ (¬ p 3361) ∨ (p 2737) ∨ (p 2383) :=
  ElevenRUP.step79246 (p 2295) (p 2383) (p 2387) (p 2668) (p 2737) (p 2743) (p 3361) (p 3568) (p 3983) (derived73416 p h) (derived73298 p h) (derived73246 p h) (derived46868 p h)

theorem derived79249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3983) ∨ (¬ p 2797) ∨ (p 2383) :=
  ElevenRUP.step79249 (p 2383) (p 2387) (p 2668) (p 2797) (p 3983) (derived73246 p h) (derived71415 p h)

theorem derived79251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 2668) ∨ (p 2598) ∨ (¬ p 4749) ∨ (p 3323) ∨ (p 2383) ∨ (¬ p 4841) ∨ (¬ p 3434) ∨ (p 3425) ∨ (¬ p 4625) :=
  ElevenRUP.step79251 (p 2383) (p 2387) (p 2598) (p 2668) (p 2785) (p 3055) (p 3323) (p 3425) (p 3434) (p 3471) (p 4037) (p 4625) (p 4749) (p 4841) (derived73350 p h) (derived73508 p h) (derived73246 p h) (derived73396 p h) (derived63346 p h)

theorem derived79254 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 2509) ∨ (¬ p 2668) ∨ (¬ p 2459) ∨ (¬ p 3550) ∨ (p 3379) ∨ (¬ p 2331) ∨ (¬ p 5118) ∨ (¬ p 2248) :=
  ElevenRUP.step79254 (p 2248) (p 2331) (p 2459) (p 2509) (p 2668) (p 3379) (p 3452) (p 3550) (p 4149) (p 4286) (p 5118) (derived73548 p h) (derived73394 p h) (derived50433 p h)

theorem derived79255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2331) ∨ (¬ p 3136) ∨ (p 2946) :=
  ElevenRUP.step79255 (p 2331) (p 2668) (p 2946) (p 2952) (p 3136) (derived73330 p h) (derived62056 p h)

theorem derived79259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2427) ∨ (¬ p 2563) ∨ (¬ p 4275) ∨ (¬ p 4405) ∨ (¬ p 3745) :=
  ElevenRUP.step79259 (p 2427) (p 2563) (p 2668) (p 3745) (p 4235) (p 4275) (p 4405) (derived73536 p h) (derived54706 p h)

theorem derived79263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3323) ∨ (¬ p 2668) ∨ (¬ p 2563) :=
  ElevenRUP.step79263 (p 2563) (p 2668) (p 3125) (p 3323) (p 4037) (derived73508 p h) (derived44506 p h)

theorem derived79266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 5660) ∨ (¬ p 2668) ∨ (¬ p 3389) ∨ (p 2295) ∨ (¬ p 2787) ∨ (¬ p 3362) ∨ (¬ p 4556) ∨ (p 2383) :=
  ElevenRUP.step79266 (p 2295) (p 2383) (p 2387) (p 2668) (p 2787) (p 3362) (p 3389) (p 3568) (p 3868) (p 4556) (p 5660) (derived73416 p h) (derived73246 p h) (derived64699 p h)

theorem derived79270 (p : Nat → Prop) (h : Inputs p) :
    (p 4361) ∨ (¬ p 2295) :=
  ElevenRUP.step79270 (p 2295) (p 4361) (p 4571) (derived73644 p h) (h 7245)

theorem derived79271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (¬ p 3564) ∨ (¬ p 2331) :=
  ElevenRUP.step79271 (p 2295) (p 2331) (p 2553) (p 2588) (p 3564) (derived73282 p h) (derived43704 p h)

theorem derived79272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (p 2352) ∨ (¬ p 3564) :=
  ElevenRUP.step79272 (p 2295) (p 2352) (p 3323) (p 3564) (p 3956) (p 4037) (derived73508 p h) (derived73500 p h) (derived44212 p h)

theorem derived79273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (p 2274) ∨ (¬ p 3564) :=
  ElevenRUP.step79273 (p 2274) (p 2295) (p 3097) (p 3323) (p 3564) (p 4037) (derived73508 p h) (derived73352 p h) (derived60748 p h)

theorem derived79276 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2295) ∨ (p 3422) ∨ (¬ p 4750) ∨ (¬ p 3019) ∨ (¬ p 2386) :=
  ElevenRUP.step79276 (p 2295) (p 2307) (p 2313) (p 2386) (p 3019) (p 3422) (p 3584) (p 4750) (derived73238 p h) (derived73426 p h) (derived57742 p h)

theorem derived79278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (¬ p 2659) ∨ (p 2573) ∨ (¬ p 3019) :=
  ElevenRUP.step79278 (p 2295) (p 2553) (p 2573) (p 2579) (p 2588) (p 2659) (p 3019) (derived73282 p h) (derived73274 p h) (derived41816 p h)

theorem derived79279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3323) ∨ (¬ p 2295) ∨ (¬ p 2774) :=
  ElevenRUP.step79279 (p 2295) (p 2774) (p 3323) (p 3483) (p 4037) (derived73508 p h) (derived43048 p h)

theorem derived79281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3921) ∨ (p 3389) ∨ (¬ p 4976) ∨ (¬ p 2573) :=
  ElevenRUP.step79281 (p 2295) (p 2573) (p 3389) (p 3540) (p 3921) (p 4976) (derived73402 p h) (derived41690 p h)

theorem derived79282 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (p 2553) :=
  ElevenRUP.step79282 (p 2295) (p 2352) (p 2363) (p 2553) (p 2588) (derived73282 p h) (derived46697 p h)

theorem derived79283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 4389) ∨ (p 2553) :=
  ElevenRUP.step79283 (p 2295) (p 2553) (p 2588) (p 4389) (derived73282 p h) (h 20173)

theorem derived79284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2295) ∨ (p 2553) ∨ (¬ p 2241) :=
  ElevenRUP.step79284 (p 2241) (p 2295) (p 2553) (p 2588) (p 2641) (derived73282 p h) (derived43165 p h)

theorem derived79286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (p 2553) ∨ (p 2727) :=
  ElevenRUP.step79286 (p 2295) (p 2553) (p 2588) (p 2641) (p 2727) (p 4111) (derived73282 p h) (derived73518 p h) (derived62330 p h)

theorem derived79287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (p 2651) ∨ (¬ p 2331) :=
  ElevenRUP.step79287 (p 2295) (p 2331) (p 2553) (p 2588) (p 2651) (p 2657) (derived73282 p h) (derived73288 p h) (derived42774 p h)

theorem derived79289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2295) ∨ (¬ p 2241) ∨ (p 2274) :=
  ElevenRUP.step79289 (p 2241) (p 2274) (p 2295) (p 2641) (p 3097) (derived73352 p h) (derived47666 p h)

theorem derived79291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (p 2651) ∨ (p 2274) :=
  ElevenRUP.step79291 (p 2274) (p 2295) (p 2331) (p 2651) (p 2657) (p 3097) (derived73288 p h) (derived73352 p h) (derived57710 p h)

theorem derived79292 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (p 2274) ∨ (p 2946) :=
  ElevenRUP.step79292 (p 2274) (p 2295) (p 2331) (p 2946) (p 2952) (p 3097) (derived73352 p h) (derived73330 p h) (derived44385 p h)

theorem derived79294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2655) ∨ (¬ p 2797) ∨ (p 2307) ∨ (¬ p 2577) :=
  ElevenRUP.step79294 (p 2295) (p 2307) (p 2313) (p 2577) (p 2655) (p 2797) (derived73238 p h) (derived71416 p h)

theorem derived79301 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2295) ∨ (¬ p 2386) ∨ (¬ p 4717) ∨ (¬ p 2440) ∨ (¬ p 3019) :=
  ElevenRUP.step79301 (p 2295) (p 2307) (p 2313) (p 2386) (p 2440) (p 3019) (p 4717) (derived73238 p h) (derived40921 p h)

theorem derived79304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (¬ p 2663) ∨ (¬ p 2230) ∨ (¬ p 3019) ∨ (¬ p 2440) :=
  ElevenRUP.step79304 (p 2230) (p 2295) (p 2440) (p 2553) (p 2588) (p 2663) (p 3019) (derived73282 p h) (derived63971 p h)

theorem derived79307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2295) ∨ (p 2307) ∨ (p 2493) ∨ (¬ p 4811) ∨ (¬ p 3019) :=
  ElevenRUP.step79307 (p 2295) (p 2307) (p 2313) (p 2386) (p 2493) (p 2499) (p 3019) (p 4811) (derived73238 p h) (derived73260 p h) (derived41151 p h)

theorem derived79312 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2295) ∨ (¬ p 4275) ∨ (¬ p 2156) :=
  ElevenRUP.step79312 (p 2156) (p 2295) (p 3051) (p 3556) (p 4275) (p 4560) (derived73414 p h) (derived72955 p h) (derived50943 p h)

theorem derived79315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2881) ∨ (¬ p 2177) ∨ (¬ p 4204) :=
  ElevenRUP.step79315 (p 2177) (p 2295) (p 2881) (p 3570) (p 4204) (p 4560) (derived73418 p h) (derived72955 p h) (derived47995 p h)

theorem derived79319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3323) ∨ (¬ p 4396) ∨ (¬ p 4559) ∨ (¬ p 2295) :=
  ElevenRUP.step79319 (p 2295) (p 3246) (p 3323) (p 4037) (p 4396) (p 4559) (derived73508 p h) (derived58428 p h)

theorem derived79320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 2321) ∨ (p 3323) ∨ (¬ p 4396) ∨ (¬ p 2295) :=
  ElevenRUP.step79320 (p 2295) (p 2321) (p 3323) (p 3516) (p 4037) (p 4396) (derived73508 p h) (derived48393 p h)

theorem derived79322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2417) ∨ (¬ p 4396) ∨ (¬ p 4712) ∨ (p 3323) :=
  ElevenRUP.step79322 (p 2295) (p 2417) (p 3323) (p 4037) (p 4396) (p 4712) (derived73508 p h) (derived56370 p h)

theorem derived79325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 4668) ∨ (p 2668) ∨ (¬ p 4138) :=
  ElevenRUP.step79325 (p 2295) (p 2396) (p 2668) (p 3324) (p 4138) (p 4668) (derived73386 p h) (derived55447 p h)

theorem derived79331 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 2295) ∨ (¬ p 4196) ∨ (¬ p 4170) ∨ (¬ p 2088) :=
  ElevenRUP.step79331 (p 2088) (p 2295) (p 3256) (p 4118) (p 4170) (p 4196) (derived73520 p h) (derived71418 p h)

theorem derived79335 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 2295) ∨ (¬ p 4437) ∨ (¬ p 2331) ∨ (¬ p 4432) :=
  ElevenRUP.step79335 (p 2295) (p 2331) (p 3166) (p 3172) (p 4432) (p 4437) (derived73356 p h) (derived71420 p h)

theorem derived79343 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2295) ∨ (p 3309) ∨ (p 2668) :=
  ElevenRUP.step79343 (p 2295) (p 2668) (p 3093) (p 3309) (p 3324) (p 3549) (p 3591) (derived73432 p h) (derived73406 p h) (derived73386 p h) (derived46193 p h)

theorem derived79344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2341) ∨ (p 2668) ∨ (¬ p 2312) ∨ (¬ p 4503) :=
  ElevenRUP.step79344 (p 2295) (p 2312) (p 2341) (p 2668) (p 3324) (p 4503) (derived73386 p h) (derived41437 p h)

theorem derived79349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (¬ p 2295) ∨ (p 2737) ∨ (p 2307) ∨ (¬ p 3361) ∨ (p 2668) :=
  ElevenRUP.step79349 (p 2295) (p 2307) (p 2313) (p 2668) (p 2737) (p 2743) (p 3324) (p 3361) (p 3983) (derived73298 p h) (derived73238 p h) (derived73386 p h) (derived46813 p h)

theorem derived79350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 5564) ∨ (¬ p 4138) ∨ (p 2668) ∨ (¬ p 2295) :=
  ElevenRUP.step79350 (p 2295) (p 2668) (p 3324) (p 3791) (p 4138) (p 5564) (derived73386 p h) (derived41665 p h)

theorem derived79352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3325) ∨ (¬ p 3990) ∨ (p 3323) :=
  ElevenRUP.step79352 (p 2295) (p 3323) (p 3325) (p 3990) (p 4037) (derived73508 p h) (h 20637)

theorem derived79355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2295) ∨ (p 2563) ∨ (p 2230) ∨ (¬ p 2241) ∨ (¬ p 5193) ∨ (p 2187) :=
  ElevenRUP.step79355 (p 2187) (p 2230) (p 2241) (p 2295) (p 2563) (p 2589) (p 2641) (p 3989) (p 4110) (p 5193) (derived73516 p h) (derived73284 p h) (derived73502 p h) (derived71421 p h)

theorem derived79356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2295) ∨ (p 2341) ∨ (¬ p 2696) ∨ (¬ p 5197) ∨ (p 3367) ∨ (¬ p 2641) ∨ (¬ p 3363) ∨ (¬ p 2742) ∨ (¬ p 4712) :=
  ElevenRUP.step79356 (p 2295) (p 2341) (p 2641) (p 2696) (p 2742) (p 2911) (p 3363) (p 3367) (p 3551) (p 3585) (p 4712) (p 5197) (derived73408 p h) (derived73428 p h) (derived71422 p h)

theorem derived79358 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2295) ∨ (¬ p 2177) ∨ (¬ p 4976) ∨ (¬ p 3581) :=
  ElevenRUP.step79358 (p 2177) (p 2295) (p 2911) (p 3581) (p 3644) (p 4976) (derived73434 p h) (derived41815 p h)

theorem derived79361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 2295) ∨ (p 2668) ∨ (¬ p 4559) ∨ (¬ p 4138) :=
  ElevenRUP.step79361 (p 2295) (p 2668) (p 2881) (p 3324) (p 4138) (p 4559) (derived73386 p h) (derived48283 p h)

theorem derived79363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2363) ∨ (p 2668) ∨ (¬ p 2459) :=
  ElevenRUP.step79363 (p 2295) (p 2363) (p 2459) (p 2668) (p 3324) (p 4347) (derived73560 p h) (derived73386 p h) (derived52342 p h)

theorem derived79364 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2295) ∨ (p 2668) ∨ (¬ p 4356) ∨ (p 2563) :=
  ElevenRUP.step79364 (p 2295) (p 2307) (p 2313) (p 2563) (p 2668) (p 3324) (p 4110) (p 4356) (derived73238 p h) (derived73386 p h) (derived73516 p h) (derived56690 p h)

theorem derived79365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2363) ∨ (p 2668) ∨ (p 2307) :=
  ElevenRUP.step79365 (p 2295) (p 2307) (p 2313) (p 2363) (p 2668) (p 3324) (p 4347) (derived73560 p h) (derived73386 p h) (derived73238 p h) (derived42810 p h)

theorem derived79368 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2295) ∨ (¬ p 2662) ∨ (p 3389) ∨ (p 2727) ∨ (¬ p 2255) ∨ (¬ p 4666) ∨ (¬ p 2177) ∨ (¬ p 2331) :=
  ElevenRUP.step79368 (p 2177) (p 2255) (p 2295) (p 2331) (p 2417) (p 2662) (p 2727) (p 3389) (p 3540) (p 4111) (p 4278) (p 4666) (derived73546 p h) (derived73402 p h) (derived73518 p h) (derived60337 p h)

theorem derived79370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2295) ∨ (p 2946) ∨ (¬ p 3136) :=
  ElevenRUP.step79370 (p 2295) (p 2331) (p 2946) (p 2952) (p 3136) (derived73330 p h) (derived62055 p h)

theorem derived79374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2295) ∨ (¬ p 2249) ∨ (¬ p 3983) ∨ (p 2307) :=
  ElevenRUP.step79374 (p 2249) (p 2295) (p 2307) (p 2313) (p 2641) (p 3983) (derived73238 p h) (derived51739 p h)

theorem derived79376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2274) ∨ (p 2406) ∨ (¬ p 2667) ∨ (¬ p 2493) ∨ (¬ p 2578) :=
  ElevenRUP.step79376 (p 2274) (p 2295) (p 2406) (p 2493) (p 2578) (p 2667) (p 3097) (p 3238) (derived73352 p h) (derived73374 p h) (derived47388 p h)

theorem derived79378 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 3983) ∨ (¬ p 4563) ∨ (¬ p 2295) ∨ (¬ p 2946) :=
  ElevenRUP.step79378 (p 2295) (p 2307) (p 2313) (p 2946) (p 3983) (p 4563) (derived73238 p h) (derived54164 p h)

theorem derived79379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3246) ∨ (¬ p 2396) :=
  ElevenRUP.step79379 (p 2295) (p 2396) (p 3246) (p 3690) (p 4107) (p 4560) (derived73446 p h) (derived72955 p h) (derived73513 p h) (derived66930 p h)

theorem derived79383 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 3983) ∨ (¬ p 2797) ∨ (¬ p 2295) :=
  ElevenRUP.step79383 (p 2295) (p 2307) (p 2313) (p 2797) (p 3983) (derived73238 p h) (derived71425 p h)

theorem derived79386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2307) ∨ (¬ p 2797) ∨ (¬ p 2295) :=
  ElevenRUP.step79386 (p 2295) (p 2307) (p 2313) (p 2797) (p 3654) (derived73238 p h) (derived56350 p h)

theorem derived79388 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3146) ∨ (¬ p 3325) ∨ (¬ p 3988) ∨ (¬ p 2363) :=
  ElevenRUP.step79388 (p 2295) (p 2363) (p 3146) (p 3325) (p 3692) (p 3988) (p 4560) (derived73448 p h) (derived72955 p h) (derived62245 p h)

theorem derived79389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2177) ∨ (p 2651) :=
  ElevenRUP.step79389 (p 2177) (p 2295) (p 2331) (p 2651) (p 2657) (derived73288 p h) (derived44890 p h)

theorem derived79390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2295) ∨ (¬ p 2373) ∨ (¬ p 3983) ∨ (p 2307) ∨ (¬ p 3379) ∨ (¬ p 4433) ∨ (¬ p 2254) ∨ (p 2668) :=
  ElevenRUP.step79390 (p 2254) (p 2295) (p 2307) (p 2313) (p 2373) (p 2406) (p 2668) (p 3324) (p 3379) (p 3983) (p 4433) (derived73238 p h) (derived73386 p h) (derived63350 p h)

theorem derived79391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2241) ∨ (p 2911) ∨ (p 3389) ∨ (¬ p 2881) ∨ (¬ p 2295) ∨ (¬ p 5193) ∨ (¬ p 4559) :=
  ElevenRUP.step79391 (p 2241) (p 2295) (p 2641) (p 2881) (p 2911) (p 3389) (p 3540) (p 3644) (p 4559) (p 5193) (derived73434 p h) (derived73402 p h) (derived60472 p h)

theorem derived79393 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (p 3516) ∨ (¬ p 2881) ∨ (¬ p 4283) :=
  ElevenRUP.step79393 (p 2295) (p 2396) (p 2881) (p 3516) (p 3821) (p 4283) (derived73470 p h) (derived57305 p h)

theorem derived79396 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2088) ∨ (¬ p 3146) ∨ (¬ p 2177) ∨ (¬ p 4905) ∨ (p 3136) ∨ (¬ p 2957) ∨ (¬ p 2331) ∨ (¬ p 3697) ∨ (¬ p 4790) :=
  ElevenRUP.step79396 (p 2088) (p 2177) (p 2295) (p 2331) (p 2957) (p 3136) (p 3146) (p 3697) (p 3857) (p 4315) (p 4790) (p 4905) (derived73480 p h) (derived73550 p h) (derived53222 p h)

theorem derived79403 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3323) ∨ (¬ p 2761) ∨ (¬ p 2295) :=
  ElevenRUP.step79403 (p 2295) (p 2761) (p 3323) (p 3461) (p 4037) (p 4191) (derived73530 p h) (derived73508 p h) (derived43756 p h)

theorem derived79404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 3461) ∨ (p 3323) ∨ (¬ p 2295) :=
  ElevenRUP.step79404 (p 2295) (p 3276) (p 3323) (p 3461) (p 4037) (p 4191) (derived73530 p h) (derived73508 p h) (derived43698 p h)

theorem derived79408 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (¬ p 2187) ∨ (¬ p 2156) ∨ (¬ p 2958) ∨ (¬ p 2295) :=
  ElevenRUP.step79408 (p 2156) (p 2187) (p 2295) (p 2668) (p 2958) (p 3324) (derived73386 p h) (derived42996 p h)

theorem derived79409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2274) ∨ (¬ p 2946) ∨ (¬ p 4336) ∨ (¬ p 2187) :=
  ElevenRUP.step79409 (p 2187) (p 2274) (p 2295) (p 2946) (p 3097) (p 4336) (derived73352 p h) (derived47765 p h)

theorem derived79411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2553) ∨ (¬ p 2352) ∨ (¬ p 2331) :=
  ElevenRUP.step79411 (p 2295) (p 2331) (p 2352) (p 2553) (p 2588) (derived73282 p h) (derived47640 p h)

theorem derived79412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2307) ∨ (¬ p 4356) ∨ (¬ p 4336) ∨ (p 2860) ∨ (¬ p 4906) :=
  ElevenRUP.step79412 (p 2295) (p 2307) (p 2313) (p 2860) (p 3758) (p 4336) (p 4356) (p 4906) (derived73238 p h) (derived73456 p h) (derived41640 p h)

theorem derived79413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2307) ∨ (¬ p 2295) ∨ (p 3564) :=
  ElevenRUP.step79413 (p 2295) (p 2307) (p 2313) (p 3564) (p 3654) (p 4137) (derived73238 p h) (derived73524 p h) (derived47886 p h)

theorem derived79414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2307) ∨ (p 2563) ∨ (¬ p 4705) ∨ (¬ p 4356) ∨ (¬ p 4336) :=
  ElevenRUP.step79414 (p 2295) (p 2307) (p 2313) (p 2563) (p 4110) (p 4336) (p 4356) (p 4705) (derived73238 p h) (derived73516 p h) (derived57466 p h)

theorem derived79417 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 3564) ∨ (p 2553) ∨ (¬ p 2797) ∨ (p 2241) ∨ (p 3189) ∨ (¬ p 4330) ∨ (¬ p 4967) ∨ (¬ p 2295) :=
  ElevenRUP.step79417 (p 2241) (p 2247) (p 2295) (p 2553) (p 2588) (p 2797) (p 3189) (p 3564) (p 3609) (p 4330) (p 4340) (p 4360) (p 4967) (derived73558 p h) (derived73282 p h) (derived73226 p h) (derived73566 p h) (derived46311 p h)

theorem derived79418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2619) ∨ (¬ p 4441) ∨ (p 2860) ∨ (p 2668) :=
  ElevenRUP.step79418 (p 2295) (p 2619) (p 2668) (p 2860) (p 3324) (p 3758) (p 4441) (derived73456 p h) (derived73386 p h) (derived47307 p h)

theorem derived79419 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 2528) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (¬ p 4786) ∨ (¬ p 2331) ∨ (¬ p 2295) ∨ (p 2598) :=
  ElevenRUP.step79419 (p 2295) (p 2331) (p 2396) (p 2528) (p 2534) (p 2598) (p 3055) (p 3641) (p 3874) (p 3950) (p 4786) (derived73484 p h) (derived73268 p h) (derived73350 p h) (derived57332 p h)

theorem derived79422 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2417) ∨ (¬ p 2177) ∨ (¬ p 2331) ∨ (¬ p 4786) ∨ (p 2598) ∨ (¬ p 2295) ∨ (¬ p 4666) :=
  ElevenRUP.step79422 (p 2177) (p 2295) (p 2331) (p 2417) (p 2598) (p 3055) (p 3201) (p 3876) (p 4278) (p 4666) (p 4786) (derived73486 p h) (derived73546 p h) (derived73350 p h) (derived52250 p h)

theorem derived79426 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2295) ∨ (p 3379) ∨ (p 2553) :=
  ElevenRUP.step79426 (p 2295) (p 2493) (p 2499) (p 2553) (p 2588) (p 3379) (p 3452) (derived73260 p h) (derived73394 p h) (derived73282 p h) (derived44181 p h)

theorem derived79427 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2946) ∨ (¬ p 3136) ∨ (¬ p 2252) ∨ (¬ p 2295) :=
  ElevenRUP.step79427 (p 2252) (p 2295) (p 2641) (p 2946) (p 2952) (p 3136) (derived73330 p h) (derived61494 p h)

theorem derived79433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 3323) ∨ (p 2274) ∨ (¬ p 2295) :=
  ElevenRUP.step79433 (p 2274) (p 2295) (p 3097) (p 3319) (p 3323) (p 4037) (derived73508 p h) (derived73352 p h) (derived44505 p h)

theorem derived79435 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 2295) ∨ (¬ p 3093) ∨ (p 3323) :=
  ElevenRUP.step79435 (p 2295) (p 3093) (p 3319) (p 3323) (p 4037) (derived73508 p h) (derived45337 p h)

theorem derived79439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2274) ∨ (¬ p 4705) ∨ (p 2563) :=
  ElevenRUP.step79439 (p 2274) (p 2295) (p 2563) (p 3097) (p 4110) (p 4705) (derived73352 p h) (derived73516 p h) (derived68872 p h)

theorem derived79442 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 2295) ∨ (¬ p 5045) ∨ (¬ p 2982) ∨ (p 2563) :=
  ElevenRUP.step79442 (p 2295) (p 2563) (p 2982) (p 3323) (p 4037) (p 4110) (p 5045) (derived73508 p h) (derived73516 p h) (derived44022 p h)

theorem derived79443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3323) ∨ (¬ p 3125) ∨ (¬ p 2177) :=
  ElevenRUP.step79443 (p 2177) (p 2295) (p 3125) (p 3323) (p 4037) (derived73508 p h) (derived47697 p h)

theorem derived79444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (p 2307) ∨ (¬ p 2383) :=
  ElevenRUP.step79444 (p 2295) (p 2307) (p 2313) (p 2383) (p 2641) (derived73238 p h) (derived43213 p h)

theorem derived79450 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2295) ∨ (¬ p 2584) ∨ (p 2668) ∨ (p 2230) :=
  ElevenRUP.step79450 (p 2230) (p 2295) (p 2383) (p 2584) (p 2589) (p 2668) (p 3324) (derived73386 p h) (derived73284 p h) (derived43209 p h)

theorem derived79455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 2312) ∨ (¬ p 4067) ∨ (p 2449) ∨ (¬ p 2274) ∨ (¬ p 4564) :=
  ElevenRUP.step79455 (p 2274) (p 2312) (p 2449) (p 3516) (p 3947) (p 4067) (p 4564) (derived73494 p h) (derived41245 p h)

theorem derived79456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2177) ∨ (p 2264) ∨ (¬ p 4973) ∨ (¬ p 4067) :=
  ElevenRUP.step79456 (p 2177) (p 2264) (p 2553) (p 3553) (p 4067) (p 4973) (derived73410 p h) (derived41405 p h)

theorem derived79457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 3984) ∨ (p 2264) ∨ (¬ p 4275) ∨ (¬ p 4067) ∨ (¬ p 2881) ∨ (¬ p 4624) :=
  ElevenRUP.step79457 (p 2264) (p 2881) (p 3553) (p 3564) (p 3984) (p 4067) (p 4275) (p 4624) (derived73410 p h) (derived49710 p h)

theorem derived79458 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2396) ∨ (¬ p 4067) ∨ (¬ p 4405) ∨ (p 2449) :=
  ElevenRUP.step79458 (p 2396) (p 2449) (p 2668) (p 3947) (p 4067) (p 4405) (derived73494 p h) (derived54891 p h)

theorem derived79462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 4067) ∨ (p 2264) ∨ (¬ p 2177) ∨ (¬ p 4624) :=
  ElevenRUP.step79462 (p 2177) (p 2264) (p 3323) (p 3553) (p 4067) (p 4624) (derived73410 p h) (derived51362 p h)

theorem derived79465 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 4067) ∨ (¬ p 2807) :=
  ElevenRUP.step79465 (p 2331) (p 2807) (p 2963) (p 4067) (derived73338 p h) (h 6052)

theorem derived79467 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2274) ∨ (¬ p 3986) :=
  ElevenRUP.step79467 (p 2274) (p 2295) (p 3568) (p 3986) (derived73416 p h) (h 20288)

theorem derived79472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 3986) ∨ (p 2668) ∨ (p 2563) ∨ (p 3309) :=
  ElevenRUP.step79472 (p 2563) (p 2668) (p 3063) (p 3309) (p 3324) (p 3549) (p 3986) (p 4110) (derived73386 p h) (derived73516 p h) (derived73406 p h) (derived46205 p h)

theorem derived79473 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (¬ p 2187) ∨ (¬ p 3986) :=
  ElevenRUP.step79473 (p 2187) (p 2668) (p 3324) (p 3986) (derived73386 p h) (h 6004)

theorem derived79480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5118) ∨ (¬ p 4345) ∨ (p 2668) ∨ (¬ p 3986) ∨ (¬ p 3125) :=
  ElevenRUP.step79480 (p 2668) (p 3125) (p 3324) (p 3986) (p 4345) (p 5118) (p 5580) (derived73386 p h) (derived49463 p h)

theorem derived79484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4045) ∨ (¬ p 3343) ∨ (p 3083) :=
  ElevenRUP.step79484 (p 3083) (p 3343) (p 3359) (p 4045) (p 4256) (derived73387 p h) (derived73542 p h) (h 24642)

theorem derived79488 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 4972) :=
  ElevenRUP.step79488 (p 3016) (p 4971) (p 4972) (derived73858 p h) (h 8275)

theorem derived79489 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 4973) :=
  ElevenRUP.step79489 (p 3016) (p 4971) (p 4973) (derived73858 p h) (h 8276)

theorem derived79490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3920) ∨ (p 2363) ∨ (¬ p 4973) ∨ (¬ p 3875) ∨ (p 2668) ∨ (¬ p 2528) :=
  ElevenRUP.step79490 (p 2363) (p 2528) (p 2668) (p 3324) (p 3875) (p 3920) (p 4347) (p 4973) (derived73560 p h) (derived73386 p h) (derived41465 p h)

theorem derived79491 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3192) ∨ (¬ p 3276) ∨ (p 2911) ∨ (¬ p 4668) :=
  ElevenRUP.step79491 (p 2761) (p 2911) (p 3192) (p 3276) (p 3644) (p 4381) (p 4668) (derived73574 p h) (derived73434 p h) (derived49641 p h)

theorem derived79494 (p : Nat → Prop) (h : Inputs p) :
    (p 4445) ∨ (p 2459) :=
  ElevenRUP.step79494 (p 2459) (p 4445) (p 4665) (derived73696 p h) (h 7480)

theorem derived79495 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 4666) :=
  ElevenRUP.step79495 (p 2459) (p 4665) (p 4666) (derived73696 p h) (h 7482)

theorem derived79496 (p : Nat → Prop) (h : Inputs p) :
    (p 3950) ∨ (p 2459) :=
  ElevenRUP.step79496 (p 2459) (p 3950) (p 4665) (derived73696 p h) (h 7483)

theorem derived79502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3125) ∨ (¬ p 3016) ∨ (¬ p 2440) :=
  ElevenRUP.step79502 (p 2440) (p 3016) (p 3125) (p 3564) (p 3744) (derived73454 p h) (derived43023 p h)

theorem derived79503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3125) ∨ (¬ p 3096) :=
  ElevenRUP.step79503 (p 3096) (p 3125) (p 3564) (p 3744) (derived73454 p h) (h 26007)

theorem derived79506 (p : Nat → Prop) (h : Inputs p) :
    (p 4604) ∨ (¬ p 3564) ∨ (p 2363) :=
  ElevenRUP.step79506 (p 2363) (p 3564) (p 4347) (p 4604) (derived73560 p h) (derived50033 p h)

theorem derived79507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3125) ∨ (p 2553) ∨ (p 2284) ∨ (¬ p 4700) :=
  ElevenRUP.step79507 (p 2284) (p 2553) (p 2588) (p 3125) (p 3564) (p 3744) (p 3952) (p 4700) (derived73454 p h) (derived73282 p h) (derived73496 p h) (derived48612 p h)

theorem derived79512 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (¬ p 3564) ∨ (p 2553) ∨ (¬ p 4033) ∨ (¬ p 2284) :=
  ElevenRUP.step79512 (p 2284) (p 2553) (p 2588) (p 3115) (p 3564) (p 4033) (p 4208) (derived73534 p h) (derived73282 p h) (derived45372 p h)

theorem derived79515 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3096) ∨ (¬ p 3564) ∨ (p 2274) :=
  ElevenRUP.step79515 (p 2274) (p 2761) (p 3096) (p 3097) (p 3461) (p 3564) (p 4381) (derived73574 p h) (derived73352 p h) (derived44361 p h)

theorem derived79517 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2264) ∨ (¬ p 3581) ∨ (¬ p 3564) ∨ (¬ p 2807) :=
  ElevenRUP.step79517 (p 2264) (p 2807) (p 2911) (p 3564) (p 3581) (p 3644) (derived73434 p h) (derived59106 p h)

theorem derived79518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 4623) ∨ (p 2274) ∨ (¬ p 3096) ∨ (p 2449) :=
  ElevenRUP.step79518 (p 2274) (p 2449) (p 3096) (p 3097) (p 3564) (p 3947) (p 4623) (derived73352 p h) (derived73494 p h) (derived71430 p h)

theorem derived79519 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3323) ∨ (p 2553) ∨ (¬ p 2274) ∨ (¬ p 4564) :=
  ElevenRUP.step79519 (p 2274) (p 2553) (p 2588) (p 3323) (p 3564) (p 4037) (p 4564) (derived73508 p h) (derived73282 p h) (derived41594 p h)

theorem derived79520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 3461) ∨ (p 2553) ∨ (¬ p 2274) :=
  ElevenRUP.step79520 (p 2274) (p 2553) (p 2588) (p 3461) (p 3564) (derived73282 p h) (derived46319 p h)

theorem derived79521 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2774) ∨ (¬ p 2911) ∨ (¬ p 2363) ∨ (¬ p 3759) ∨ (¬ p 4503) ∨ (¬ p 3367) ∨ (¬ p 3389) ∨ (¬ p 4078) :=
  ElevenRUP.step79521 (p 2363) (p 2774) (p 2780) (p 2911) (p 3367) (p 3389) (p 3609) (p 3759) (p 4078) (p 4340) (p 4503) (p 4734) (derived73558 p h) (derived73308 p h) (derived72735 p h) (derived54283 p h)

theorem derived79523 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3266) ∨ (p 3343) ∨ (p 2440) :=
  ElevenRUP.step79523 (p 2440) (p 2542) (p 3266) (p 3276) (p 3343) (p 3359) (p 4425) (derived73578 p h) (derived73388 p h) (derived73270 p h) (derived45506 p h)

theorem derived79525 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3266) ∨ (p 3343) ∨ (p 2630) :=
  ElevenRUP.step79525 (p 2630) (p 2810) (p 3266) (p 3276) (p 3343) (p 3359) (p 4425) (derived73578 p h) (derived73388 p h) (derived73316 p h) (derived43620 p h)

theorem derived79526 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 2761) ∨ (¬ p 2662) ∨ (¬ p 3346) ∨ (p 2727) :=
  ElevenRUP.step79526 (p 2662) (p 2727) (p 2761) (p 3276) (p 3346) (p 4111) (p 4425) (derived73578 p h) (derived73518 p h) (derived48489 p h)

theorem derived79527 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3266) ∨ (¬ p 2662) ∨ (¬ p 3346) ∨ (p 2727) :=
  ElevenRUP.step79527 (p 2662) (p 2727) (p 3266) (p 3276) (p 3346) (p 4111) (p 4425) (derived73578 p h) (derived73518 p h) (derived60287 p h)

theorem derived79531 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 3343) ∨ (¬ p 3461) ∨ (¬ p 3016) :=
  ElevenRUP.step79531 (p 3016) (p 3276) (p 3343) (p 3359) (p 3461) (p 4425) (derived73578 p h) (derived73388 p h) (derived54914 p h)

theorem derived79533 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 4171) ∨ (¬ p 2459) ∨ (¬ p 4045) ∨ (¬ p 3461) ∨ (¬ p 4420) :=
  ElevenRUP.step79533 (p 2459) (p 3276) (p 3461) (p 4045) (p 4171) (p 4420) (p 4425) (derived73578 p h) (derived58566 p h)

theorem derived79534 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3266) ∨ (¬ p 4695) :=
  ElevenRUP.step79534 (p 3266) (p 3276) (p 4425) (p 4695) (derived73578 p h) (h 19888)

theorem derived79536 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 2761) ∨ (¬ p 4621) ∨ (¬ p 2797) ∨ (¬ p 2696) ∨ (¬ p 3323) ∨ (¬ p 3346) ∨ (¬ p 4729) :=
  ElevenRUP.step79536 (p 2696) (p 2761) (p 2797) (p 3276) (p 3323) (p 3346) (p 4425) (p 4621) (p 4729) (derived73578 p h) (derived50587 p h)

theorem derived79537 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3483) ∨ (¬ p 5193) ∨ (¬ p 4621) ∨ (¬ p 2608) ∨ (¬ p 3346) ∨ (¬ p 2761) ∨ (¬ p 2829) :=
  ElevenRUP.step79537 (p 2608) (p 2761) (p 2829) (p 3276) (p 3346) (p 3483) (p 4425) (p 4621) (p 5193) (derived73578 p h) (derived63691 p h)

theorem derived79538 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 2761) ∨ (¬ p 4635) ∨ (¬ p 3246) ∨ (¬ p 4277) :=
  ElevenRUP.step79538 (p 2761) (p 3246) (p 3276) (p 4277) (p 4425) (p 4635) (derived73578 p h) (derived55997 p h)

theorem derived79539 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3461) ∨ (¬ p 3323) ∨ (¬ p 3746) ∨ (¬ p 4976) :=
  ElevenRUP.step79539 (p 3276) (p 3323) (p 3461) (p 3746) (p 4425) (p 4976) (derived73578 p h) (derived41824 p h)

theorem derived79540 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 4045) ∨ (¬ p 3266) ∨ (¬ p 2484) ∨ (¬ p 2088) :=
  ElevenRUP.step79540 (p 2088) (p 2484) (p 3266) (p 3276) (p 4045) (p 4425) (derived73578 p h) (derived54793 p h)

theorem derived79543 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3125) ∨ (¬ p 2132) ∨ (¬ p 4330) ∨ (¬ p 4729) ∨ (¬ p 2860) ∨ (¬ p 3346) ∨ (¬ p 3266) :=
  ElevenRUP.step79543 (p 2132) (p 2860) (p 3125) (p 3266) (p 3276) (p 3346) (p 4330) (p 4425) (p 4729) (derived73578 p h) (derived50976 p h)

theorem derived79545 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 4451) ∨ (¬ p 2761) :=
  ElevenRUP.step79545 (p 2761) (p 3276) (p 4425) (p 4451) (derived73578 p h) (h 37717)

theorem derived79548 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3461) ∨ (¬ p 4620) ∨ (¬ p 2553) ∨ (¬ p 3746) :=
  ElevenRUP.step79548 (p 2553) (p 3276) (p 3461) (p 3746) (p 4425) (p 4620) (derived73578 p h) (derived42566 p h)

theorem derived79555 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 4066) ∨ (¬ p 2761) ∨ (¬ p 4653) ∨ (¬ p 3516) ∨ (¬ p 4635) :=
  ElevenRUP.step79555 (p 2761) (p 3276) (p 3516) (p 4066) (p 4425) (p 4635) (p 4653) (derived73578 p h) (derived55466 p h)

theorem derived79558 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 5122) :=
  ElevenRUP.step79558 (p 3266) (p 4444) (p 5122) (derived73580 p h) (derived47325 p h)

theorem derived79560 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3276) ∨ (¬ p 4438) ∨ (¬ p 3358) ∨ (p 2459) :=
  ElevenRUP.step79560 (p 2459) (p 3266) (p 3276) (p 3358) (p 4348) (p 4438) (p 4444) (derived73580 p h) (derived73562 p h) (derived40942 p h)

theorem derived79563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 3266) ∨ (¬ p 5190) ∨ (p 3125) ∨ (p 2210) ∨ (p 2192) ∨ (¬ p 3355) ∨ (¬ p 4604) :=
  ElevenRUP.step79563 (p 2192) (p 2210) (p 3125) (p 3266) (p 3276) (p 3355) (p 3555) (p 3744) (p 4173) (p 4444) (p 4604) (p 5190) (derived73580 p h) (derived73454 p h) (derived73412 p h) (derived73528 p h) (derived56280 p h)

theorem derived79565 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2528) ∨ (¬ p 3363) ∨ (p 3367) ∨ (p 2470) :=
  ElevenRUP.step79565 (p 2470) (p 2476) (p 2528) (p 2534) (p 3266) (p 3363) (p 3367) (p 3585) (p 4444) (derived73580 p h) (derived73268 p h) (derived73428 p h) (derived73250 p h) (derived45221 p h)

theorem derived79569 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3276) ∨ (¬ p 3358) ∨ (p 3146) ∨ (¬ p 4434) :=
  ElevenRUP.step79569 (p 3146) (p 3266) (p 3276) (p 3358) (p 3692) (p 4434) (p 4444) (derived73580 p h) (derived73448 p h) (derived41672 p h)

theorem derived79572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 3266) ∨ (¬ p 4636) ∨ (p 3146) ∨ (¬ p 3945) ∨ (¬ p 4902) :=
  ElevenRUP.step79572 (p 3146) (p 3266) (p 3276) (p 3692) (p 3945) (p 4444) (p 4636) (p 4902) (derived73580 p h) (derived73448 p h) (derived48625 p h)

theorem derived79573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 3266) ∨ (p 3379) ∨ (p 2528) :=
  ElevenRUP.step79573 (p 2509) (p 2528) (p 2534) (p 3266) (p 3379) (p 3452) (p 4444) (derived73580 p h) (derived73394 p h) (derived73268 p h) (derived42722 p h)

theorem derived79574 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3266) ∨ (p 2651) ∨ (p 3083) :=
  ElevenRUP.step79574 (p 2528) (p 2534) (p 2651) (p 2657) (p 3083) (p 3266) (p 4256) (p 4444) (derived73268 p h) (derived73580 p h) (derived73288 p h) (derived73542 p h) (derived45455 p h)

theorem derived79577 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (p 2528) ∨ (p 2470) ∨ (¬ p 2662) ∨ (p 3266) :=
  ElevenRUP.step79577 (p 2470) (p 2476) (p 2528) (p 2534) (p 2662) (p 2727) (p 3266) (p 4111) (p 4444) (derived73518 p h) (derived73268 p h) (derived73250 p h) (derived73580 p h) (derived43621 p h)

theorem derived79578 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2528) ∨ (p 2470) ∨ (p 2630) ∨ (¬ p 2662) :=
  ElevenRUP.step79578 (p 2470) (p 2476) (p 2528) (p 2534) (p 2630) (p 2662) (p 2810) (p 3266) (p 4444) (derived73580 p h) (derived73268 p h) (derived73250 p h) (derived73316 p h) (derived56771 p h)

theorem derived79580 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2761) ∨ (¬ p 3945) ∨ (¬ p 4420) ∨ (p 2528) :=
  ElevenRUP.step79580 (p 2528) (p 2534) (p 2761) (p 3266) (p 3945) (p 4420) (p 4444) (derived73580 p h) (derived73268 p h) (derived62932 p h)

theorem derived79588 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3266) ∨ (¬ p 4826) ∨ (p 2470) ∨ (¬ p 5193) ∨ (¬ p 3931) ∨ (¬ p 2241) ∨ (p 2996) :=
  ElevenRUP.step79588 (p 2241) (p 2470) (p 2476) (p 2528) (p 2534) (p 2996) (p 3027) (p 3266) (p 3931) (p 4444) (p 4826) (p 5193) (derived73268 p h) (derived73580 p h) (derived73250 p h) (derived73340 p h) (derived50289 p h)

theorem derived79591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4075) ∨ (p 3266) ∨ (p 2608) ∨ (¬ p 4826) ∨ (¬ p 3347) ∨ (p 2528) ∨ (p 2470) ∨ (¬ p 3399) :=
  ElevenRUP.step79591 (p 2470) (p 2476) (p 2528) (p 2534) (p 2608) (p 3266) (p 3347) (p 3399) (p 3954) (p 4075) (p 4444) (p 4826) (derived73580 p h) (derived73498 p h) (derived73268 p h) (derived73250 p h) (derived71432 p h)

theorem derived79595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (p 3266) ∨ (¬ p 4826) ∨ (p 2470) ∨ (p 2528) ∨ (¬ p 2870) ∨ (¬ p 4729) ∨ (¬ p 2132) :=
  ElevenRUP.step79595 (p 2132) (p 2470) (p 2476) (p 2528) (p 2534) (p 2870) (p 3266) (p 4129) (p 4444) (p 4729) (p 4826) (derived73580 p h) (derived73250 p h) (derived73268 p h) (derived62891 p h)

theorem derived79598 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 4418) ∨ (¬ p 2608) ∨ (¬ p 5059) ∨ (p 2210) ∨ (¬ p 3355) ∨ (¬ p 4376) ∨ (¬ p 3519) ∨ (p 3105) ∨ (¬ p 3276) :=
  ElevenRUP.step79598 (p 2210) (p 2608) (p 3105) (p 3266) (p 3276) (p 3355) (p 3519) (p 3555) (p 4376) (p 4385) (p 4418) (p 4444) (p 5059) (derived73580 p h) (derived73412 p h) (derived73576 p h) (derived56221 p h)

theorem derived79599 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2528) ∨ (¬ p 3177) ∨ (¬ p 2475) ∨ (¬ p 2630) ∨ (p 3005) :=
  ElevenRUP.step79599 (p 2475) (p 2528) (p 2534) (p 2630) (p 3005) (p 3177) (p 3266) (p 3877) (p 4444) (derived73580 p h) (derived73268 p h) (derived73488 p h) (derived45369 p h)

theorem derived79600 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2528) ∨ (p 2470) ∨ (¬ p 2230) :=
  ElevenRUP.step79600 (p 2230) (p 2470) (p 2476) (p 2528) (p 2534) (p 3266) (p 4444) (derived73580 p h) (derived73268 p h) (derived73250 p h) (derived44590 p h)

theorem derived79605 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3276) ∨ (p 2363) ∨ (¬ p 3358) ∨ (¬ p 4384) :=
  ElevenRUP.step79605 (p 2363) (p 3266) (p 3276) (p 3358) (p 4347) (p 4384) (p 4444) (derived73580 p h) (derived73560 p h) (derived48488 p h)

theorem derived79606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3888) ∨ (p 3266) ∨ (¬ p 5250) ∨ (¬ p 3366) ∨ (p 2459) ∨ (¬ p 2744) ∨ (¬ p 3820) ∨ (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (p 2341) :=
  ElevenRUP.step79606 (p 2246) (p 2341) (p 2459) (p 2651) (p 2744) (p 3016) (p 3266) (p 3366) (p 3551) (p 3820) (p 3888) (p 4348) (p 4444) (p 5250) (derived73580 p h) (derived73562 p h) (derived73408 p h) (derived64141 p h)

theorem derived79608 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3266) ∨ (p 3641) ∨ (p 2598) :=
  ElevenRUP.step79608 (p 2528) (p 2534) (p 2598) (p 3055) (p 3266) (p 3641) (p 3874) (p 4444) (derived73268 p h) (derived73580 p h) (derived73484 p h) (derived73350 p h) (derived46543 p h)

theorem derived79610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4171) ∨ (p 3266) ∨ (¬ p 3461) :=
  ElevenRUP.step79610 (p 3266) (p 3461) (p 4171) (p 4444) (derived73580 p h) (h 9696)

theorem derived79611 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2761) ∨ (p 2363) ∨ (¬ p 3945) ∨ (¬ p 4133) :=
  ElevenRUP.step79611 (p 2363) (p 2761) (p 3266) (p 3945) (p 4133) (p 4347) (p 4444) (derived73580 p h) (derived73560 p h) (derived41811 p h)

theorem derived79612 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2363) ∨ (p 3016) ∨ (p 2352) :=
  ElevenRUP.step79612 (p 2352) (p 2363) (p 3016) (p 3266) (p 3574) (p 3956) (p 4347) (p 4444) (derived73580 p h) (derived73560 p h) (derived73422 p h) (derived73500 p h) (derived47534 p h)

theorem derived79613 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 2493) ∨ (p 2352) ∨ (p 2363) :=
  ElevenRUP.step79613 (p 2352) (p 2363) (p 2493) (p 2499) (p 3266) (p 3956) (p 4347) (p 4444) (derived73580 p h) (derived73260 p h) (derived73500 p h) (derived73560 p h) (derived42869 p h)

theorem derived79615 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 3266) ∨ (p 3389) ∨ (p 2459) :=
  ElevenRUP.step79615 (p 2459) (p 2911) (p 3266) (p 3389) (p 3540) (p 3644) (p 4348) (p 4444) (derived73434 p h) (derived73580 p h) (derived73402 p h) (derived73562 p h) (derived44532 p h)

theorem derived79616 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 3146) ∨ (p 2437) ∨ (¬ p 4042) ∨ (¬ p 4279) ∨ (p 2341) :=
  ElevenRUP.step79616 (p 2341) (p 2437) (p 3146) (p 3266) (p 3551) (p 3692) (p 3742) (p 4042) (p 4279) (p 4444) (derived73580 p h) (derived73448 p h) (derived73452 p h) (derived73408 p h) (derived45566 p h)

theorem derived79617 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 4445) ∨ (¬ p 2761) :=
  ElevenRUP.step79617 (p 2761) (p 3266) (p 4381) (p 4444) (p 4445) (derived73580 p h) (derived73573 p h) (h 23297)

theorem derived79619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3266) ∨ (¬ p 2761) ∨ (p 2177) :=
  ElevenRUP.step79619 (p 2177) (p 2299) (p 2396) (p 2761) (p 3266) (p 4444) (derived73580 p h) (derived73234 p h) (derived45071 p h)

theorem derived79622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (p 3266) ∨ (¬ p 3246) ∨ (¬ p 3051) :=
  ElevenRUP.step79622 (p 2761) (p 3051) (p 3246) (p 3266) (p 4444) (derived73580 p h) (derived46728 p h)

theorem derived79625 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2819) ∨ (¬ p 2774) ∨ (¬ p 3990) ∨ (¬ p 3461) :=
  ElevenRUP.step79625 (p 2774) (p 2819) (p 3266) (p 3461) (p 3990) (p 4444) (derived73580 p h) (derived46818 p h)

theorem derived79626 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (p 2668) ∨ (¬ p 3323) :=
  ElevenRUP.step79626 (p 2668) (p 3266) (p 3323) (p 3324) (p 3461) (p 4444) (derived73580 p h) (derived73386 p h) (derived65266 p h)

theorem derived79627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 3266) ∨ (¬ p 2331) ∨ (¬ p 3323) :=
  ElevenRUP.step79627 (p 2331) (p 3266) (p 3323) (p 3461) (p 4444) (derived73580 p h) (derived55618 p h)

theorem derived79630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 3266) ∨ (¬ p 3654) ∨ (¬ p 3461) ∨ (¬ p 2797) :=
  ElevenRUP.step79630 (p 2797) (p 3266) (p 3461) (p 3567) (p 3654) (p 4444) (derived73580 p h) (derived60726 p h)

theorem derived79633 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 4138) ∨ (p 3266) ∨ (¬ p 2274) ∨ (p 2187) :=
  ElevenRUP.step79633 (p 2187) (p 2274) (p 2459) (p 3266) (p 3989) (p 4138) (p 4348) (p 4444) (derived73562 p h) (derived73580 p h) (derived73502 p h) (derived43274 p h)

theorem derived79634 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3125) ∨ (¬ p 2192) :=
  ElevenRUP.step79634 (p 2192) (p 3125) (p 3266) (p 3461) (p 4444) (derived73580 p h) (derived45720 p h)

theorem derived79637 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (p 2553) :=
  ElevenRUP.step79637 (p 2553) (p 2588) (p 3266) (p 3461) (p 3564) (p 4444) (derived73580 p h) (derived73282 p h) (derived63625 p h)

theorem derived79638 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 2573) :=
  ElevenRUP.step79638 (p 2573) (p 3266) (p 3461) (p 3564) (p 4444) (derived73580 p h) (derived46966 p h)

theorem derived79639 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (p 2187) ∨ (¬ p 3096) :=
  ElevenRUP.step79639 (p 2187) (p 3096) (p 3266) (p 3461) (p 3564) (p 3989) (p 4444) (derived73580 p h) (derived73502 p h) (derived43556 p h)

theorem derived79640 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2761) ∨ (¬ p 4604) ∨ (p 2641) ∨ (¬ p 3516) ∨ (p 2241) ∨ (¬ p 4988) ∨ (¬ p 4521) ∨ (p 3323) :=
  ElevenRUP.step79640 (p 2241) (p 2247) (p 2641) (p 2761) (p 3266) (p 3323) (p 3516) (p 4037) (p 4154) (p 4444) (p 4521) (p 4604) (p 4988) (derived73580 p h) (derived73526 p h) (derived73226 p h) (derived73508 p h) (derived51795 p h)

theorem derived79643 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3516) ∨ (p 3564) ∨ (¬ p 2761) ∨ (p 3422) ∨ (¬ p 2139) ∨ (p 2598) ∨ (¬ p 4988) ∨ (¬ p 4604) :=
  ElevenRUP.step79643 (p 2139) (p 2598) (p 2761) (p 3055) (p 3266) (p 3422) (p 3516) (p 3564) (p 3584) (p 4137) (p 4444) (p 4604) (p 4988) (derived73580 p h) (derived73524 p h) (derived73426 p h) (derived73350 p h) (derived56204 p h)

theorem derived79649 (p : Nat → Prop) (h : Inputs p) :
    (p 2509) ∨ (p 2573) ∨ (¬ p 3573) ∨ (¬ p 3347) :=
  ElevenRUP.step79649 (p 2509) (p 2573) (p 2579) (p 3347) (p 3573) (derived73274 p h) (h 24508)

theorem derived79654 (p : Nat → Prop) (h : Inputs p) :
    (p 2509) ∨ (¬ p 4116) ∨ (p 3083) :=
  ElevenRUP.step79654 (p 2509) (p 3083) (p 4116) (p 4256) (derived73542 p h) (h 39385)

theorem derived79655 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 5194) :=
  ElevenRUP.step79655 (p 3379) (p 3452) (p 5194) (derived73394 p h) (derived48298 p h)

theorem derived79656 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 5193) :=
  ElevenRUP.step79656 (p 3379) (p 3452) (p 5193) (derived73394 p h) (derived48331 p h)

theorem derived79657 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2608) ∨ (p 2406) ∨ (p 2427) :=
  ElevenRUP.step79657 (p 2406) (p 2427) (p 2608) (p 3238) (p 3379) (p 3452) (p 4235) (derived73394 p h) (derived73374 p h) (derived73536 p h) (derived54231 p h)

theorem derived79658 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2417) ∨ (¬ p 2608) ∨ (p 3379) :=
  ElevenRUP.step79658 (p 2417) (p 2608) (p 2922) (p 2928) (p 3379) (p 3452) (p 4278) (derived73320 p h) (derived73546 p h) (derived73394 p h) (derived43510 p h)

theorem derived79659 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2373) ∨ (¬ p 2608) ∨ (p 2406) :=
  ElevenRUP.step79659 (p 2373) (p 2406) (p 2608) (p 3238) (p 3379) (p 3452) (p 3880) (derived73394 p h) (derived73490 p h) (derived73374 p h) (derived44011 p h)

theorem derived79661 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (¬ p 2608) ∨ (p 3564) :=
  ElevenRUP.step79661 (p 2493) (p 2499) (p 2608) (p 3379) (p 3452) (p 3564) (p 4137) (derived73260 p h) (derived73394 p h) (derived73524 p h) (derived44435 p h)

theorem derived79663 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2608) ∨ (p 2406) ∨ (p 2440) :=
  ElevenRUP.step79663 (p 2406) (p 2440) (p 2542) (p 2608) (p 3238) (p 3379) (p 3452) (derived73394 p h) (derived73374 p h) (derived73270 p h) (derived44858 p h)

theorem derived79664 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2608) ∨ (p 2563) ∨ (p 2406) :=
  ElevenRUP.step79664 (p 2406) (p 2563) (p 2608) (p 3238) (p 3379) (p 3452) (p 4110) (derived73394 p h) (derived73516 p h) (derived73374 p h) (derived60078 p h)

theorem derived79668 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (¬ p 2608) ∨ (¬ p 3016) :=
  ElevenRUP.step79668 (p 2493) (p 2499) (p 2608) (p 3016) (p 3379) (p 3452) (derived73260 p h) (derived73394 p h) (derived45480 p h)

theorem derived79669 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (¬ p 2608) ∨ (¬ p 3422) :=
  ElevenRUP.step79669 (p 2493) (p 2499) (p 2608) (p 3379) (p 3422) (p 3452) (derived73260 p h) (derived73394 p h) (derived45490 p h)

theorem derived79670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 3379) ∨ (p 2922) ∨ (p 2911) :=
  ElevenRUP.step79670 (p 2608) (p 2911) (p 2922) (p 2928) (p 3379) (p 3452) (p 3644) (derived73394 p h) (derived73320 p h) (derived73434 p h) (derived46669 p h)

theorem derived79671 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 3379) ∨ (p 2528) ∨ (¬ p 2608) :=
  ElevenRUP.step79671 (p 2509) (p 2528) (p 2534) (p 2608) (p 3379) (p 3452) (derived73394 p h) (derived73268 p h) (derived50384 p h)

theorem derived79676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 3016) ∨ (p 2493) :=
  ElevenRUP.step79676 (p 2241) (p 2493) (p 2499) (p 3016) (p 3379) (p 3452) (derived73394 p h) (derived73260 p h) (derived45472 p h)

theorem derived79679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 2608) ∨ (¬ p 2459) ∨ (p 3379) ∨ (¬ p 3370) ∨ (¬ p 4377) ∨ (¬ p 4697) ∨ (¬ p 3193) :=
  ElevenRUP.step79679 (p 2459) (p 2608) (p 2881) (p 3051) (p 3193) (p 3370) (p 3379) (p 3452) (p 4377) (p 4697) (derived73394 p h) (derived60986 p h)

theorem derived79690 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 3379) ∨ (¬ p 2210) ∨ (¬ p 2192) :=
  ElevenRUP.step79690 (p 2192) (p 2210) (p 2274) (p 3379) (p 3452) (derived73394 p h) (derived64916 p h)

theorem derived79692 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 2881) :=
  ElevenRUP.step79692 (p 2210) (p 2881) (p 2891) (p 3379) (p 3452) (derived73394 p h) (derived64952 p h)

theorem derived79693 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3246) :=
  ElevenRUP.step79693 (p 2210) (p 2891) (p 3246) (p 3379) (p 3452) (derived73394 p h) (derived47940 p h)

theorem derived79695 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (¬ p 2608) ∨ (p 2352) :=
  ElevenRUP.step79695 (p 2352) (p 2493) (p 2499) (p 2608) (p 3379) (p 3452) (p 3956) (derived73260 p h) (derived73394 p h) (derived73500 p h) (derived44198 p h)

theorem derived79696 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2493) ∨ (¬ p 2210) ∨ (¬ p 4715) ∨ (¬ p 4210) :=
  ElevenRUP.step79696 (p 2210) (p 2493) (p 2499) (p 3379) (p 3452) (p 4210) (p 4715) (derived73394 p h) (derived73260 p h) (derived50881 p h)

theorem derived79699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (p 3379) ∨ (¬ p 2210) ∨ (¬ p 2166) :=
  ElevenRUP.step79699 (p 2166) (p 2210) (p 3146) (p 3379) (p 3452) (derived73394 p h) (derived47099 p h)

theorem derived79704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4210) ∨ (p 3379) ∨ (¬ p 2509) ∨ (¬ p 4608) ∨ (¬ p 2210) :=
  ElevenRUP.step79704 (p 2210) (p 2509) (p 3379) (p 3452) (p 4210) (p 4608) (derived73394 p h) (derived42196 p h)

theorem derived79705 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 4210) ∨ (¬ p 2440) ∨ (¬ p 4814) ∨ (¬ p 2210) :=
  ElevenRUP.step79705 (p 2210) (p 2440) (p 3379) (p 3452) (p 4210) (p 4814) (derived73394 p h) (derived50092 p h)

theorem derived79708 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (p 2850) ∨ (¬ p 4210) ∨ (¬ p 5217) :=
  ElevenRUP.step79708 (p 2210) (p 2850) (p 3379) (p 3452) (p 3684) (p 4210) (p 5217) (derived73394 p h) (derived73442 p h) (derived40961 p h)

theorem derived79709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4210) ∨ (¬ p 2210) ∨ (¬ p 2881) ∨ (p 3379) ∨ (¬ p 2427) :=
  ElevenRUP.step79709 (p 2210) (p 2427) (p 2881) (p 3379) (p 3452) (p 4210) (derived73394 p h) (derived64885 p h)

theorem derived79710 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2922) ∨ (¬ p 4210) ∨ (¬ p 4644) ∨ (¬ p 2210) :=
  ElevenRUP.step79710 (p 2210) (p 2922) (p 2928) (p 3379) (p 3452) (p 4210) (p 4644) (derived73394 p h) (derived73320 p h) (derived50884 p h)

theorem derived79717 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 3680) ∨ (¬ p 4210) ∨ (¬ p 2210) ∨ (p 3379) :=
  ElevenRUP.step79717 (p 2210) (p 2982) (p 3379) (p 3452) (p 3680) (p 4210) (derived73394 p h) (derived64963 p h)

theorem derived79723 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3590) ∨ (p 3422) ∨ (¬ p 2210) ∨ (¬ p 4241) ∨ (¬ p 4715) ∨ (¬ p 4282) :=
  ElevenRUP.step79723 (p 2210) (p 3379) (p 3422) (p 3452) (p 3584) (p 3590) (p 4241) (p 4282) (p 4715) (derived73394 p h) (derived73426 p h) (derived50354 p h)

theorem derived79725 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2264) ∨ (p 2922) ∨ (¬ p 2696) ∨ (p 3379) ∨ (¬ p 2685) ∨ (¬ p 4733) ∨ (¬ p 4666) :=
  ElevenRUP.step79725 (p 2264) (p 2417) (p 2685) (p 2696) (p 2922) (p 2928) (p 3379) (p 3452) (p 4278) (p 4666) (p 4733) (derived73546 p h) (derived73320 p h) (derived73394 p h) (derived49997 p h)

theorem derived79732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 4116) ∨ (¬ p 4652) ∨ (p 2996) :=
  ElevenRUP.step79732 (p 2241) (p 2996) (p 3027) (p 3379) (p 3452) (p 4116) (p 4652) (derived73394 p h) (derived73340 p h) (derived42612 p h)

theorem derived79733 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 2641) ∨ (¬ p 4116) ∨ (¬ p 4975) :=
  ElevenRUP.step79733 (p 2241) (p 2641) (p 3379) (p 3452) (p 4116) (p 4975) (derived73394 p h) (derived41386 p h)

theorem derived79743 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 4116) ∨ (¬ p 2745) ∨ (¬ p 2630) :=
  ElevenRUP.step79743 (p 2241) (p 2630) (p 2745) (p 3379) (p 3452) (p 4116) (derived73394 p h) (derived41384 p h)

theorem derived79744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (p 2406) ∨ (p 2440) :=
  ElevenRUP.step79744 (p 2241) (p 2406) (p 2440) (p 2542) (p 3238) (p 3379) (p 3452) (derived73394 p h) (derived73374 p h) (derived73270 p h) (derived44854 p h)

theorem derived79748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 2992) ∨ (¬ p 4116) :=
  ElevenRUP.step79748 (p 2241) (p 2992) (p 3379) (p 3452) (p 4116) (p 4704) (derived73394 p h) (derived73046 p h) (derived41317 p h)

theorem derived79749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 3379) ∨ (¬ p 2241) ∨ (p 2528) :=
  ElevenRUP.step79749 (p 2241) (p 2509) (p 2528) (p 2534) (p 3379) (p 3452) (derived73394 p h) (derived73268 p h) (derived47793 p h)

theorem derived79750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 3379) ∨ (¬ p 2696) ∨ (¬ p 2509) ∨ (¬ p 2685) ∨ (¬ p 3950) ∨ (p 2528) ∨ (¬ p 4733) :=
  ElevenRUP.step79750 (p 2449) (p 2509) (p 2528) (p 2534) (p 2685) (p 2696) (p 3379) (p 3452) (p 3950) (p 4733) (derived73394 p h) (derived73268 p h) (derived49800 p h)

theorem derived79753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (p 3276) ∨ (¬ p 2241) ∨ (p 3379) :=
  ElevenRUP.step79753 (p 2241) (p 3193) (p 3276) (p 3379) (p 3452) (p 4425) (derived73578 p h) (derived73394 p h) (derived65274 p h)

theorem derived79755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 3189) ∨ (¬ p 4116) ∨ (¬ p 5011) :=
  ElevenRUP.step79755 (p 2241) (p 3189) (p 3379) (p 3452) (p 4116) (p 5011) (derived73394 p h) (derived42231 p h)

theorem derived79756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 4116) ∨ (¬ p 3842) ∨ (¬ p 5177) :=
  ElevenRUP.step79756 (p 2241) (p 3379) (p 3452) (p 3842) (p 4116) (p 5177) (derived73394 p h) (derived42233 p h)

theorem derived79757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 2363) ∨ (¬ p 3399) ∨ (¬ p 4236) ∨ (¬ p 3366) ∨ (¬ p 3950) ∨ (p 2331) ∨ (p 3379) ∨ (¬ p 4376) ∨ (p 2668) :=
  ElevenRUP.step79757 (p 2331) (p 2363) (p 2668) (p 2963) (p 3324) (p 3366) (p 3379) (p 3399) (p 3452) (p 3631) (p 3950) (p 4236) (p 4347) (p 4376) (derived73560 p h) (derived73338 p h) (derived73394 p h) (derived73386 p h) (derived53525 p h)

theorem derived79760 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2098) ∨ (¬ p 3741) ∨ (p 2373) ∨ (p 3379) ∨ (¬ p 4733) ∨ (¬ p 4134) ∨ (¬ p 3609) ∨ (p 2922) :=
  ElevenRUP.step79760 (p 2098) (p 2363) (p 2373) (p 2922) (p 2928) (p 3379) (p 3452) (p 3609) (p 3741) (p 3880) (p 4134) (p 4347) (p 4733) (derived73560 p h) (derived73490 p h) (derived73394 p h) (derived73320 p h) (derived49781 p h)

theorem derived79764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3093) ∨ (p 3379) ∨ (¬ p 2177) :=
  ElevenRUP.step79764 (p 2177) (p 3093) (p 3309) (p 3379) (p 3452) (derived73394 p h) (derived47943 p h)

theorem derived79765 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2417) ∨ (¬ p 2396) ∨ (p 3379) :=
  ElevenRUP.step79765 (p 2396) (p 2417) (p 2922) (p 2928) (p 3379) (p 3452) (p 4278) (derived73320 p h) (derived73546 p h) (derived73394 p h) (derived44936 p h)

theorem derived79766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2122) ∨ (p 3379) ∨ (¬ p 2774) ∨ (¬ p 4733) ∨ (p 2528) ∨ (¬ p 3950) ∨ (¬ p 2509) :=
  ElevenRUP.step79766 (p 2122) (p 2396) (p 2509) (p 2528) (p 2534) (p 2774) (p 3379) (p 3452) (p 3950) (p 4733) (derived73394 p h) (derived73268 p h) (derived62227 p h)

theorem derived79770 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 2922) ∨ (p 3379) ∨ (¬ p 3246) :=
  ElevenRUP.step79770 (p 2417) (p 2922) (p 2928) (p 3246) (p 3379) (p 3452) (p 4278) (derived73546 p h) (derived73320 p h) (derived73394 p h) (derived45547 p h)

theorem derived79771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2493) ∨ (p 2553) ∨ (¬ p 2248) ∨ (p 3379) ∨ (¬ p 2946) ∨ (¬ p 4405) ∨ (¬ p 2187) :=
  ElevenRUP.step79771 (p 2187) (p 2248) (p 2284) (p 2493) (p 2499) (p 2553) (p 2588) (p 2946) (p 3379) (p 3452) (p 4405) (derived73260 p h) (derived73282 p h) (derived73394 p h) (derived61772 p h)

theorem derived79774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3379) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (p 2406) ∨ (¬ p 5059) ∨ (¬ p 2248) ∨ (p 2982) :=
  ElevenRUP.step79774 (p 2248) (p 2331) (p 2363) (p 2406) (p 2668) (p 2982) (p 3238) (p 3379) (p 3452) (p 4948) (p 5059) (derived73394 p h) (derived73374 p h) (derived73846 p h) (derived48595 p h)

theorem derived79775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2331) ∨ (p 2922) ∨ (¬ p 2363) ∨ (p 2417) ∨ (¬ p 4669) ∨ (p 3379) ∨ (¬ p 2248) :=
  ElevenRUP.step79775 (p 2248) (p 2331) (p 2363) (p 2417) (p 2668) (p 2922) (p 2928) (p 3379) (p 3452) (p 4278) (p 4669) (derived73320 p h) (derived73546 p h) (derived73394 p h) (derived48573 p h)

theorem derived79777 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2509) ∨ (¬ p 5122) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (p 2528) ∨ (¬ p 3979) ∨ (p 3379) :=
  ElevenRUP.step79777 (p 2248) (p 2331) (p 2509) (p 2528) (p 2534) (p 2668) (p 3379) (p 3452) (p 3979) (p 5122) (derived73268 p h) (derived73394 p h) (derived52589 p h)

theorem derived79782 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3379) ∨ (¬ p 3923) :=
  ElevenRUP.step79782 (p 2383) (p 3379) (p 3452) (p 3923) (derived73394 p h) (derived66683 p h)

theorem derived79783 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3848) ∨ (¬ p 2253) ∨ (¬ p 3286) ∨ (¬ p 4376) ∨ (p 3379) ∨ (¬ p 2741) :=
  ElevenRUP.step79783 (p 2253) (p 2741) (p 3286) (p 3379) (p 3452) (p 3848) (p 4376) (derived73394 p h) (derived42232 p h)

theorem derived79785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (¬ p 4521) ∨ (p 2922) ∨ (¬ p 4902) ∨ (p 2911) ∨ (¬ p 2156) ∨ (p 3379) :=
  ElevenRUP.step79785 (p 2156) (p 2284) (p 2911) (p 2922) (p 2928) (p 3156) (p 3379) (p 3452) (p 3644) (p 3952) (p 4521) (p 4902) (derived73496 p h) (derived73320 p h) (derived73434 p h) (derived73394 p h) (derived50428 p h)

theorem derived79789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 3379) ∨ (¬ p 2156) ∨ (p 2563) ∨ (¬ p 4172) :=
  ElevenRUP.step79789 (p 2156) (p 2427) (p 2563) (p 3379) (p 3452) (p 4110) (p 4172) (derived73394 p h) (derived73516 p h) (derived43302 p h)

theorem derived79793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (p 2563) ∨ (p 2406) :=
  ElevenRUP.step79793 (p 2241) (p 2406) (p 2563) (p 3238) (p 3379) (p 3452) (p 4110) (derived73394 p h) (derived73516 p h) (derived73374 p h) (derived43962 p h)

theorem derived79794 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2563) ∨ (p 2187) ∨ (p 2406) :=
  ElevenRUP.step79794 (p 2187) (p 2406) (p 2563) (p 3238) (p 3379) (p 3452) (p 3989) (p 4110) (derived73394 p h) (derived73516 p h) (derived73502 p h) (derived73374 p h) (derived44056 p h)

theorem derived79795 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2563) ∨ (p 2406) ∨ (p 2274) :=
  ElevenRUP.step79795 (p 2274) (p 2406) (p 2563) (p 3097) (p 3238) (p 3379) (p 3452) (p 4110) (derived73394 p h) (derived73516 p h) (derived73374 p h) (derived73352 p h) (derived44031 p h)

theorem derived79797 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (p 2427) :=
  ElevenRUP.step79797 (p 2210) (p 2427) (p 2891) (p 3379) (p 3452) (p 4235) (derived73394 p h) (derived73536 p h) (derived46561 p h)

theorem derived79798 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2427) ∨ (p 2881) ∨ (p 2406) :=
  ElevenRUP.step79798 (p 2406) (p 2427) (p 2881) (p 3238) (p 3379) (p 3452) (p 3570) (p 4235) (derived73394 p h) (derived73536 p h) (derived73418 p h) (derived73374 p h) (derived43892 p h)

theorem derived79800 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 3246) ∨ (p 2427) ∨ (p 2406) :=
  ElevenRUP.step79800 (p 2406) (p 2427) (p 3238) (p 3246) (p 3379) (p 3452) (p 3690) (p 4235) (derived73394 p h) (derived73446 p h) (derived73536 p h) (derived73374 p h) (derived43539 p h)

theorem derived79801 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (p 2177) ∨ (p 2553) :=
  ElevenRUP.step79801 (p 2177) (p 2299) (p 2493) (p 2499) (p 2553) (p 2588) (p 3379) (p 3452) (derived73260 p h) (derived73394 p h) (derived73234 p h) (derived73282 p h) (derived43889 p h)

theorem derived79803 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (p 2553) ∨ (p 2396) :=
  ElevenRUP.step79803 (p 2396) (p 2493) (p 2499) (p 2553) (p 2588) (p 3379) (p 3452) (p 4107) (derived73260 p h) (derived73394 p h) (derived73282 p h) (derived73514 p h) (derived44182 p h)

theorem derived79808 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (p 2553) ∨ (¬ p 2274) :=
  ElevenRUP.step79808 (p 2274) (p 2493) (p 2499) (p 2553) (p 2588) (p 3379) (p 3452) (derived73260 p h) (derived73394 p h) (derived73282 p h) (derived45471 p h)

theorem derived79810 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 3125) ∨ (p 3379) ∨ (p 3564) :=
  ElevenRUP.step79810 (p 2493) (p 2499) (p 3125) (p 3379) (p 3452) (p 3564) (p 4137) (derived73260 p h) (derived73394 p h) (derived73524 p h) (derived44186 p h)

theorem derived79813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5020) ∨ (¬ p 2307) ∨ (¬ p 2506) ∨ (p 3309) ∨ (p 3379) :=
  ElevenRUP.step79813 (p 2307) (p 2506) (p 3309) (p 3379) (p 3452) (p 3549) (p 5020) (derived73406 p h) (derived73394 p h) (derived54036 p h)

theorem derived79816 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (¬ p 3370) ∨ (¬ p 2187) ∨ (¬ p 4384) ∨ (p 3379) ∨ (¬ p 2307) ∨ (¬ p 2509) ∨ (¬ p 2608) ∨ (¬ p 4377) ∨ (¬ p 2962) :=
  ElevenRUP.step79816 (p 2187) (p 2274) (p 2307) (p 2509) (p 2608) (p 2962) (p 3097) (p 3370) (p 3379) (p 3452) (p 4377) (p 4384) (derived73352 p h) (derived73394 p h) (derived52625 p h)

theorem derived79820 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 5207) ∨ (¬ p 2761) ∨ (p 2493) ∨ (p 3266) ∨ (¬ p 3516) ∨ (p 3564) ∨ (¬ p 4604) :=
  ElevenRUP.step79820 (p 2493) (p 2499) (p 2761) (p 3266) (p 3379) (p 3452) (p 3516) (p 3564) (p 4137) (p 4444) (p 4604) (p 5207) (derived73394 p h) (derived73260 p h) (derived73580 p h) (derived73524 p h) (derived51790 p h)

theorem derived79823 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3256) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (p 2406) ∨ (p 2373) ∨ (p 3379) ∨ (¬ p 4134) ∨ (¬ p 4341) :=
  ElevenRUP.step79823 (p 2248) (p 2331) (p 2363) (p 2373) (p 2406) (p 3238) (p 3256) (p 3379) (p 3452) (p 3880) (p 4134) (p 4341) (p 4347) (derived73560 p h) (derived73374 p h) (derived73490 p h) (derived73394 p h) (derived48569 p h)

theorem derived79827 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 2274) ∨ (¬ p 4438) ∨ (p 3379) ∨ (¬ p 3453) ∨ (¬ p 2528) ∨ (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 4521) :=
  ElevenRUP.step79827 (p 2156) (p 2177) (p 2274) (p 2528) (p 3073) (p 3379) (p 3452) (p 3453) (p 4261) (p 4438) (p 4521) (derived73544 p h) (derived73394 p h) (derived54265 p h)

theorem derived79828 (p : Nat → Prop) (h : Inputs p) :
    (p 2901) ∨ (¬ p 3156) ∨ (p 3379) ∨ (¬ p 2958) ∨ (p 2352) ∨ (¬ p 2248) ∨ (p 2493) ∨ (¬ p 3051) ∨ (¬ p 4433) :=
  ElevenRUP.step79828 (p 2248) (p 2352) (p 2493) (p 2499) (p 2901) (p 2958) (p 3051) (p 3156) (p 3379) (p 3452) (p 3956) (p 4320) (p 4433) (derived73552 p h) (derived73394 p h) (derived73500 p h) (derived73260 p h) (derived59901 p h)

theorem derived79829 (p : Nat → Prop) (h : Inputs p) :
    (p 2901) ∨ (¬ p 3156) ∨ (¬ p 2246) ∨ (¬ p 4434) ∨ (¬ p 2509) ∨ (¬ p 2958) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3051) ∨ (p 3379) :=
  ElevenRUP.step79829 (p 2246) (p 2509) (p 2608) (p 2744) (p 2901) (p 2958) (p 3051) (p 3156) (p 3379) (p 3452) (p 4320) (p 4434) (derived73552 p h) (derived73394 p h) (derived60025 p h)

theorem derived79832 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3791) ∨ (¬ p 4733) ∨ (¬ p 2774) ∨ (¬ p 2122) ∨ (p 3379) ∨ (¬ p 4826) ∨ (¬ p 3193) :=
  ElevenRUP.step79832 (p 2122) (p 2774) (p 3193) (p 3276) (p 3379) (p 3452) (p 3791) (p 4425) (p 4733) (p 4826) (derived73578 p h) (derived73394 p h) (derived50344 p h)

theorem derived79833 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 3343) ∨ (p 2440) ∨ (p 2406) :=
  ElevenRUP.step79833 (p 2406) (p 2440) (p 2542) (p 3238) (p 3343) (p 3359) (p 3379) (p 3452) (derived73394 p h) (derived73388 p h) (derived73270 p h) (derived73374 p h) (derived48558 p h)

theorem derived79834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 3379) ∨ (p 2373) ∨ (¬ p 2177) ∨ (¬ p 4905) ∨ (p 2406) ∨ (¬ p 2248) ∨ (¬ p 2331) :=
  ElevenRUP.step79834 (p 2177) (p 2248) (p 2295) (p 2331) (p 2373) (p 2406) (p 3238) (p 3379) (p 3452) (p 3880) (p 4905) (derived73394 p h) (derived73490 p h) (derived73374 p h) (derived48583 p h)

theorem derived79835 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3791) ∨ (¬ p 2331) ∨ (p 3379) ∨ (¬ p 2248) ∨ (¬ p 4826) ∨ (¬ p 3193) ∨ (¬ p 2295) :=
  ElevenRUP.step79835 (p 2248) (p 2295) (p 2331) (p 3193) (p 3276) (p 3379) (p 3452) (p 3791) (p 4425) (p 4826) (derived73578 p h) (derived73394 p h) (derived56638 p h)

theorem derived79836 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 4607) ∨ (¬ p 3146) ∨ (p 2406) ∨ (p 2528) :=
  ElevenRUP.step79836 (p 2406) (p 2528) (p 2534) (p 3146) (p 3238) (p 3379) (p 3452) (p 4607) (derived73394 p h) (derived73374 p h) (derived73268 p h) (derived44007 p h)

theorem derived79844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3379) ∨ (p 2406) ∨ (p 2373) :=
  ElevenRUP.step79844 (p 2373) (p 2406) (p 2619) (p 3238) (p 3379) (p 3452) (p 3880) (derived73394 p h) (derived73374 p h) (derived73490 p h) (derived44010 p h)

theorem derived79845 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (p 2373) ∨ (¬ p 2166) :=
  ElevenRUP.step79845 (p 2166) (p 2210) (p 2373) (p 3379) (p 3452) (p 3880) (derived73394 p h) (derived73490 p h) (derived46964 p h)

theorem derived79846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (p 3379) ∨ (¬ p 2331) ∨ (¬ p 2248) ∨ (p 2373) ∨ (¬ p 2363) ∨ (p 2406) ∨ (¬ p 2668) :=
  ElevenRUP.step79846 (p 2248) (p 2331) (p 2363) (p 2373) (p 2406) (p 2668) (p 3238) (p 3379) (p 3452) (p 3880) (p 5568) (derived73394 p h) (derived73490 p h) (derived73374 p h) (derived48599 p h)

theorem derived79848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (p 2797) ∨ (¬ p 3005) ∨ (¬ p 2331) ∨ (p 2406) ∨ (p 3379) ∨ (¬ p 5063) ∨ (p 2373) :=
  ElevenRUP.step79848 (p 2248) (p 2331) (p 2373) (p 2406) (p 2797) (p 3005) (p 3238) (p 3379) (p 3452) (p 3880) (p 4195) (p 5063) (derived73532 p h) (derived73374 p h) (derived73394 p h) (derived73490 p h) (derived54096 p h)

theorem derived79850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 3379) ∨ (p 2982) ∨ (p 2406) :=
  ElevenRUP.step79850 (p 2406) (p 2982) (p 3238) (p 3379) (p 3452) (p 4322) (p 4948) (derived73394 p h) (derived73846 p h) (derived73374 p h) (derived44013 p h)

theorem derived79851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (¬ p 3449) ∨ (p 4149) ∨ (p 3379) :=
  ElevenRUP.step79851 (p 3379) (p 3449) (p 3452) (p 4149) (p 4181) (p 4286) (derived73548 p h) (derived73394 p h) (derived47632 p h)

theorem derived79855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (p 3005) ∨ (¬ p 4376) ∨ (¬ p 3366) ∨ (¬ p 4774) ∨ (¬ p 3093) ∨ (¬ p 4236) ∨ (p 3379) ∨ (¬ p 2685) ∨ (p 2807) :=
  ElevenRUP.step79855 (p 2685) (p 2807) (p 3005) (p 3063) (p 3093) (p 3366) (p 3379) (p 3414) (p 3452) (p 3877) (p 4236) (p 4376) (p 4774) (derived73488 p h) (derived73394 p h) (derived73392 p h) (derived58395 p h)

theorem derived79856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3590) ∨ (p 3379) ∨ (¬ p 2608) ∨ (¬ p 2598) :=
  ElevenRUP.step79856 (p 2598) (p 2608) (p 3379) (p 3452) (p 3590) (derived73394 p h) (derived71436 p h)

theorem derived79857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3922) ∨ (p 3379) ∨ (¬ p 3590) ∨ (¬ p 4595) ∨ (p 3641) ∨ (¬ p 3984) ∨ (¬ p 3093) :=
  ElevenRUP.step79857 (p 3093) (p 3379) (p 3452) (p 3590) (p 3641) (p 3874) (p 3922) (p 3984) (p 4595) (derived73394 p h) (derived73484 p h) (derived41714 p h)

theorem derived79860 (p : Nat → Prop) (h : Inputs p) :
    (p 3193) ∨ (¬ p 4635) ∨ (p 2922) :=
  ElevenRUP.step79860 (p 2922) (p 2928) (p 3193) (p 4635) (derived73320 p h) (h 35784)

theorem derived79862 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2891) ∨ (¬ p 4877) ∨ (¬ p 2749) ∨ (¬ p 2210) ∨ (p 2807) :=
  ElevenRUP.step79862 (p 2210) (p 2241) (p 2244) (p 2749) (p 2807) (p 2891) (p 3414) (p 4877) (derived73224 p h) (derived73392 p h) (derived67141 p h)

theorem derived79864 (p : Nat → Prop) (h : Inputs p) :
    (p 3412) ∨ (p 2992) :=
  ElevenRUP.step79864 (p 2992) (p 3412) (p 5959) (derived74285 p h) (h 12739)

theorem derived79866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4333) ∨ (¬ p 2881) ∨ (p 2264) :=
  ElevenRUP.step79866 (p 2264) (p 2881) (p 3553) (p 3570) (p 4333) (derived73417 p h) (derived73410 p h) (h 28562)

theorem derived79871 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 3246) ∨ (¬ p 4333) :=
  ElevenRUP.step79871 (p 2449) (p 3246) (p 3947) (p 4333) (derived73494 p h) (h 6565)

theorem derived79872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4333) ∨ (p 2427) ∨ (¬ p 2651) ∨ (¬ p 2685) ∨ (p 2630) ∨ (¬ p 2246) :=
  ElevenRUP.step79872 (p 2246) (p 2427) (p 2630) (p 2651) (p 2685) (p 2810) (p 4235) (p 4333) (derived73536 p h) (derived73316 p h) (derived62144 p h)

end ElevenLogic
