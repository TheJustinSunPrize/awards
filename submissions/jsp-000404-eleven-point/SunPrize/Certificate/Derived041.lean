import SunPrize.Certificate.Derived040
import SunPrize.Certificate.Logic041
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived84901 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2190) ∨ (¬ p 3969) ∨ (¬ p 4405) ∨ (p 2274) :=
  ElevenRUP.step84901 (p 2190) (p 2274) (p 3097) (p 3969) (p 4405) (p 5580) (derived73352 p h) (derived48118 p h)

theorem derived84902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2190) ∨ (p 3125) ∨ (¬ p 3955) ∨ (¬ p 4620) ∨ (¬ p 3969) :=
  ElevenRUP.step84902 (p 2190) (p 3125) (p 3744) (p 3955) (p 3969) (p 4620) (p 5580) (derived73454 p h) (derived42017 p h)

theorem derived84903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5118) ∨ (¬ p 2528) ∨ (¬ p 3564) ∨ (p 2352) :=
  ElevenRUP.step84903 (p 2352) (p 2528) (p 2534) (p 3564) (p 4594) (p 5118) (p 5580) (derived73267 p h) (derived73656 p h) (derived67214 p h)

theorem derived84906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 2493) ∨ (p 3379) ∨ (p 2352) :=
  ElevenRUP.step84906 (p 2352) (p 2493) (p 2499) (p 3379) (p 3452) (p 3956) (p 5580) (derived73260 p h) (derived73394 p h) (derived73500 p h) (derived44232 p h)

theorem derived84909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3941) ∨ (p 2459) ∨ (p 2383) ∨ (¬ p 2778) :=
  ElevenRUP.step84909 (p 2383) (p 2387) (p 2459) (p 2778) (p 3941) (p 4348) (p 5580) (derived73562 p h) (derived73246 p h) (derived47049 p h)

theorem derived84910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 5580) ∨ (p 2383) ∨ (p 2528) ∨ (¬ p 2881) ∨ (¬ p 2778) ∨ (¬ p 2946) ∨ (¬ p 4786) ∨ (¬ p 2901) :=
  ElevenRUP.step84910 (p 2383) (p 2387) (p 2528) (p 2534) (p 2778) (p 2881) (p 2901) (p 2946) (p 4149) (p 4786) (p 5580) (derived73246 p h) (derived73268 p h) (derived52232 p h)

theorem derived84912 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3115) ∨ (¬ p 2946) ∨ (¬ p 3680) ∨ (¬ p 5123) ∨ (p 2774) ∨ (¬ p 4786) ∨ (p 2819) :=
  ElevenRUP.step84912 (p 2774) (p 2780) (p 2819) (p 2946) (p 3115) (p 3680) (p 4358) (p 4786) (p 5123) (p 5580) (derived73308 p h) (derived73564 p h) (derived63992 p h)

theorem derived84917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2246) ∨ (¬ p 5123) ∨ (p 2573) ∨ (¬ p 2761) ∨ (p 2352) ∨ (¬ p 2449) ∨ (¬ p 2807) ∨ (¬ p 4257) ∨ (¬ p 3347) ∨ (¬ p 2744) :=
  ElevenRUP.step84917 (p 2246) (p 2352) (p 2449) (p 2573) (p 2579) (p 2744) (p 2761) (p 2807) (p 3347) (p 3956) (p 4257) (p 5123) (p 5580) (derived73274 p h) (derived73500 p h) (derived52925 p h)

theorem derived84918 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2246) ∨ (¬ p 3366) ∨ (p 2774) ∨ (¬ p 2744) ∨ (¬ p 2651) ∨ (p 2819) ∨ (¬ p 3276) ∨ (¬ p 3343) ∨ (¬ p 5123) :=
  ElevenRUP.step84918 (p 2246) (p 2651) (p 2744) (p 2774) (p 2780) (p 2819) (p 3276) (p 3343) (p 3366) (p 4358) (p 5123) (p 5580) (derived73308 p h) (derived73564 p h) (derived63831 p h)

theorem derived84920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5118) ∨ (¬ p 3905) ∨ (¬ p 3366) ∨ (p 2573) ∨ (¬ p 3073) ∨ (p 2241) ∨ (¬ p 2744) ∨ (¬ p 3449) ∨ (p 2352) :=
  ElevenRUP.step84920 (p 2241) (p 2247) (p 2352) (p 2573) (p 2579) (p 2744) (p 3073) (p 3366) (p 3449) (p 3905) (p 3956) (p 5118) (p 5580) (derived73274 p h) (derived73226 p h) (derived73500 p h) (derived60494 p h)

theorem derived84921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5118) ∨ (p 2241) ∨ (¬ p 2744) ∨ (¬ p 3449) ∨ (p 2819) ∨ (¬ p 3073) ∨ (p 2829) :=
  ElevenRUP.step84921 (p 2241) (p 2247) (p 2744) (p 2819) (p 2829) (p 3073) (p 3449) (p 3688) (p 4358) (p 5118) (p 5580) (derived73226 p h) (derived73564 p h) (derived73444 p h) (derived52551 p h)

theorem derived84922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 2241) ∨ (¬ p 5118) ∨ (p 2156) ∨ (¬ p 3449) ∨ (¬ p 3073) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (p 2187) ∨ (¬ p 2136) :=
  ElevenRUP.step84922 (p 2136) (p 2156) (p 2187) (p 2241) (p 2247) (p 2744) (p 3073) (p 3366) (p 3449) (p 3646) (p 3989) (p 5118) (p 5580) (derived73226 p h) (derived73436 p h) (derived73502 p h) (derived59483 p h)

theorem derived84923 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3853) ∨ (¬ p 3830) ∨ (¬ p 3506) ∨ (p 2241) ∨ (¬ p 5123) ∨ (¬ p 3645) ∨ (p 2187) ∨ (p 2156) ∨ (¬ p 4959) :=
  ElevenRUP.step84923 (p 2156) (p 2187) (p 2241) (p 2247) (p 3506) (p 3645) (p 3646) (p 3830) (p 3853) (p 3989) (p 4959) (p 5123) (p 5580) (derived73226 p h) (derived73502 p h) (derived73436 p h) (derived50171 p h)

theorem derived84925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (p 2608) ∨ (p 2331) ∨ (¬ p 3707) ∨ (¬ p 2750) ∨ (p 2668) ∨ (¬ p 3830) ∨ (¬ p 5123) ∨ (¬ p 2252) :=
  ElevenRUP.step84925 (p 2252) (p 2331) (p 2608) (p 2668) (p 2750) (p 2963) (p 3324) (p 3707) (p 3830) (p 3954) (p 5123) (p 5580) (derived73498 p h) (derived73338 p h) (derived73386 p h) (derived64470 p h)

theorem derived84929 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5123) ∨ (¬ p 3276) ∨ (¬ p 3343) ∨ (p 2774) ∨ (¬ p 2651) ∨ (p 2819) ∨ (¬ p 4786) :=
  ElevenRUP.step84929 (p 2651) (p 2774) (p 2780) (p 2819) (p 3276) (p 3343) (p 4358) (p 4786) (p 5123) (p 5580) (derived73308 p h) (derived73564 p h) (derived63748 p h)

theorem derived84933 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3998) ∨ (¬ p 2363) ∨ (¬ p 5242) ∨ (p 2241) :=
  ElevenRUP.step84933 (p 2241) (p 2247) (p 2363) (p 3998) (p 5242) (p 5580) (derived73226 p h) (derived47024 p h)

theorem derived84934 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3998) ∨ (¬ p 5580) ∨ (¬ p 4744) ∨ (¬ p 2103) ∨ (¬ p 2363) ∨ (¬ p 3698) ∨ (p 2563) :=
  ElevenRUP.step84934 (p 2103) (p 2363) (p 2563) (p 3698) (p 3998) (p 4110) (p 4744) (p 5580) (derived73516 p h) (derived57103 p h)

theorem derived84935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 5580) ∨ (p 2553) ∨ (¬ p 4405) ∨ (¬ p 2510) :=
  ElevenRUP.step84935 (p 2510) (p 2553) (p 2588) (p 4149) (p 4405) (p 5580) (derived73282 p h) (derived42587 p h)

theorem derived84944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3941) ∨ (p 2383) ∨ (¬ p 2307) :=
  ElevenRUP.step84944 (p 2307) (p 2383) (p 2387) (p 3941) (p 5580) (derived73246 p h) (derived45830 p h)

theorem derived84945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3680) ∨ (¬ p 3922) ∨ (¬ p 3923) ∨ (¬ p 2249) ∨ (¬ p 3212) ∨ (¬ p 2727) ∨ (¬ p 2656) ∨ (¬ p 4399) ∨ (p 2331) ∨ (¬ p 5123) :=
  ElevenRUP.step84945 (p 2249) (p 2331) (p 2656) (p 2727) (p 2963) (p 3212) (p 3680) (p 3922) (p 3923) (p 4399) (p 5123) (p 5580) (derived73338 p h) (derived61194 p h)

theorem derived84946 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3680) ∨ (¬ p 5123) ∨ (p 2668) ∨ (¬ p 2230) ∨ (¬ p 3362) ∨ (¬ p 3105) ∨ (¬ p 4789) ∨ (¬ p 3698) ∨ (p 2331) :=
  ElevenRUP.step84946 (p 2230) (p 2331) (p 2668) (p 2963) (p 3105) (p 3324) (p 3362) (p 3680) (p 3698) (p 4789) (p 5123) (p 5580) (derived73386 p h) (derived73338 p h) (derived48266 p h)

theorem derived84947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 2753) ∨ (p 2187) ∨ (¬ p 3645) ∨ (¬ p 3755) ∨ (p 2156) ∨ (¬ p 3506) ∨ (¬ p 4877) ∨ (¬ p 2696) ∨ (¬ p 5123) :=
  ElevenRUP.step84947 (p 2156) (p 2187) (p 2696) (p 2753) (p 3506) (p 3645) (p 3646) (p 3755) (p 3989) (p 4877) (p 5123) (p 5580) (derived73502 p h) (derived73436 p h) (derived61381 p h)

theorem derived84949 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3842) ∨ (¬ p 5123) ∨ (¬ p 2241) ∨ (p 2187) ∨ (p 2156) ∨ (¬ p 3506) :=
  ElevenRUP.step84949 (p 2156) (p 2187) (p 2241) (p 3506) (p 3646) (p 3842) (p 3989) (p 4524) (p 5123) (p 5580) (derived73502 p h) (derived73436 p h) (derived72962 p h) (derived52235 p h)

theorem derived84952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3125) ∨ (¬ p 3872) ∨ (¬ p 2274) :=
  ElevenRUP.step84952 (p 2274) (p 3125) (p 3246) (p 3690) (p 3744) (p 3872) (derived73445 p h) (derived73454 p h) (derived65745 p h)

theorem derived84956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4237) ∨ (¬ p 3256) ∨ (p 2284) ∨ (p 3146) ∨ (¬ p 4509) :=
  ElevenRUP.step84956 (p 2284) (p 3146) (p 3256) (p 3692) (p 3952) (p 4237) (p 4509) (derived73496 p h) (derived73448 p h) (derived50306 p h)

theorem derived84958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5612) ∨ (¬ p 4009) ∨ (¬ p 4509) ∨ (¬ p 4188) ∨ (p 2284) ∨ (¬ p 4237) :=
  ElevenRUP.step84958 (p 2284) (p 3952) (p 4009) (p 4188) (p 4237) (p 4509) (p 5612) (derived73496 p h) (derived62184 p h)

theorem derived84960 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 3256) ∨ (¬ p 2946) ∨ (¬ p 2255) ∨ (¬ p 4262) ∨ (¬ p 4237) :=
  ElevenRUP.step84960 (p 2255) (p 2946) (p 3073) (p 3256) (p 4237) (p 4261) (p 4262) (derived73544 p h) (derived48511 p h)

theorem derived84962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3657) ∨ (p 2881) ∨ (¬ p 4001) :=
  ElevenRUP.step84962 (p 2417) (p 2881) (p 3570) (p 3657) (p 4001) (derived73418 p h) (h 33944)

theorem derived84968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3037) ∨ (¬ p 2341) ∨ (¬ p 4919) ∨ (¬ p 4104) ∨ (p 2946) ∨ (p 3527) :=
  ElevenRUP.step84968 (p 2341) (p 2946) (p 2952) (p 3037) (p 3527) (p 3548) (p 4104) (p 4919) (derived73330 p h) (derived73404 p h) (derived41024 p h)

theorem derived84975 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2449) ∨ (¬ p 4156) ∨ (p 2396) ∨ (p 2668) ∨ (¬ p 3987) :=
  ElevenRUP.step84975 (p 2383) (p 2396) (p 2449) (p 2668) (p 3324) (p 3987) (p 4107) (p 4156) (derived73514 p h) (derived73386 p h) (derived43228 p h)

theorem derived84976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2668) ∨ (¬ p 4566) ∨ (¬ p 3987) ∨ (p 2946) :=
  ElevenRUP.step84976 (p 2383) (p 2668) (p 2946) (p 2952) (p 3324) (p 3987) (p 4566) (derived73386 p h) (derived73330 p h) (derived41103 p h)

theorem derived84977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2383) ∨ (¬ p 3987) ∨ (p 2668) ∨ (¬ p 2396) :=
  ElevenRUP.step84977 (p 2295) (p 2383) (p 2396) (p 2668) (p 3324) (p 3987) (derived73386 p h) (derived49483 p h)

theorem derived84979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 3987) ∨ (p 2274) :=
  ElevenRUP.step84979 (p 2274) (p 2295) (p 2383) (p 2668) (p 3097) (p 3324) (p 3987) (derived73386 p h) (derived73352 p h) (derived49481 p h)

theorem derived84980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 3987) ∨ (p 2651) :=
  ElevenRUP.step84980 (p 2295) (p 2383) (p 2651) (p 2657) (p 2668) (p 3324) (p 3987) (derived73386 p h) (derived73288 p h) (derived49464 p h)

theorem derived84981 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2383) ∨ (¬ p 2630) ∨ (p 2668) ∨ (¬ p 3987) :=
  ElevenRUP.step84981 (p 2383) (p 2630) (p 2668) (p 2797) (p 3324) (p 3987) (p 4195) (derived73532 p h) (derived73386 p h) (derived43224 p h)

theorem derived84982 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 4790) ∨ (¬ p 3987) :=
  ElevenRUP.step84982 (p 2383) (p 2668) (p 2797) (p 3324) (p 3987) (p 4195) (p 4790) (derived73532 p h) (derived73386 p h) (derived53073 p h)

theorem derived84986 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 4036) ∨ (¬ p 3987) ∨ (¬ p 4038) ∨ (¬ p 4190) :=
  ElevenRUP.step84986 (p 3286) (p 3292) (p 3987) (p 4036) (p 4038) (p 4190) (derived73378 p h) (h 17654)

theorem derived84987 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 4421) ∨ (¬ p 2667) ∨ (¬ p 3987) :=
  ElevenRUP.step84987 (p 2667) (p 3286) (p 3292) (p 3987) (p 4421) (derived73378 p h) (h 32327)

theorem derived84998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 3746) ∨ (p 2573) :=
  ElevenRUP.step84998 (p 2573) (p 2579) (p 3355) (p 3746) (derived73274 p h) (h 20208)

theorem derived85001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 3276) ∨ (¬ p 3016) ∨ (p 2573) :=
  ElevenRUP.step85001 (p 2573) (p 2579) (p 3016) (p 3276) (p 3355) (derived73274 p h) (derived47889 p h)

theorem derived85004 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4695) ∨ (p 2363) ∨ (¬ p 3355) ∨ (p 2470) ∨ (¬ p 4384) :=
  ElevenRUP.step85004 (p 2363) (p 2470) (p 2476) (p 3355) (p 4347) (p 4384) (p 4695) (derived73560 p h) (derived73250 p h) (derived46822 p h)

theorem derived85006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (p 3146) ∨ (¬ p 4434) ∨ (p 2470) ∨ (¬ p 4695) :=
  ElevenRUP.step85006 (p 2470) (p 2476) (p 3146) (p 3355) (p 3692) (p 4434) (p 4695) (derived73448 p h) (derived73250 p h) (derived41697 p h)

theorem derived85010 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4635) ∨ (p 3389) :=
  ElevenRUP.step85010 (p 3355) (p 3389) (p 3540) (p 4635) (derived73402 p h) (h 19852)

theorem derived85011 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4451) ∨ (p 3389) ∨ (p 2449) ∨ (¬ p 4327) :=
  ElevenRUP.step85011 (p 2449) (p 3355) (p 3389) (p 3540) (p 3947) (p 4327) (p 4451) (derived73402 p h) (derived73494 p h) (derived48023 p h)

theorem derived85012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4451) ∨ (p 3246) ∨ (¬ p 4647) ∨ (p 3389) :=
  ElevenRUP.step85012 (p 3246) (p 3355) (p 3389) (p 3540) (p 3690) (p 4451) (p 4647) (derived73446 p h) (derived73402 p h) (derived50081 p h)

theorem derived85016 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 5160) ∨ (p 2573) ∨ (p 2553) :=
  ElevenRUP.step85016 (p 2553) (p 2573) (p 2579) (p 2588) (p 3355) (p 5160) (derived73274 p h) (derived73282 p h) (derived47982 p h)

theorem derived85018 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 3276) ∨ (¬ p 2493) ∨ (p 2573) :=
  ElevenRUP.step85018 (p 2493) (p 2573) (p 2579) (p 3276) (p 3355) (derived73274 p h) (derived59610 p h)

theorem derived85023 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3355) ∨ (¬ p 3016) ∨ (p 2573) :=
  ElevenRUP.step85023 (p 2437) (p 2573) (p 2579) (p 3016) (p 3355) (p 3742) (derived73452 p h) (derived73274 p h) (derived45915 p h)

theorem derived85026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 3355) ∨ (p 3389) ∨ (¬ p 2761) ∨ (¬ p 4451) :=
  ElevenRUP.step85026 (p 2437) (p 2761) (p 3355) (p 3389) (p 3540) (p 4451) (derived73402 p h) (derived58080 p h)

theorem derived85029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (p 3389) ∨ (¬ p 2440) ∨ (¬ p 2437) :=
  ElevenRUP.step85029 (p 2437) (p 2440) (p 3355) (p 3389) (p 3540) (derived73402 p h) (derived45864 p h)

theorem derived85033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3355) ∨ (p 2440) ∨ (p 2230) ∨ (¬ p 4952) :=
  ElevenRUP.step85033 (p 2230) (p 2440) (p 2542) (p 2589) (p 3355) (p 3680) (p 4952) (derived73270 p h) (derived73284 p h) (derived48715 p h)

theorem derived85034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (p 2230) :=
  ElevenRUP.step85034 (p 2230) (p 2589) (p 3276) (p 3355) (p 4322) (derived73284 p h) (derived63425 p h)

theorem derived85035 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3355) ∨ (¬ p 3276) ∨ (p 2230) ∨ (¬ p 4281) :=
  ElevenRUP.step85035 (p 2230) (p 2406) (p 2589) (p 3276) (p 3355) (p 4281) (derived73284 p h) (derived45161 p h)

theorem derived85036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 3237) ∨ (p 2230) :=
  ElevenRUP.step85036 (p 2230) (p 2589) (p 3237) (p 3355) (derived73284 p h) (h 20205)

theorem derived85041 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4438) ∨ (p 2459) ∨ (p 2470) ∨ (¬ p 4695) :=
  ElevenRUP.step85041 (p 2459) (p 2470) (p 2476) (p 3355) (p 4348) (p 4438) (p 4695) (derived73562 p h) (derived73250 p h) (derived40946 p h)

theorem derived85042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4451) ∨ (p 3631) ∨ (p 3389) ∨ (¬ p 2930) :=
  ElevenRUP.step85042 (p 2930) (p 3355) (p 3389) (p 3540) (p 3631) (p 3817) (p 4451) (derived73468 p h) (derived73402 p h) (derived41096 p h)

theorem derived85047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4451) ∨ (¬ p 2922) ∨ (p 3389) ∨ (¬ p 2761) ∨ (¬ p 3355) :=
  ElevenRUP.step85047 (p 2761) (p 2922) (p 3355) (p 3389) (p 3540) (p 4451) (derived73402 p h) (derived55293 p h)

theorem derived85052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 5116) ∨ (p 2459) :=
  ElevenRUP.step85052 (p 2459) (p 3941) (p 4348) (p 5116) (derived73562 p h) (h 30490)

theorem derived85053 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4262) ∨ (¬ p 3449) ∨ (p 2241) :=
  ElevenRUP.step85053 (p 2241) (p 2247) (p 3449) (p 4262) (derived73226 p h) (h 6433)

theorem derived85065 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 3136) ∨ (¬ p 4590) ∨ (¬ p 2951) ∨ (¬ p 2745) ∨ (¬ p 4988) ∨ (¬ p 4262) ∨ (¬ p 2088) :=
  ElevenRUP.step85065 (p 2088) (p 2745) (p 2951) (p 3073) (p 3136) (p 4261) (p 4262) (p 4590) (p 4988) (derived73544 p h) (derived64951 p h)

theorem derived85066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2331) ∨ (¬ p 4556) ∨ (¬ p 3361) ∨ (p 3425) ∨ (¬ p 4424) ∨ (p 2737) ∨ (p 2295) ∨ (p 2881) :=
  ElevenRUP.step85066 (p 2295) (p 2331) (p 2737) (p 2743) (p 2881) (p 2963) (p 3361) (p 3425) (p 3471) (p 3527) (p 3568) (p 3570) (p 4424) (p 4556) (derived73338 p h) (derived73396 p h) (derived73298 p h) (derived73416 p h) (derived73418 p h) (derived71601 p h)

theorem derived85068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3038) ∨ (p 2992) ∨ (p 2881) ∨ (¬ p 2946) :=
  ElevenRUP.step85068 (p 2881) (p 2946) (p 2992) (p 3038) (p 3527) (p 3570) (p 3662) (derived73440 p h) (derived73418 p h) (derived43745 p h)

theorem derived85069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4736) ∨ (¬ p 4556) ∨ (p 2553) ∨ (¬ p 2210) ∨ (p 3422) ∨ (p 2598) ∨ (p 2881) ∨ (¬ p 4431) :=
  ElevenRUP.step85069 (p 2210) (p 2553) (p 2588) (p 2598) (p 2881) (p 3055) (p 3422) (p 3527) (p 3570) (p 3584) (p 4431) (p 4556) (p 4736) (derived73282 p h) (derived73426 p h) (derived73350 p h) (derived73418 p h) (derived50471 p h)

theorem derived85072 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4909) ∨ (p 2881) :=
  ElevenRUP.step85072 (p 2881) (p 3527) (p 3570) (p 4909) (derived73418 p h) (h 20248)

theorem derived85074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2608) ∨ (p 2881) ∨ (¬ p 3399) :=
  ElevenRUP.step85074 (p 2608) (p 2881) (p 3399) (p 3527) (p 3570) (p 3954) (derived73498 p h) (derived73418 p h) (derived45796 p h)

theorem derived85075 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 3379) ∨ (¬ p 3399) ∨ (p 2881) :=
  ElevenRUP.step85075 (p 2881) (p 3379) (p 3399) (p 3452) (p 3527) (p 3570) (derived73394 p h) (derived73418 p h) (derived44612 p h)

theorem derived85077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4556) ∨ (¬ p 3399) ∨ (p 2881) ∨ (p 2696) ∨ (p 2295) ∨ (p 2797) ∨ (¬ p 4736) :=
  ElevenRUP.step85077 (p 2295) (p 2696) (p 2797) (p 2881) (p 3365) (p 3399) (p 3527) (p 3568) (p 3570) (p 4195) (p 4556) (p 4736) (derived73418 p h) (derived73390 p h) (derived73416 p h) (derived73532 p h) (derived52360 p h)

theorem derived85078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (¬ p 2797) ∨ (¬ p 3399) ∨ (¬ p 4736) ∨ (p 3005) ∨ (¬ p 4044) ∨ (p 2881) ∨ (¬ p 2298) ∨ (p 2331) ∨ (¬ p 4556) ∨ (¬ p 3527) :=
  ElevenRUP.step85078 (p 2298) (p 2331) (p 2797) (p 2881) (p 2963) (p 3005) (p 3399) (p 3527) (p 3570) (p 3877) (p 4044) (p 4236) (p 4556) (p 4736) (derived73488 p h) (derived73418 p h) (derived73338 p h) (derived58286 p h)

theorem derived85082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2437) ∨ (¬ p 5193) ∨ (¬ p 3016) ∨ (¬ p 3399) ∨ (p 2881) ∨ (¬ p 4647) ∨ (p 2573) :=
  ElevenRUP.step85082 (p 2437) (p 2573) (p 2579) (p 2881) (p 3016) (p 3399) (p 3527) (p 3570) (p 3742) (p 4647) (p 5193) (derived73452 p h) (derived73418 p h) (derived73274 p h) (derived50534 p h)

theorem derived85085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3032) ∨ (p 2651) ∨ (¬ p 2807) ∨ (p 2881) :=
  ElevenRUP.step85085 (p 2651) (p 2657) (p 2807) (p 2881) (p 3032) (p 3527) (p 3570) (derived73288 p h) (derived73418 p h) (derived45245 p h)

theorem derived85086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2341) ∨ (¬ p 4344) ∨ (¬ p 3959) ∨ (p 2427) ∨ (¬ p 4632) ∨ (¬ p 4431) :=
  ElevenRUP.step85086 (p 2341) (p 2427) (p 3527) (p 3551) (p 3959) (p 4235) (p 4344) (p 4431) (p 4632) (derived73408 p h) (derived73536 p h) (derived41913 p h)

theorem derived85090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2396) ∨ (¬ p 2441) ∨ (¬ p 4877) ∨ (p 2156) ∨ (p 2608) ∨ (¬ p 3645) ∨ (¬ p 3399) ∨ (p 2911) ∨ (p 2274) :=
  ElevenRUP.step85090 (p 2156) (p 2274) (p 2396) (p 2441) (p 2608) (p 2911) (p 3097) (p 3399) (p 3527) (p 3644) (p 3645) (p 3646) (p 3954) (p 4107) (p 4877) (derived73514 p h) (derived73436 p h) (derived73498 p h) (derived73434 p h) (derived73352 p h) (derived50795 p h)

theorem derived85094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2341) ∨ (¬ p 3687) ∨ (¬ p 3379) ∨ (¬ p 5206) :=
  ElevenRUP.step85094 (p 2341) (p 3379) (p 3527) (p 3551) (p 3687) (p 5206) (derived73408 p h) (derived71602 p h)

theorem derived85098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 3379) ∨ (¬ p 3399) ∨ (p 2911) ∨ (¬ p 3581) :=
  ElevenRUP.step85098 (p 2911) (p 3379) (p 3399) (p 3452) (p 3527) (p 3581) (p 3644) (derived73394 p h) (derived73434 p h) (derived59502 p h)

theorem derived85099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3136) ∨ (p 2177) ∨ (¬ p 3399) ∨ (¬ p 4361) ∨ (¬ p 2254) ∨ (p 2685) ∨ (p 2946) :=
  ElevenRUP.step85099 (p 2177) (p 2254) (p 2299) (p 2685) (p 2946) (p 2952) (p 3136) (p 3399) (p 3527) (p 3572) (p 4361) (derived73234 p h) (derived73420 p h) (derived73330 p h) (derived58583 p h)

theorem derived85105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2341) ∨ (¬ p 4793) ∨ (¬ p 3873) ∨ (¬ p 2608) ∨ (¬ p 3820) :=
  ElevenRUP.step85105 (p 2341) (p 2608) (p 3527) (p 3551) (p 3820) (p 3873) (p 4793) (derived73408 p h) (derived48117 p h)

theorem derived85109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2241) ∨ (p 2911) ∨ (p 2437) :=
  ElevenRUP.step85109 (p 2241) (p 2247) (p 2437) (p 2911) (p 3527) (p 3644) (p 3742) (derived73226 p h) (derived73434 p h) (derived73452 p h) (derived66765 p h)

theorem derived85111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2927) ∨ (p 2911) :=
  ElevenRUP.step85111 (p 2911) (p 2927) (p 3527) (p 3644) (derived73434 p h) (h 28361)

theorem derived85118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5358) ∨ (p 3830) ∨ (¬ p 4666) ∨ (¬ p 3527) ∨ (¬ p 3399) :=
  ElevenRUP.step85118 (p 3399) (p 3527) (p 3830) (p 3834) (p 4666) (p 5358) (derived73474 p h) (derived65032 p h)

theorem derived85120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2417) ∨ (p 2911) ∨ (¬ p 3399) :=
  ElevenRUP.step85120 (p 2417) (p 2911) (p 3399) (p 3527) (p 3644) (derived73434 p h) (derived44888 p h)

theorem derived85122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 5472) ∨ (¬ p 4452) ∨ (¬ p 3527) ∨ (p 2177) :=
  ElevenRUP.step85122 (p 2177) (p 2299) (p 3527) (p 4435) (p 4452) (p 5472) (derived73234 p h) (derived48048 p h)

theorem derived85123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2946) ∨ (¬ p 2254) ∨ (¬ p 4473) ∨ (¬ p 3399) ∨ (p 2717) ∨ (p 2284) ∨ (p 2274) :=
  ElevenRUP.step85123 (p 2254) (p 2274) (p 2284) (p 2717) (p 2946) (p 2952) (p 3097) (p 3399) (p 3527) (p 3659) (p 3952) (p 4473) (derived73330 p h) (derived73438 p h) (derived73496 p h) (derived73352 p h) (derived48457 p h)

theorem derived85129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4427) ∨ (¬ p 2311) ∨ (¬ p 2274) ∨ (p 2341) :=
  ElevenRUP.step85129 (p 2274) (p 2311) (p 2341) (p 3527) (p 3551) (p 4427) (derived73408 p h) (derived71604 p h)

theorem derived85130 (p : Nat → Prop) (h : Inputs p) :
    (p 3631) ∨ (¬ p 3527) ∨ (¬ p 2274) ∨ (¬ p 2396) :=
  ElevenRUP.step85130 (p 2274) (p 2396) (p 3527) (p 3631) (p 3817) (derived73468 p h) (derived55388 p h)

theorem derived85135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2927) ∨ (¬ p 4730) ∨ (¬ p 3389) ∨ (¬ p 3686) ∨ (p 2717) :=
  ElevenRUP.step85135 (p 2717) (p 2927) (p 3389) (p 3527) (p 3659) (p 3686) (p 4730) (derived73438 p h) (derived59991 p h)

theorem derived85136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 4112) ∨ (¬ p 2665) ∨ (¬ p 2927) ∨ (¬ p 3527) ∨ (p 2264) :=
  ElevenRUP.step85136 (p 2264) (p 2665) (p 2927) (p 3389) (p 3527) (p 3553) (p 4112) (derived73410 p h) (derived48396 p h)

theorem derived85138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4424) ∨ (¬ p 3527) ∨ (p 2156) ∨ (¬ p 2143) ∨ (¬ p 4276) ∨ (p 2274) ∨ (p 2839) ∨ (p 2911) ∨ (p 3425) :=
  ElevenRUP.step85138 (p 2143) (p 2156) (p 2274) (p 2839) (p 2911) (p 3097) (p 3425) (p 3471) (p 3527) (p 3583) (p 3644) (p 3646) (p 4276) (p 4424) (derived73436 p h) (derived73352 p h) (derived73424 p h) (derived73434 p h) (derived73396 p h) (derived71605 p h)

theorem derived85140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5145) ∨ (¬ p 2295) ∨ (¬ p 2667) ∨ (¬ p 4138) ∨ (p 2383) ∨ (¬ p 3527) :=
  ElevenRUP.step85140 (p 2295) (p 2383) (p 2387) (p 2667) (p 3527) (p 4138) (p 5145) (derived73246 p h) (derived63659 p h)

theorem derived85142 (p : Nat → Prop) (h : Inputs p) :
    (p 3547) ∨ (¬ p 3309) :=
  ElevenRUP.step85142 (p 3309) (p 3547) (p 5143) (derived73938 p h) (h 8709)

theorem derived85159 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2295) ∨ (¬ p 2751) ∨ (¬ p 4759) ∨ (¬ p 3309) :=
  ElevenRUP.step85159 (p 2295) (p 2751) (p 2797) (p 3309) (p 3568) (p 4195) (p 4759) (derived73532 p h) (derived73416 p h) (derived60580 p h)

theorem derived85160 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2295) ∨ (¬ p 3093) ∨ (¬ p 3309) :=
  ElevenRUP.step85160 (p 2295) (p 2797) (p 3093) (p 3309) (p 3568) (p 4195) (derived73532 p h) (derived73416 p h) (derived45998 p h)

theorem derived85162 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 3309) ∨ (¬ p 4518) ∨ (¬ p 2156) ∨ (¬ p 4275) :=
  ElevenRUP.step85162 (p 2156) (p 3051) (p 3309) (p 3556) (p 4275) (p 4518) (derived73414 p h) (derived41646 p h)

theorem derived85165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3948) ∨ (¬ p 3309) ∨ (p 2307) ∨ (p 3016) ∨ (¬ p 2386) ∨ (¬ p 4814) ∨ (¬ p 4338) :=
  ElevenRUP.step85165 (p 2307) (p 2313) (p 2386) (p 3016) (p 3309) (p 3574) (p 3948) (p 4338) (p 4814) (derived73238 p h) (derived73422 p h) (derived53320 p h)

theorem derived85167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2307) ∨ (¬ p 5015) ∨ (¬ p 3379) ∨ (¬ p 4869) :=
  ElevenRUP.step85167 (p 2307) (p 2313) (p 3309) (p 3379) (p 4869) (p 5015) (derived73238 p h) (derived71608 p h)

theorem derived85172 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4869) ∨ (¬ p 2598) ∨ (p 3367) ∨ (p 2553) :=
  ElevenRUP.step85172 (p 2553) (p 2588) (p 2598) (p 3309) (p 3367) (p 3585) (p 4869) (derived73428 p h) (derived73282 p h) (derived42877 p h)

theorem derived85174 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3309) ∨ (¬ p 2177) ∨ (¬ p 2507) ∨ (¬ p 3581) :=
  ElevenRUP.step85174 (p 2177) (p 2507) (p 2911) (p 3309) (p 3581) (p 3644) (derived73434 p h) (derived48163 p h)

theorem derived85175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 3093) ∨ (p 3005) ∨ (p 2696) ∨ (p 3256) ∨ (¬ p 4736) ∨ (¬ p 3950) :=
  ElevenRUP.step85175 (p 2396) (p 2696) (p 3005) (p 3093) (p 3256) (p 3309) (p 3365) (p 3877) (p 3950) (p 4118) (p 4736) (derived73488 p h) (derived73390 p h) (derived73520 p h) (derived50310 p h)

theorem derived85179 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2177) :=
  ElevenRUP.step85179 (p 2177) (p 2608) (p 3093) (p 3309) (p 3954) (derived73498 p h) (derived52571 p h)

theorem derived85181 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2295) :=
  ElevenRUP.step85181 (p 2295) (p 2608) (p 3093) (p 3309) (p 3568) (p 3954) (derived73498 p h) (derived73416 p h) (derived62694 p h)

theorem derived85190 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (p 2331) ∨ (¬ p 3923) ∨ (¬ p 3309) :=
  ElevenRUP.step85190 (p 2295) (p 2331) (p 2963) (p 3309) (p 3568) (p 3923) (derived73416 p h) (derived73338 p h) (derived44192 p h)

theorem derived85191 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 3309) ∨ (p 2696) ∨ (¬ p 4666) ∨ (¬ p 2177) ∨ (¬ p 3093) ∨ (¬ p 4736) ∨ (p 2685) :=
  ElevenRUP.step85191 (p 2177) (p 2449) (p 2685) (p 2696) (p 3093) (p 3309) (p 3365) (p 3572) (p 3947) (p 4666) (p 4736) (derived73494 p h) (derived73390 p h) (derived73420 p h) (derived49409 p h)

theorem derived85192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2881) ∨ (¬ p 2177) ∨ (¬ p 4338) ∨ (¬ p 2210) :=
  ElevenRUP.step85192 (p 2177) (p 2210) (p 2881) (p 3309) (p 3570) (p 4338) (derived73418 p h) (derived60323 p h)

theorem derived85195 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3309) ∨ (¬ p 4187) ∨ (¬ p 3093) :=
  ElevenRUP.step85195 (p 2761) (p 3093) (p 3309) (p 3461) (p 4187) (p 4381) (derived73574 p h) (derived45910 p h)

theorem derived85196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4869) ∨ (¬ p 4845) ∨ (p 2307) ∨ (¬ p 2785) ∨ (p 2737) :=
  ElevenRUP.step85196 (p 2307) (p 2313) (p 2737) (p 2743) (p 2785) (p 3309) (p 4845) (p 4869) (derived73238 p h) (derived73298 p h) (derived42372 p h)

theorem derived85201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4869) ∨ (¬ p 3983) ∨ (p 2307) ∨ (¬ p 3361) ∨ (¬ p 4749) ∨ (p 3367) :=
  ElevenRUP.step85201 (p 2307) (p 2313) (p 3309) (p 3361) (p 3367) (p 3585) (p 3983) (p 4749) (p 4869) (derived73238 p h) (derived73428 p h) (derived53026 p h)

theorem derived85206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 3073) ∨ (¬ p 2528) ∨ (¬ p 4432) ∨ (¬ p 4371) :=
  ElevenRUP.step85206 (p 2528) (p 3073) (p 3309) (p 4261) (p 4371) (p 4432) (derived73544 p h) (derived71611 p h)

theorem derived85207 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3366) ∨ (p 2352) ∨ (p 3422) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2744) ∨ (p 2598) :=
  ElevenRUP.step85207 (p 2241) (p 2247) (p 2352) (p 2598) (p 2744) (p 3055) (p 3093) (p 3309) (p 3366) (p 3422) (p 3584) (p 3956) (derived73226 p h) (derived73500 p h) (derived73426 p h) (derived73350 p h) (derived71612 p h)

theorem derived85209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2509) ∨ (p 2553) ∨ (¬ p 2505) ∨ (¬ p 4595) :=
  ElevenRUP.step85209 (p 2505) (p 2509) (p 2553) (p 2588) (p 3309) (p 4595) (derived73282 p h) (derived53837 p h)

theorem derived85213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3276) ∨ (p 3105) ∨ (¬ p 4952) ∨ (p 2132) ∨ (¬ p 3309) ∨ (¬ p 4826) ∨ (¬ p 4736) ∨ (¬ p 3093) :=
  ElevenRUP.step85213 (p 2132) (p 2138) (p 3093) (p 3105) (p 3276) (p 3309) (p 3791) (p 4385) (p 4425) (p 4736) (p 4826) (p 4952) (derived73578 p h) (derived73576 p h) (derived73214 p h) (derived51436 p h)

theorem derived85214 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3319) ∨ (¬ p 3309) ∨ (p 2274) :=
  ElevenRUP.step85214 (p 2274) (p 3097) (p 3309) (p 3319) (p 3461) (p 4026) (p 4191) (derived73530 p h) (derived73504 p h) (derived73352 p h) (derived64444 p h)

theorem derived85218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2274) ∨ (¬ p 4338) ∨ (¬ p 2187) ∨ (¬ p 2210) :=
  ElevenRUP.step85218 (p 2187) (p 2210) (p 2274) (p 3097) (p 3309) (p 4338) (derived73352 p h) (derived54997 p h)

theorem derived85220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2298) ∨ (¬ p 4761) ∨ (p 2807) ∨ (¬ p 2331) :=
  ElevenRUP.step85220 (p 2298) (p 2331) (p 2807) (p 3309) (p 3414) (p 4761) (derived73392 p h) (derived41629 p h)

theorem derived85222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2295) ∨ (¬ p 3093) ∨ (¬ p 3309) :=
  ElevenRUP.step85222 (p 2295) (p 2668) (p 3093) (p 3309) (p 3568) (derived73416 p h) (derived48668 p h)

theorem derived85224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2727) ∨ (p 2295) ∨ (¬ p 4975) ∨ (¬ p 4759) :=
  ElevenRUP.step85224 (p 2295) (p 2727) (p 3309) (p 3568) (p 4111) (p 4759) (p 4975) (derived73518 p h) (derived73416 p h) (derived51560 p h)

theorem derived85227 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 3309) ∨ (¬ p 3146) ∨ (¬ p 4371) ∨ (p 2295) :=
  ElevenRUP.step85227 (p 2295) (p 3073) (p 3146) (p 3309) (p 3568) (p 4261) (p 4371) (derived73544 p h) (derived73416 p h) (derived44287 p h)

theorem derived85231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2505) ∨ (p 2553) ∨ (¬ p 2663) ∨ (p 2406) ∨ (¬ p 2230) :=
  ElevenRUP.step85231 (p 2230) (p 2406) (p 2505) (p 2553) (p 2588) (p 2663) (p 3238) (p 3309) (derived73282 p h) (derived73374 p h) (derived63970 p h)

theorem derived85232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2307) ∨ (p 2406) ∨ (¬ p 4717) ∨ (¬ p 2386) ∨ (¬ p 2505) :=
  ElevenRUP.step85232 (p 2307) (p 2313) (p 2386) (p 2406) (p 2505) (p 3238) (p 3309) (p 4717) (derived73238 p h) (derived73374 p h) (derived42046 p h)

theorem derived85233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3921) ∨ (¬ p 3309) ∨ (p 2922) ∨ (¬ p 2505) :=
  ElevenRUP.step85233 (p 2505) (p 2922) (p 2928) (p 3309) (p 3921) (derived73320 p h) (h 5810)

theorem derived85236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3921) ∨ (¬ p 2441) ∨ (¬ p 3309) ∨ (p 2230) ∨ (¬ p 5193) ∨ (¬ p 3093) :=
  ElevenRUP.step85236 (p 2230) (p 2441) (p 2589) (p 3093) (p 3309) (p 3921) (p 5193) (derived73284 p h) (derived41528 p h)

theorem derived85239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2363) ∨ (¬ p 3923) ∨ (p 2307) ∨ (¬ p 5015) :=
  ElevenRUP.step85239 (p 2307) (p 2313) (p 2363) (p 3309) (p 3923) (p 4347) (p 5015) (derived73560 p h) (derived73238 p h) (derived53787 p h)

theorem derived85245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2850) ∨ (¬ p 4433) ∨ (¬ p 2598) ∨ (¬ p 3923) ∨ (¬ p 4733) ∨ (p 2307) ∨ (¬ p 2373) ∨ (¬ p 5015) :=
  ElevenRUP.step85245 (p 2307) (p 2313) (p 2373) (p 2598) (p 2850) (p 3309) (p 3923) (p 4433) (p 4733) (p 5015) (derived73238 p h) (derived51556 p h)

theorem derived85250 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3309) ∨ (p 2553) ∨ (¬ p 3093) :=
  ElevenRUP.step85250 (p 2553) (p 2588) (p 2608) (p 3093) (p 3309) (p 3954) (derived73498 p h) (derived73282 p h) (derived53566 p h)

theorem derived85252 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2122) :=
  ElevenRUP.step85252 (p 2122) (p 2608) (p 3093) (p 3309) (p 3822) (p 3954) (derived73498 p h) (derived73472 p h) (derived62948 p h)

theorem derived85253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2274) ∨ (p 2608) ∨ (¬ p 3093) :=
  ElevenRUP.step85253 (p 2274) (p 2608) (p 3093) (p 3097) (p 3309) (p 3954) (derived73352 p h) (derived73498 p h) (derived46878 p h)

theorem derived85254 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2274) ∨ (p 2608) ∨ (¬ p 2210) ∨ (¬ p 4338) :=
  ElevenRUP.step85254 (p 2210) (p 2274) (p 2608) (p 3097) (p 3309) (p 3954) (p 4338) (derived73352 p h) (derived73498 p h) (derived60218 p h)

theorem derived85255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3950) ∨ (p 2651) ∨ (¬ p 3093) ∨ (p 3083) ∨ (p 2528) ∨ (¬ p 2254) ∨ (¬ p 2396) :=
  ElevenRUP.step85255 (p 2254) (p 2396) (p 2528) (p 2534) (p 2651) (p 2657) (p 3083) (p 3093) (p 3309) (p 3950) (p 4256) (derived73288 p h) (derived73542 p h) (derived73268 p h) (derived48875 p h)

theorem derived85259 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3309) ∨ (¬ p 3204) ∨ (¬ p 4566) ∨ (p 2295) ∨ (¬ p 3987) :=
  ElevenRUP.step85259 (p 2295) (p 2946) (p 2952) (p 3204) (p 3309) (p 3568) (p 3987) (p 4566) (derived73330 p h) (derived73416 p h) (derived48196 p h)

theorem derived85261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4319) ∨ (¬ p 2528) ∨ (¬ p 2255) ∨ (p 2727) ∨ (¬ p 4438) ∨ (¬ p 2474) ∨ (¬ p 2177) ∨ (p 2088) ∨ (¬ p 2662) ∨ (¬ p 2331) :=
  ElevenRUP.step85261 (p 2088) (p 2177) (p 2255) (p 2331) (p 2474) (p 2528) (p 2662) (p 2727) (p 3309) (p 3857) (p 4111) (p 4319) (p 4438) (derived73518 p h) (derived73480 p h) (derived64098 p h)

theorem derived85262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3921) ∨ (¬ p 2662) ∨ (p 3389) ∨ (¬ p 3016) ∨ (¬ p 3923) :=
  ElevenRUP.step85262 (p 2662) (p 3016) (p 3309) (p 3389) (p 3540) (p 3921) (p 3923) (derived73402 p h) (derived47064 p h)

theorem derived85266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2505) ∨ (p 2274) ∨ (p 2406) ∨ (¬ p 2230) ∨ (¬ p 4079) :=
  ElevenRUP.step85266 (p 2230) (p 2274) (p 2406) (p 2505) (p 3097) (p 3238) (p 3309) (p 4079) (derived73352 p h) (derived73374 p h) (derived46973 p h)

theorem derived85272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 5015) ∨ (¬ p 4866) ∨ (¬ p 2608) ∨ (p 2307) :=
  ElevenRUP.step85272 (p 2307) (p 2313) (p 2608) (p 3309) (p 4866) (p 5015) (derived73238 p h) (derived48075 p h)

theorem derived85273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2274) ∨ (¬ p 2187) ∨ (¬ p 3093) :=
  ElevenRUP.step85273 (p 2187) (p 2274) (p 3093) (p 3097) (p 3309) (derived73352 p h) (derived59851 p h)

theorem derived85276 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (p 3256) ∨ (¬ p 4905) ∨ (¬ p 2177) ∨ (¬ p 3146) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 2254) :=
  ElevenRUP.step85276 (p 2177) (p 2254) (p 3093) (p 3146) (p 3166) (p 3172) (p 3256) (p 3309) (p 4118) (p 4905) (derived73356 p h) (derived73520 p h) (derived48870 p h)

theorem derived85280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2553) ∨ (p 2573) ∨ (¬ p 5191) ∨ (¬ p 2505) :=
  ElevenRUP.step85280 (p 2505) (p 2553) (p 2573) (p 2579) (p 2588) (p 3309) (p 5191) (derived73282 p h) (derived73274 p h) (derived47474 p h)

theorem derived85283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 4759) ∨ (¬ p 2241) ∨ (p 2449) :=
  ElevenRUP.step85283 (p 2241) (p 2396) (p 2449) (p 3309) (p 3947) (p 4759) (derived73494 p h) (derived43087 p h)

theorem derived85287 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3309) ∨ (¬ p 2311) ∨ (¬ p 5018) ∨ (¬ p 2177) :=
  ElevenRUP.step85287 (p 2177) (p 2311) (p 2341) (p 3309) (p 3551) (p 5018) (derived73408 p h) (derived41725 p h)

theorem derived85296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2264) ∨ (¬ p 4204) ∨ (¬ p 4155) ∨ (¬ p 4518) ∨ (¬ p 2312) ∨ (p 2881) :=
  ElevenRUP.step85296 (p 2264) (p 2312) (p 2881) (p 3309) (p 3570) (p 4155) (p 4204) (p 4518) (derived73418 p h) (derived60908 p h)

theorem derived85297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3309) ∨ (¬ p 4275) ∨ (¬ p 3093) ∨ (p 2685) ∨ (p 2264) ∨ (¬ p 4668) ∨ (p 2696) ∨ (¬ p 4736) :=
  ElevenRUP.step85297 (p 2264) (p 2685) (p 2696) (p 3093) (p 3246) (p 3309) (p 3365) (p 3553) (p 3572) (p 4275) (p 4668) (p 4736) (derived73420 p h) (derived73410 p h) (derived73390 p h) (derived60453 p h)

theorem derived85298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3309) ∨ (¬ p 4761) ∨ (p 2264) ∨ (¬ p 4067) ∨ (¬ p 2312) :=
  ElevenRUP.step85298 (p 2264) (p 2312) (p 2341) (p 3309) (p 3553) (p 4067) (p 4761) (derived73410 p h) (derived42488 p h)

theorem derived85300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2797) ∨ (¬ p 3366) ∨ (p 2630) ∨ (p 3379) ∨ (p 2331) ∨ (¬ p 4236) ∨ (¬ p 4376) ∨ (¬ p 3093) ∨ (p 2274) :=
  ElevenRUP.step85300 (p 2274) (p 2331) (p 2630) (p 2797) (p 2810) (p 2963) (p 3093) (p 3097) (p 3309) (p 3366) (p 3379) (p 3452) (p 4236) (p 4376) (derived73316 p h) (derived73394 p h) (derived73338 p h) (derived73352 p h) (derived58003 p h)

theorem derived85301 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2274) :=
  ElevenRUP.step85301 (p 2241) (p 2247) (p 2274) (p 3093) (p 3097) (p 3309) (derived73226 p h) (derived73352 p h) (derived46476 p h)

theorem derived85302 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3309) ∨ (¬ p 2177) ∨ (¬ p 3093) :=
  ElevenRUP.step85302 (p 2177) (p 2241) (p 2247) (p 3093) (p 3309) (derived73226 p h) (derived45442 p h)

theorem derived85303 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2307) :=
  ElevenRUP.step85303 (p 2241) (p 2247) (p 2307) (p 2313) (p 3093) (p 3309) (derived73226 p h) (derived73238 p h) (derived59915 p h)

theorem derived85305 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 3309) ∨ (¬ p 4319) ∨ (¬ p 4769) ∨ (¬ p 2331) :=
  ElevenRUP.step85305 (p 2331) (p 3166) (p 3172) (p 3309) (p 4319) (p 4769) (derived73356 p h) (derived71619 p h)

theorem derived85306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2177) ∨ (¬ p 5193) ∨ (¬ p 2850) ∨ (¬ p 3093) ∨ (¬ p 4438) ∨ (p 2230) ∨ (p 3641) :=
  ElevenRUP.step85306 (p 2177) (p 2230) (p 2589) (p 2850) (p 3093) (p 3309) (p 3641) (p 3874) (p 4438) (p 5193) (derived73284 p h) (derived73484 p h) (derived62817 p h)

theorem derived85307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 3073) ∨ (¬ p 4371) ∨ (¬ p 2363) :=
  ElevenRUP.step85307 (p 2363) (p 3073) (p 3309) (p 4261) (p 4371) (derived73544 p h) (derived71620 p h)

theorem derived85310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2331) ∨ (¬ p 4666) ∨ (p 3246) ∨ (¬ p 2177) ∨ (p 3051) ∨ (¬ p 2957) ∨ (¬ p 2255) ∨ (p 2992) ∨ (¬ p 4319) :=
  ElevenRUP.step85310 (p 2177) (p 2255) (p 2331) (p 2957) (p 2992) (p 3051) (p 3246) (p 3309) (p 3556) (p 3662) (p 3690) (p 4319) (p 4666) (derived73446 p h) (derived73414 p h) (derived73440 p h) (derived59138 p h)

theorem derived85312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2992) ∨ (p 2274) ∨ (¬ p 2946) ∨ (¬ p 4759) ∨ (¬ p 2253) :=
  ElevenRUP.step85312 (p 2253) (p 2274) (p 2946) (p 2992) (p 3097) (p 3309) (p 3662) (p 4759) (derived73440 p h) (derived73352 p h) (derived47217 p h)

theorem derived85313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2363) ∨ (¬ p 3325) ∨ (p 2459) :=
  ElevenRUP.step85313 (p 2363) (p 2459) (p 3093) (p 3309) (p 3325) (p 4348) (derived73562 p h) (derived56034 p h)

theorem derived85316 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3309) ∨ (p 3641) ∨ (¬ p 3950) ∨ (¬ p 3093) ∨ (¬ p 4736) ∨ (p 2598) ∨ (¬ p 2396) :=
  ElevenRUP.step85316 (p 2396) (p 2528) (p 2534) (p 2598) (p 3055) (p 3093) (p 3309) (p 3641) (p 3874) (p 3950) (p 4736) (derived73268 p h) (derived73484 p h) (derived73350 p h) (derived49622 p h)

theorem derived85321 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (p 3256) ∨ (¬ p 3918) ∨ (¬ p 2663) ∨ (p 3367) ∨ (¬ p 2774) ∨ (¬ p 3363) ∨ (¬ p 2396) ∨ (¬ p 3309) ∨ (¬ p 3950) :=
  ElevenRUP.step85321 (p 2396) (p 2663) (p 2774) (p 3166) (p 3172) (p 3256) (p 3309) (p 3363) (p 3367) (p 3585) (p 3918) (p 3950) (p 4118) (derived73356 p h) (derived73520 p h) (derived73428 p h) (derived71622 p h)

theorem derived85323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 3319) ∨ (¬ p 3125) ∨ (¬ p 2177) :=
  ElevenRUP.step85323 (p 2177) (p 3125) (p 3309) (p 3319) (p 4026) (derived73504 p h) (derived62811 p h)

theorem derived85327 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 3379) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3366) ∨ (¬ p 2685) ∨ (p 2807) ∨ (¬ p 4376) ∨ (¬ p 4236) ∨ (¬ p 4769) :=
  ElevenRUP.step85327 (p 2685) (p 2807) (p 3005) (p 3093) (p 3309) (p 3366) (p 3379) (p 3414) (p 3452) (p 3877) (p 4236) (p 4376) (p 4769) (derived73488 p h) (derived73394 p h) (derived73392 p h) (derived71623 p h)

theorem derived85328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 3016) ∨ (p 2307) ∨ (¬ p 2386) ∨ (¬ p 4814) ∨ (¬ p 2505) :=
  ElevenRUP.step85328 (p 2307) (p 2313) (p 2386) (p 2505) (p 3016) (p 3309) (p 3574) (p 4814) (derived73422 p h) (derived73238 p h) (derived62838 p h)

theorem derived85330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3319) ∨ (¬ p 4396) ∨ (¬ p 3309) ∨ (¬ p 4559) :=
  ElevenRUP.step85330 (p 3246) (p 3309) (p 3319) (p 4026) (p 4396) (p 4559) (derived73504 p h) (derived60189 p h)

theorem derived85331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 4319) ∨ (¬ p 3309) ∨ (¬ p 4826) ∨ (p 3276) ∨ (¬ p 2255) ∨ (¬ p 2331) ∨ (p 2727) ∨ (¬ p 3346) ∨ (¬ p 2662) :=
  ElevenRUP.step85331 (p 2255) (p 2331) (p 2662) (p 2727) (p 3276) (p 3309) (p 3346) (p 3791) (p 4111) (p 4319) (p 4425) (p 4826) (derived73578 p h) (derived73518 p h) (derived60342 p h)

theorem derived85333 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3461) ∨ (¬ p 4620) ∨ (¬ p 4430) ∨ (¬ p 3309) :=
  ElevenRUP.step85333 (p 3309) (p 3461) (p 3707) (p 4321) (p 4430) (p 4620) (derived73554 p h) (derived49078 p h)

theorem derived85339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2553) ∨ (¬ p 3093) ∨ (¬ p 2352) :=
  ElevenRUP.step85339 (p 2352) (p 2553) (p 2588) (p 3093) (p 3309) (derived73282 p h) (derived45408 p h)

theorem derived85342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3309) ∨ (p 3256) ∨ (¬ p 3361) ∨ (¬ p 2774) ∨ (¬ p 3950) ∨ (p 2737) ∨ (¬ p 3918) ∨ (p 3166) :=
  ElevenRUP.step85342 (p 2396) (p 2737) (p 2743) (p 2774) (p 3166) (p 3172) (p 3256) (p 3309) (p 3361) (p 3918) (p 3950) (p 4118) (derived73520 p h) (derived73298 p h) (derived73356 p h) (derived71624 p h)

theorem derived85345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 4736) ∨ (p 2911) ∨ (¬ p 4668) ∨ (p 3201) ∨ (¬ p 3093) ∨ (p 2598) :=
  ElevenRUP.step85345 (p 2396) (p 2598) (p 2911) (p 3055) (p 3093) (p 3201) (p 3309) (p 3644) (p 3876) (p 4668) (p 4736) (derived73434 p h) (derived73486 p h) (derived73350 p h) (derived51268 p h)

theorem derived85346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 3951) ∨ (¬ p 4736) ∨ (p 2982) ∨ (p 2850) ∨ (p 2598) ∨ (¬ p 3093) :=
  ElevenRUP.step85346 (p 2396) (p 2598) (p 2850) (p 2982) (p 3055) (p 3093) (p 3309) (p 3684) (p 3951) (p 4736) (p 4948) (derived73846 p h) (derived73442 p h) (derived73350 p h) (derived49594 p h)

theorem derived85348 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2383) ∨ (¬ p 4559) ∨ (p 2598) ∨ (p 2427) ∨ (¬ p 3923) ∨ (p 2850) ∨ (¬ p 4736) ∨ (¬ p 5020) :=
  ElevenRUP.step85348 (p 2383) (p 2427) (p 2598) (p 2850) (p 3055) (p 3309) (p 3684) (p 3923) (p 4235) (p 4559) (p 4736) (p 5020) (derived73350 p h) (derived73536 p h) (derived73442 p h) (derived57029 p h)

theorem derived85349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2417) ∨ (¬ p 4736) ∨ (¬ p 4666) ∨ (p 3201) ∨ (¬ p 2177) ∨ (¬ p 3093) ∨ (p 2598) :=
  ElevenRUP.step85349 (p 2177) (p 2417) (p 2598) (p 3055) (p 3093) (p 3201) (p 3309) (p 3876) (p 4278) (p 4666) (p 4736) (derived73546 p h) (derived73486 p h) (derived73350 p h) (derived61865 p h)

theorem derived85350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2417) ∨ (¬ p 2396) ∨ (¬ p 3093) :=
  ElevenRUP.step85350 (p 2396) (p 2417) (p 3093) (p 3309) (p 4278) (derived73546 p h) (derived43572 p h)

theorem derived85355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2553) ∨ (p 3379) :=
  ElevenRUP.step85355 (p 2553) (p 2588) (p 3093) (p 3309) (p 3379) (p 3452) (derived73282 p h) (derived73394 p h) (derived43348 p h)

theorem derived85361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2528) ∨ (¬ p 2177) ∨ (¬ p 4736) ∨ (p 2098) ∨ (¬ p 4438) ∨ (p 3609) :=
  ElevenRUP.step85361 (p 2098) (p 2104) (p 2177) (p 2528) (p 3093) (p 3309) (p 3609) (p 4340) (p 4438) (p 4736) (derived73204 p h) (derived73558 p h) (derived60113 p h)

theorem derived85363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2668) ∨ (¬ p 3923) ∨ (p 2274) :=
  ElevenRUP.step85363 (p 2274) (p 2668) (p 3097) (p 3309) (p 3923) (p 4560) (derived72955 p h) (derived73352 p h) (derived50672 p h)

theorem derived85366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 5015) ∨ (¬ p 2505) ∨ (¬ p 2608) ∨ (¬ p 4376) ∨ (p 2307) :=
  ElevenRUP.step85366 (p 2307) (p 2313) (p 2505) (p 2608) (p 3309) (p 4376) (p 5015) (derived73238 p h) (derived53487 p h)

theorem derived85375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 4592) :=
  ElevenRUP.step85375 (p 2341) (p 4589) (p 4592) (derived73654 p h) (h 7300)

theorem derived85378 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 4518) :=
  ElevenRUP.step85378 (p 2156) (p 3646) (p 4518) (derived73436 p h) (derived46069 p h)

theorem derived85379 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 4401) :=
  ElevenRUP.step85379 (p 2156) (p 3646) (p 4401) (derived73436 p h) (derived47395 p h)

theorem derived85380 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 4489) :=
  ElevenRUP.step85380 (p 2156) (p 3646) (p 4489) (derived73436 p h) (derived48273 p h)

theorem derived85382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2284) ∨ (¬ p 3246) ∨ (p 2156) :=
  ElevenRUP.step85382 (p 2156) (p 2284) (p 3051) (p 3246) (p 3646) (derived73436 p h) (derived46276 p h)

theorem derived85383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (¬ p 2881) ∨ (¬ p 2563) :=
  ElevenRUP.step85383 (p 2156) (p 2563) (p 2881) (p 3051) (p 3646) (derived73436 p h) (derived54943 p h)

theorem derived85384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2284) ∨ (p 2156) ∨ (¬ p 2881) :=
  ElevenRUP.step85384 (p 2156) (p 2284) (p 2881) (p 3051) (p 3646) (derived73436 p h) (derived57971 p h)

theorem derived85385 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4140) ∨ (p 2553) ∨ (p 2156) ∨ (¬ p 3958) :=
  ElevenRUP.step85385 (p 2156) (p 2553) (p 2588) (p 3051) (p 3646) (p 3958) (p 4140) (derived73282 p h) (derived73436 p h) (derived53078 p h)

theorem derived85386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4140) ∨ (p 2156) ∨ (¬ p 2177) ∨ (¬ p 2563) :=
  ElevenRUP.step85386 (p 2156) (p 2177) (p 2563) (p 3051) (p 3646) (p 4140) (derived73436 p h) (derived61941 p h)

theorem derived85387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2156) ∨ (¬ p 2881) ∨ (¬ p 3645) ∨ (¬ p 2563) :=
  ElevenRUP.step85387 (p 2156) (p 2563) (p 2881) (p 2891) (p 3645) (p 3646) (derived73436 p h) (derived54942 p h)

theorem derived85388 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2396) ∨ (¬ p 3645) ∨ (p 2274) ∨ (p 2156) ∨ (¬ p 4877) ∨ (¬ p 3399) ∨ (¬ p 4666) ∨ (¬ p 3037) ∨ (¬ p 2264) :=
  ElevenRUP.step85388 (p 2156) (p 2264) (p 2274) (p 2396) (p 2608) (p 3037) (p 3097) (p 3399) (p 3645) (p 3646) (p 3954) (p 4107) (p 4666) (p 4877) (derived73498 p h) (derived73514 p h) (derived73352 p h) (derived73436 p h) (derived62242 p h)

theorem derived85389 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2427) ∨ (¬ p 3904) ∨ (¬ p 2563) ∨ (p 2156) :=
  ElevenRUP.step85389 (p 2156) (p 2427) (p 2563) (p 3246) (p 3646) (p 3690) (p 3904) (p 4235) (derived73446 p h) (derived73536 p h) (derived73436 p h) (derived62769 p h)

theorem derived85390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 3246) ∨ (¬ p 4558) ∨ (¬ p 4988) ∨ (p 2156) :=
  ElevenRUP.step85390 (p 2156) (p 3246) (p 3516) (p 3646) (p 3690) (p 4558) (p 4988) (derived73446 p h) (derived73436 p h) (derived62280 p h)

theorem derived85391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4441) ∨ (p 2156) ∨ (¬ p 2363) ∨ (¬ p 2563) ∨ (¬ p 2220) :=
  ElevenRUP.step85391 (p 2156) (p 2220) (p 2363) (p 2563) (p 3646) (p 4441) (derived73436 p h) (derived52293 p h)

theorem derived85394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4140) ∨ (p 2553) ∨ (¬ p 2220) ∨ (p 2156) ∨ (¬ p 4119) ∨ (¬ p 3958) :=
  ElevenRUP.step85394 (p 2156) (p 2220) (p 2553) (p 2588) (p 3646) (p 3958) (p 4119) (p 4140) (derived73282 p h) (derived73436 p h) (derived59154 p h)

theorem derived85395 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 3461) ∨ (p 2156) ∨ (p 3125) :=
  ElevenRUP.step85395 (p 2156) (p 3051) (p 3125) (p 3461) (p 3646) (p 3744) (p 4191) (derived73530 p h) (derived73436 p h) (derived73454 p h) (derived45155 p h)

theorem derived85396 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 2839) ∨ (¬ p 2143) ∨ (¬ p 2563) ∨ (p 2156) :=
  ElevenRUP.step85396 (p 2143) (p 2156) (p 2563) (p 2839) (p 3367) (p 3583) (p 3646) (derived73424 p h) (derived73436 p h) (derived45384 p h)

theorem derived85398 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3125) ∨ (¬ p 2143) ∨ (p 2839) ∨ (p 2156) :=
  ElevenRUP.step85398 (p 2143) (p 2156) (p 2839) (p 3125) (p 3461) (p 3583) (p 3646) (p 3744) (p 4191) (derived73530 p h) (derived73454 p h) (derived73424 p h) (derived73436 p h) (derived43858 p h)

theorem derived85399 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2220) ∨ (p 2274) ∨ (p 2396) :=
  ElevenRUP.step85399 (p 2156) (p 2220) (p 2274) (p 2396) (p 3097) (p 3646) (p 4107) (derived73436 p h) (derived73352 p h) (derived73514 p h) (derived43851 p h)

theorem derived85401 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2396) ∨ (¬ p 2860) ∨ (¬ p 4275) ∨ (p 2156) :=
  ElevenRUP.step85401 (p 2156) (p 2396) (p 2860) (p 2870) (p 3646) (p 4107) (p 4244) (p 4275) (derived73540 p h) (derived73514 p h) (derived73436 p h) (derived53109 p h)

theorem derived85405 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (p 2363) ∨ (p 2187) :=
  ElevenRUP.step85405 (p 2156) (p 2187) (p 2220) (p 2363) (p 3646) (p 3989) (p 4347) (derived73436 p h) (derived73560 p h) (derived73502 p h) (derived53199 p h)

theorem derived85406 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2156) ∨ (p 2187) ∨ (¬ p 4533) ∨ (¬ p 3660) :=
  ElevenRUP.step85406 (p 2156) (p 2187) (p 2352) (p 3646) (p 3660) (p 3989) (p 4533) (derived73436 p h) (derived73502 p h) (derived40917 p h)

theorem derived85407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2396) ∨ (¬ p 4988) ∨ (p 2156) ∨ (¬ p 2563) :=
  ElevenRUP.step85407 (p 2156) (p 2396) (p 2563) (p 3516) (p 3646) (p 4107) (p 4988) (derived73514 p h) (derived73436 p h) (derived45646 p h)

theorem derived85408 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 2992) ∨ (p 2156) ∨ (¬ p 2957) ∨ (p 2274) :=
  ElevenRUP.step85408 (p 2156) (p 2274) (p 2396) (p 2957) (p 2992) (p 3097) (p 3646) (p 3662) (p 4107) (derived73514 p h) (derived73440 p h) (derived73436 p h) (derived73352 p h) (derived43800 p h)

theorem derived85410 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 2274) ∨ (¬ p 2957) ∨ (p 2156) ∨ (p 3136) :=
  ElevenRUP.step85410 (p 2156) (p 2274) (p 2396) (p 2957) (p 3097) (p 3136) (p 3646) (p 4107) (p 4315) (derived73514 p h) (derived73352 p h) (derived73436 p h) (derived73550 p h) (derived43803 p h)

theorem derived85412 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2284) ∨ (p 3156) ∨ (p 2156) ∨ (¬ p 4506) :=
  ElevenRUP.step85412 (p 2156) (p 2284) (p 2363) (p 3156) (p 3497) (p 3646) (p 4347) (p 4506) (derived73560 p h) (derived73400 p h) (derived73436 p h) (derived45284 p h)

theorem derived85413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 2220) ∨ (p 2156) ∨ (¬ p 2284) :=
  ElevenRUP.step85413 (p 2156) (p 2220) (p 2284) (p 3646) (p 3969) (derived73436 p h) (derived46277 p h)

theorem derived85416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2192) ∨ (p 2156) ∨ (p 2177) ∨ (¬ p 4988) :=
  ElevenRUP.step85416 (p 2156) (p 2177) (p 2192) (p 2299) (p 2341) (p 3646) (p 4988) (derived73436 p h) (derived73234 p h) (derived46388 p h)

theorem derived85419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (p 2274) ∨ (¬ p 4405) ∨ (¬ p 4441) :=
  ElevenRUP.step85419 (p 2156) (p 2220) (p 2274) (p 3097) (p 3646) (p 4405) (p 4441) (derived73436 p h) (derived73352 p h) (derived42531 p h)

theorem derived85421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 2363) ∨ (¬ p 3950) ∨ (¬ p 2707) ∨ (p 2156) ∨ (¬ p 3434) ∨ (p 2187) :=
  ElevenRUP.step85421 (p 2156) (p 2187) (p 2363) (p 2608) (p 2707) (p 3434) (p 3646) (p 3950) (p 3989) (p 4347) (p 4524) (derived73560 p h) (derived72962 p h) (derived73436 p h) (derived73502 p h) (derived63956 p h)

theorem derived85424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2396) ∨ (¬ p 2563) ∨ (p 2156) ∨ (¬ p 4140) :=
  ElevenRUP.step85424 (p 2156) (p 2396) (p 2563) (p 3051) (p 3646) (p 4140) (derived73436 p h) (derived54932 p h)

theorem derived85425 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (¬ p 3246) ∨ (¬ p 2563) :=
  ElevenRUP.step85425 (p 2156) (p 2563) (p 3051) (p 3246) (p 3646) (derived73436 p h) (derived53674 p h)

theorem derived85437 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4031) ∨ (p 2156) ∨ (¬ p 2440) ∨ (p 2187) :=
  ElevenRUP.step85437 (p 2156) (p 2187) (p 2363) (p 2440) (p 3646) (p 3989) (p 4031) (p 4347) (derived73560 p h) (derived73436 p h) (derived73502 p h) (derived45124 p h)

theorem derived85438 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (¬ p 5045) ∨ (p 2274) ∨ (p 2156) ∨ (¬ p 4624) :=
  ElevenRUP.step85438 (p 2156) (p 2274) (p 3097) (p 3212) (p 3646) (p 4624) (p 5045) (derived73352 p h) (derived73436 p h) (derived51261 p h)

theorem derived85441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2284) ∨ (p 2156) ∨ (p 2427) :=
  ElevenRUP.step85441 (p 2156) (p 2284) (p 2427) (p 3051) (p 3646) (p 4235) (derived73436 p h) (derived73536 p h) (derived46133 p h)

theorem derived85443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (p 2373) ∨ (¬ p 2284) ∨ (¬ p 4705) :=
  ElevenRUP.step85443 (p 2156) (p 2220) (p 2284) (p 2373) (p 3646) (p 3880) (p 4705) (derived73436 p h) (derived73490 p h) (derived63320 p h)

theorem derived85444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3051) ∨ (p 2156) ∨ (¬ p 2459) :=
  ElevenRUP.step85444 (p 2156) (p 2459) (p 2881) (p 3051) (p 3646) (derived73436 p h) (derived45511 p h)

theorem derived85445 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (¬ p 2563) ∨ (p 2177) ∨ (¬ p 4042) :=
  ElevenRUP.step85445 (p 2156) (p 2177) (p 2220) (p 2299) (p 2563) (p 3646) (p 4042) (derived73436 p h) (derived73234 p h) (derived47088 p h)

theorem derived85449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2156) ∨ (¬ p 2563) ∨ (¬ p 4646) ∨ (¬ p 3904) :=
  ElevenRUP.step85449 (p 2156) (p 2563) (p 3389) (p 3646) (p 3904) (p 4646) (derived73436 p h) (derived41336 p h)

theorem derived85451 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2850) ∨ (¬ p 2563) ∨ (¬ p 3904) :=
  ElevenRUP.step85451 (p 2156) (p 2563) (p 2850) (p 3646) (p 3904) (derived73436 p h) (derived71627 p h)

theorem derived85453 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2950) ∨ (p 2737) ∨ (¬ p 3361) ∨ (p 2156) ∨ (¬ p 2284) :=
  ElevenRUP.step85453 (p 2156) (p 2284) (p 2737) (p 2743) (p 2950) (p 3156) (p 3361) (p 3497) (p 3646) (derived73400 p h) (derived73298 p h) (derived73436 p h) (derived54028 p h)

theorem derived85454 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (p 2363) ∨ (p 2187) ∨ (p 2156) ∨ (p 2839) :=
  ElevenRUP.step85454 (p 2143) (p 2156) (p 2187) (p 2363) (p 2839) (p 3583) (p 3646) (p 3989) (p 4347) (derived73560 p h) (derived73502 p h) (derived73436 p h) (derived73424 p h) (derived43799 p h)

theorem derived85457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2737) ∨ (p 2839) ∨ (p 2156) ∨ (¬ p 2143) :=
  ElevenRUP.step85457 (p 2143) (p 2156) (p 2284) (p 2737) (p 2839) (p 3583) (p 3646) (derived73424 p h) (derived73436 p h) (derived45929 p h)

theorem derived85458 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 2881) ∨ (¬ p 2177) ∨ (p 2156) ∨ (¬ p 4204) ∨ (¬ p 2143) :=
  ElevenRUP.step85458 (p 2143) (p 2156) (p 2177) (p 2839) (p 2881) (p 3570) (p 3583) (p 3646) (p 4204) (derived73424 p h) (derived73418 p h) (derived73436 p h) (derived50296 p h)

theorem derived85462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3125) ∨ (p 2122) ∨ (p 2156) :=
  ElevenRUP.step85462 (p 2122) (p 2156) (p 3125) (p 3483) (p 3646) (p 3744) (p 3822) (derived73454 p h) (derived73472 p h) (derived73436 p h) (derived61620 p h)

theorem derived85464 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (p 2274) ∨ (p 2156) ∨ (p 2177) ∨ (p 3136) :=
  ElevenRUP.step85464 (p 2156) (p 2177) (p 2274) (p 2299) (p 2957) (p 3097) (p 3136) (p 3646) (p 4315) (derived73352 p h) (derived73436 p h) (derived73234 p h) (derived73550 p h) (derived47628 p h)

theorem derived85467 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 2156) ∨ (¬ p 2143) ∨ (p 2177) ∨ (p 2274) :=
  ElevenRUP.step85467 (p 2143) (p 2156) (p 2177) (p 2274) (p 2299) (p 2839) (p 3097) (p 3583) (p 3646) (derived73424 p h) (derived73436 p h) (derived73234 p h) (derived73352 p h) (derived43849 p h)

theorem derived85470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (¬ p 2341) ∨ (¬ p 4558) ∨ (p 2881) ∨ (p 2156) :=
  ElevenRUP.step85470 (p 2156) (p 2341) (p 2881) (p 3570) (p 3646) (p 4558) (p 4988) (derived73418 p h) (derived73436 p h) (derived52565 p h)

theorem derived85475 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 3125) ∨ (¬ p 4140) ∨ (p 2156) ∨ (¬ p 4620) :=
  ElevenRUP.step85475 (p 2156) (p 3051) (p 3125) (p 3646) (p 3744) (p 4140) (p 4620) (derived73454 p h) (derived73436 p h) (derived41348 p h)

theorem derived85476 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2136) ∨ (p 2187) ∨ (p 2156) ∨ (¬ p 2459) :=
  ElevenRUP.step85476 (p 2136) (p 2156) (p 2187) (p 2363) (p 2459) (p 3646) (p 3989) (p 4347) (derived73560 p h) (derived73502 p h) (derived73436 p h) (derived58719 p h)

theorem derived85479 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3136) ∨ (p 2156) ∨ (p 2132) :=
  ElevenRUP.step85479 (p 2132) (p 2138) (p 2156) (p 2284) (p 3136) (p 3646) (p 5050) (derived73894 p h) (derived73436 p h) (derived73214 p h) (derived66786 p h)

theorem derived85480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3985) ∨ (¬ p 2140) ∨ (p 2156) ∨ (p 2274) :=
  ElevenRUP.step85480 (p 2122) (p 2140) (p 2156) (p 2274) (p 3097) (p 3646) (p 3985) (derived73436 p h) (derived73352 p h) (derived50858 p h)

theorem derived85481 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (p 2156) ∨ (¬ p 2563) ∨ (¬ p 4953) ∨ (¬ p 3904) :=
  ElevenRUP.step85481 (p 2156) (p 2563) (p 3355) (p 3646) (p 3904) (p 4953) (derived73436 p h) (derived41693 p h)

theorem derived85485 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 2440) ∨ (¬ p 2563) ∨ (¬ p 2659) ∨ (¬ p 3904) :=
  ElevenRUP.step85485 (p 2156) (p 2440) (p 2542) (p 2563) (p 2659) (p 3646) (p 3904) (derived73436 p h) (derived73270 p h) (derived41572 p h)

theorem derived85486 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 2156) ∨ (¬ p 4750) ∨ (¬ p 2563) ∨ (¬ p 3904) ∨ (¬ p 3363) :=
  ElevenRUP.step85486 (p 2156) (p 2440) (p 2542) (p 2563) (p 3363) (p 3646) (p 3904) (p 4750) (derived73270 p h) (derived73436 p h) (derived49794 p h)

theorem derived85487 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 2156) ∨ (¬ p 4033) ∨ (¬ p 2563) ∨ (p 3461) :=
  ElevenRUP.step85487 (p 2156) (p 2563) (p 2982) (p 3461) (p 3646) (p 4033) (p 4191) (p 4948) (derived73846 p h) (derived73436 p h) (derived73530 p h) (derived57600 p h)

theorem derived85491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2230) ∨ (p 2156) ∨ (¬ p 5190) ∨ (¬ p 3369) :=
  ElevenRUP.step85491 (p 2156) (p 2230) (p 2563) (p 3369) (p 3646) (p 5190) (derived73436 p h) (derived41218 p h)

theorem derived85492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3680) ∨ (¬ p 4031) ∨ (p 2156) ∨ (¬ p 2982) :=
  ElevenRUP.step85492 (p 2156) (p 2284) (p 2982) (p 3646) (p 3680) (p 4031) (derived73436 p h) (derived46275 p h)

theorem derived85493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3125) ∨ (p 2668) ∨ (p 2156) :=
  ElevenRUP.step85493 (p 2156) (p 2668) (p 3125) (p 3323) (p 3324) (p 3646) (p 3744) (derived73454 p h) (derived73386 p h) (derived73436 p h) (derived60051 p h)

theorem derived85495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4336) ∨ (¬ p 3323) ∨ (¬ p 4957) ∨ (p 2156) ∨ (p 3125) ∨ (¬ p 3645) :=
  ElevenRUP.step85495 (p 2156) (p 3125) (p 3323) (p 3645) (p 3646) (p 3744) (p 4336) (p 4957) (derived73436 p h) (derived73454 p h) (derived42208 p h)

theorem derived85500 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 3461) ∨ (p 2156) ∨ (p 3125) ∨ (¬ p 2957) :=
  ElevenRUP.step85500 (p 2156) (p 2957) (p 2992) (p 3125) (p 3461) (p 3646) (p 3662) (p 3744) (p 4191) (derived73440 p h) (derived73530 p h) (derived73436 p h) (derived73454 p h) (derived57460 p h)

theorem derived85502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4075) ∨ (p 2608) ∨ (p 3125) ∨ (p 3461) ∨ (¬ p 3399) ∨ (p 2156) ∨ (¬ p 4877) ∨ (¬ p 4826) ∨ (¬ p 3645) :=
  ElevenRUP.step85502 (p 2156) (p 2608) (p 3125) (p 3399) (p 3461) (p 3645) (p 3646) (p 3744) (p 3954) (p 4075) (p 4191) (p 4826) (p 4877) (derived73498 p h) (derived73454 p h) (derived73530 p h) (derived73436 p h) (derived58422 p h)

theorem derived85503 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 2957) ∨ (p 3125) ∨ (p 3136) ∨ (p 2156) :=
  ElevenRUP.step85503 (p 2156) (p 2957) (p 3125) (p 3136) (p 3461) (p 3646) (p 3744) (p 4191) (p 4315) (derived73530 p h) (derived73454 p h) (derived73550 p h) (derived73436 p h) (derived57290 p h)

theorem derived85504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (p 3461) ∨ (p 3125) ∨ (¬ p 2098) ∨ (¬ p 2748) ∨ (¬ p 2252) ∨ (¬ p 2950) ∨ (¬ p 5119) ∨ (p 2156) ∨ (p 2598) ∨ (¬ p 4749) :=
  ElevenRUP.step85504 (p 2098) (p 2156) (p 2252) (p 2598) (p 2748) (p 2950) (p 3055) (p 3125) (p 3461) (p 3646) (p 3744) (p 4019) (p 4191) (p 4749) (p 5119) (derived73530 p h) (derived73454 p h) (derived73436 p h) (derived73350 p h) (derived42159 p h)

theorem derived85507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3286) ∨ (¬ p 2284) ∨ (p 2156) ∨ (¬ p 2950) ∨ (¬ p 5039) :=
  ElevenRUP.step85507 (p 2156) (p 2284) (p 2950) (p 3286) (p 3646) (p 5039) (derived73436 p h) (derived58906 p h)

theorem derived85516 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2901) ∨ (¬ p 3527) ∨ (¬ p 2950) ∨ (p 2156) ∨ (¬ p 2254) ∨ (p 2911) ∨ (¬ p 3399) ∨ (¬ p 4277) :=
  ElevenRUP.step85516 (p 2156) (p 2254) (p 2284) (p 2901) (p 2911) (p 2950) (p 3399) (p 3527) (p 3644) (p 3646) (p 4277) (p 4320) (derived73552 p h) (derived73436 p h) (derived73434 p h) (derived62374 p h)

theorem derived85517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2707) ∨ (p 2156) ∨ (p 3156) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (¬ p 2950) ∨ (¬ p 2717) ∨ (¬ p 4905) :=
  ElevenRUP.step85517 (p 2156) (p 2254) (p 2284) (p 2608) (p 2707) (p 2717) (p 2950) (p 3156) (p 3497) (p 3646) (p 4905) (derived73436 p h) (derived73400 p h) (derived55537 p h)

theorem derived85518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2950) ∨ (¬ p 4652) ∨ (¬ p 3413) ∨ (p 2156) ∨ (¬ p 2807) :=
  ElevenRUP.step85518 (p 2156) (p 2284) (p 2807) (p 2950) (p 3413) (p 3646) (p 4652) (derived73436 p h) (derived42258 p h)

theorem derived85520 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 2156) ∨ (¬ p 3904) ∨ (¬ p 2563) ∨ (¬ p 4322) :=
  ElevenRUP.step85520 (p 2156) (p 2563) (p 2982) (p 3646) (p 3904) (p 4322) (p 4948) (derived73846 p h) (derived73436 p h) (derived47470 p h)

theorem derived85525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3872) ∨ (¬ p 3413) ∨ (p 2573) ∨ (¬ p 2284) ∨ (¬ p 4705) ∨ (p 2440) ∨ (¬ p 3016) ∨ (¬ p 2911) ∨ (¬ p 2659) ∨ (p 2156) :=
  ElevenRUP.step85525 (p 2156) (p 2284) (p 2440) (p 2542) (p 2573) (p 2579) (p 2659) (p 2911) (p 3016) (p 3413) (p 3646) (p 3872) (p 4705) (derived73274 p h) (derived73270 p h) (derived73436 p h) (derived65915 p h)

theorem derived85526 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 4031) ∨ (¬ p 2440) ∨ (p 3125) ∨ (p 2156) :=
  ElevenRUP.step85526 (p 2156) (p 2440) (p 3125) (p 3461) (p 3646) (p 3744) (p 4031) (p 4191) (derived73530 p h) (derived73454 p h) (derived73436 p h) (derived61344 p h)

theorem derived85539 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2331) ∨ (¬ p 2651) ∨ (p 2156) :=
  ElevenRUP.step85539 (p 2156) (p 2331) (p 2651) (p 2946) (p 2949) (p 3646) (derived73328 p h) (derived73436 p h) (derived69653 p h)

theorem derived85541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2911) ∨ (p 2156) ∨ (¬ p 2881) :=
  ElevenRUP.step85541 (p 2156) (p 2881) (p 2911) (p 3051) (p 3644) (p 3646) (derived73434 p h) (derived73436 p h) (derived60010 p h)

theorem derived85542 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 3146) ∨ (p 2156) ∨ (¬ p 2957) ∨ (¬ p 2363) ∨ (¬ p 3988) :=
  ElevenRUP.step85542 (p 2156) (p 2363) (p 2957) (p 2992) (p 3146) (p 3646) (p 3662) (p 3692) (p 3988) (derived73440 p h) (derived73448 p h) (derived73436 p h) (derived49178 p h)

theorem derived85543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3657) ∨ (¬ p 3366) ∨ (p 3146) ∨ (¬ p 2363) ∨ (¬ p 3988) ∨ (¬ p 2651) ∨ (p 2156) ∨ (¬ p 2437) ∨ (¬ p 2417) ∨ (¬ p 4503) ∨ (¬ p 2136) ∨ (¬ p 2246) ∨ (¬ p 2744) :=
  ElevenRUP.step85543 (p 2136) (p 2156) (p 2246) (p 2363) (p 2417) (p 2437) (p 2651) (p 2744) (p 3146) (p 3366) (p 3646) (p 3657) (p 3692) (p 3988) (p 4503) (derived73448 p h) (derived73436 p h) (derived63744 p h)

theorem derived85544 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2992) ∨ (p 2187) ∨ (¬ p 2957) ∨ (p 2156) :=
  ElevenRUP.step85544 (p 2156) (p 2187) (p 2363) (p 2957) (p 2992) (p 3646) (p 3662) (p 3989) (p 4347) (derived73560 p h) (derived73440 p h) (derived73502 p h) (derived73436 p h) (derived43834 p h)

theorem derived85546 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2957) ∨ (p 3136) ∨ (p 2187) ∨ (p 2156) :=
  ElevenRUP.step85546 (p 2156) (p 2187) (p 2363) (p 2957) (p 3136) (p 3646) (p 3989) (p 4315) (p 4347) (derived73560 p h) (derived73550 p h) (derived73502 p h) (derived73436 p h) (derived48932 p h)

theorem derived85553 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3276) ∨ (¬ p 3951) ∨ (¬ p 2145) ∨ (¬ p 3362) ∨ (p 2156) ∨ (p 3115) ∨ (¬ p 2284) ∨ (¬ p 3355) :=
  ElevenRUP.step85553 (p 2145) (p 2156) (p 2284) (p 2761) (p 3115) (p 3276) (p 3355) (p 3362) (p 3646) (p 3951) (p 4208) (p 4381) (derived73574 p h) (derived73436 p h) (derived73534 p h) (derived56797 p h)

theorem derived85554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4441) ∨ (p 2156) ∨ (¬ p 2220) ∨ (p 2553) ∨ (¬ p 4203) ∨ (¬ p 4405) :=
  ElevenRUP.step85554 (p 2156) (p 2220) (p 2553) (p 2588) (p 3646) (p 4203) (p 4405) (p 4441) (derived73436 p h) (derived73282 p h) (derived48815 p h)

theorem derived85556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (¬ p 5045) ∨ (¬ p 2563) ∨ (p 2156) ∨ (¬ p 3461) :=
  ElevenRUP.step85556 (p 2156) (p 2563) (p 3212) (p 3461) (p 3646) (p 5045) (derived73436 p h) (derived45748 p h)

theorem derived85558 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (¬ p 4322) ∨ (¬ p 4202) ∨ (¬ p 4752) ∨ (¬ p 4625) ∨ (¬ p 3434) ∨ (¬ p 3645) ∨ (p 2156) ∨ (¬ p 4030) ∨ (¬ p 3461) ∨ (¬ p 4205) ∨ (p 2696) :=
  ElevenRUP.step85558 (p 2156) (p 2696) (p 3365) (p 3425) (p 3434) (p 3461) (p 3471) (p 3645) (p 3646) (p 4030) (p 4202) (p 4205) (p 4322) (p 4625) (p 4752) (derived73396 p h) (derived73436 p h) (derived73390 p h) (derived63724 p h)

theorem derived85562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3136) ∨ (¬ p 2950) ∨ (p 2156) :=
  ElevenRUP.step85562 (p 2156) (p 2284) (p 2950) (p 3136) (p 3646) (derived73436 p h) (derived71634 p h)

theorem derived85568 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 2246) ∨ (¬ p 4959) ∨ (¬ p 3941) ∨ (¬ p 3645) ∨ (p 3125) ∨ (¬ p 5119) ∨ (p 2156) ∨ (¬ p 2807) ∨ (¬ p 2264) :=
  ElevenRUP.step85568 (p 2156) (p 2246) (p 2264) (p 2807) (p 3125) (p 3461) (p 3645) (p 3646) (p 3744) (p 3941) (p 4191) (p 4959) (p 5119) (derived73530 p h) (derived73454 p h) (derived73436 p h) (derived61500 p h)

theorem derived85569 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4333) ∨ (p 2264) ∨ (¬ p 4988) ∨ (p 2156) ∨ (¬ p 4558) :=
  ElevenRUP.step85569 (p 2156) (p 2264) (p 2341) (p 3553) (p 3646) (p 4333) (p 4558) (p 4988) (derived73410 p h) (derived73436 p h) (derived59303 p h)

theorem derived85573 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 2274) ∨ (¬ p 4666) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 2911) ∨ (p 2156) :=
  ElevenRUP.step85573 (p 2156) (p 2274) (p 2396) (p 2911) (p 2922) (p 3097) (p 3379) (p 3646) (p 4107) (p 4524) (p 4666) (derived73514 p h) (derived73352 p h) (derived72962 p h) (derived73436 p h) (derived54913 p h)

theorem derived85587 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 2274) ∨ (¬ p 3546) ∨ (¬ p 4105) ∨ (¬ p 3922) ∨ (¬ p 4564) ∨ (¬ p 2177) :=
  ElevenRUP.step85587 (p 2177) (p 2274) (p 2341) (p 3546) (p 3551) (p 3922) (p 4105) (p 4564) (derived73408 p h) (derived51850 p h)

theorem derived85589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3527) ∨ (¬ p 2312) ∨ (¬ p 2274) ∨ (¬ p 4514) ∨ (¬ p 4105) :=
  ElevenRUP.step85589 (p 2274) (p 2312) (p 2341) (p 3527) (p 3548) (p 4105) (p 4514) (derived73404 p h) (derived54550 p h)

theorem derived85599 (p : Nat → Prop) (h : Inputs p) :
    (p 4319) ∨ (p 2641) :=
  ElevenRUP.step85599 (p 2641) (p 4319) (p 5893) (derived74197 p h) (h 12346)

theorem derived85610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4319) ∨ (¬ p 3309) ∨ (¬ p 2667) ∨ (p 2307) :=
  ElevenRUP.step85610 (p 2307) (p 2313) (p 2667) (p 3309) (p 3549) (p 4319) (derived73405 p h) (derived73238 p h) (h 33739)

theorem derived85625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3412) ∨ (p 2284) ∨ (¬ p 4516) ∨ (¬ p 4338) :=
  ElevenRUP.step85625 (p 2284) (p 3412) (p 3952) (p 4338) (p 4516) (derived73496 p h) (h 19493)

theorem derived85627 (p : Nat → Prop) (h : Inputs p) :
    (p 3309) ∨ (¬ p 2274) ∨ (¬ p 4516) :=
  ElevenRUP.step85627 (p 2274) (p 3309) (p 3549) (p 4516) (derived73406 p h) (h 25006)

theorem derived85633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 3309) ∨ (¬ p 2962) ∨ (p 2220) ∨ (¬ p 4516) :=
  ElevenRUP.step85633 (p 2220) (p 2307) (p 2962) (p 3309) (p 3549) (p 4120) (p 4516) (derived73406 p h) (derived73522 p h) (derived69504 p h)

theorem derived85635 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 3645) ∨ (¬ p 4431) ∨ (¬ p 3571) :=
  ElevenRUP.step85635 (p 3051) (p 3556) (p 3571) (p 3645) (p 4431) (derived73414 p h) (h 13537)

theorem derived85636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3389) ∨ (¬ p 2246) ∨ (¬ p 4874) ∨ (¬ p 4332) ∨ (¬ p 2744) ∨ (¬ p 2663) ∨ (¬ p 3645) ∨ (p 2156) ∨ (p 2363) ∨ (p 2437) ∨ (p 2187) :=
  ElevenRUP.step85636 (p 2156) (p 2187) (p 2246) (p 2363) (p 2437) (p 2663) (p 2744) (p 3343) (p 3389) (p 3645) (p 3646) (p 3742) (p 3989) (p 4332) (p 4347) (p 4874) (derived73436 p h) (derived73560 p h) (derived73452 p h) (derived73502 p h) (derived57004 p h)

theorem derived85638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2156) ∨ (¬ p 3645) :=
  ElevenRUP.step85638 (p 2156) (p 2192) (p 3645) (p 3646) (derived73436 p h) (h 5323)

theorem derived85643 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 4032) ∨ (¬ p 2761) ∨ (¬ p 3519) ∨ (¬ p 3323) ∨ (¬ p 4621) ∨ (¬ p 3645) ∨ (¬ p 4376) ∨ (¬ p 2584) ∨ (¬ p 4874) :=
  ElevenRUP.step85643 (p 2383) (p 2584) (p 2668) (p 2761) (p 3323) (p 3324) (p 3519) (p 3645) (p 4032) (p 4322) (p 4376) (p 4621) (p 4874) (derived73386 p h) (derived59453 p h)

theorem derived85649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4967) ∨ (¬ p 3366) ∨ (¬ p 2563) ∨ (¬ p 3256) ∨ (p 2156) ∨ (¬ p 5059) ∨ (¬ p 4202) ∨ (¬ p 3537) ∨ (¬ p 4030) ∨ (¬ p 3645) ∨ (¬ p 4752) ∨ (p 2982) ∨ (p 2696) :=
  ElevenRUP.step85649 (p 2156) (p 2563) (p 2696) (p 2982) (p 3256) (p 3365) (p 3366) (p 3537) (p 3645) (p 3646) (p 4030) (p 4202) (p 4752) (p 4948) (p 4967) (p 5059) (derived73436 p h) (derived73846 p h) (derived73390 p h) (derived63723 p h)

theorem derived85651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 3888) ∨ (p 2220) ∨ (¬ p 2651) ∨ (p 3266) ∨ (¬ p 5250) ∨ (¬ p 3016) ∨ (p 3146) ∨ (¬ p 4877) ∨ (¬ p 3645) ∨ (¬ p 2749) :=
  ElevenRUP.step85651 (p 2220) (p 2246) (p 2651) (p 2749) (p 3016) (p 3146) (p 3266) (p 3645) (p 3692) (p 3888) (p 4120) (p 4444) (p 4877) (p 5250) (derived73522 p h) (derived73580 p h) (derived73448 p h) (derived62238 p h)

theorem derived85659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3979) ∨ (p 2220) ∨ (¬ p 2563) ∨ (¬ p 3645) ∨ (¬ p 4210) :=
  ElevenRUP.step85659 (p 2220) (p 2563) (p 3645) (p 3979) (p 4120) (p 4210) (p 5568) (derived73522 p h) (derived45148 p h)

theorem derived85660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 5123) ∨ (¬ p 3645) ∨ (p 2156) ∨ (¬ p 2246) ∨ (¬ p 4877) ∨ (¬ p 3333) ∨ (p 2187) ∨ (¬ p 2651) ∨ (¬ p 2749) ∨ (¬ p 4343) ∨ (¬ p 3276) :=
  ElevenRUP.step85660 (p 2156) (p 2187) (p 2246) (p 2651) (p 2749) (p 3276) (p 3333) (p 3645) (p 3646) (p 3989) (p 4343) (p 4877) (p 5123) (p 5580) (derived73436 p h) (derived73502 p h) (derived50803 p h)

theorem derived85669 (p : Nat → Prop) (h : Inputs p) :
    (p 4432) ∨ (p 2352) :=
  ElevenRUP.step85669 (p 2352) (p 4432) (p 5833) (derived74121 p h) (h 11991)

theorem derived85673 (p : Nat → Prop) (h : Inputs p) :
    (p 4383) ∨ (p 2911) :=
  ElevenRUP.step85673 (p 2911) (p 4383) (p 4921) (derived73830 p h) (h 8137)

theorem derived85674 (p : Nat → Prop) (h : Inputs p) :
    (p 4383) ∨ (p 2911) :=
  ElevenRUP.step85674 (p 2911) (p 4383) (p 5950) (derived74273 p h) (h 12681)

theorem derived85676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (¬ p 3878) ∨ (p 2651) :=
  ElevenRUP.step85676 (p 2651) (p 2657) (p 3166) (p 3878) (derived73288 p h) (h 19564)

theorem derived85684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 5203) :=
  ElevenRUP.step85684 (p 3389) (p 5200) (p 5203) (derived73954 p h) (h 8824)

theorem derived85687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3516) ∨ (¬ p 4155) ∨ (p 2881) ∨ (¬ p 2996) :=
  ElevenRUP.step85687 (p 2881) (p 2996) (p 3246) (p 3516) (p 3570) (p 3821) (p 4155) (derived73470 p h) (derived73418 p h) (derived43658 p h)

theorem derived85691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4155) ∨ (¬ p 2187) ∨ (¬ p 3412) ∨ (¬ p 2192) ∨ (¬ p 2996) ∨ (¬ p 3961) ∨ (p 2088) ∨ (¬ p 2946) ∨ (¬ p 2459) ∨ (¬ p 4133) ∨ (¬ p 2255) :=
  ElevenRUP.step85691 (p 2088) (p 2187) (p 2192) (p 2255) (p 2459) (p 2946) (p 2996) (p 3412) (p 3857) (p 3961) (p 4133) (p 4155) (derived73480 p h) (derived58979 p h)

theorem derived85698 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 3347) ∨ (¬ p 2493) :=
  ElevenRUP.step85698 (p 2493) (p 2573) (p 2579) (p 3347) (derived73274 p h) (h 5216)

theorem derived85704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4116) ∨ (¬ p 2655) ∨ (p 2573) ∨ (¬ p 2493) ∨ (¬ p 2946) :=
  ElevenRUP.step85704 (p 2493) (p 2573) (p 2579) (p 2655) (p 2946) (p 4116) (p 4704) (derived73274 p h) (derived73046 p h) (derived53224 p h)

theorem derived85709 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2573) ∨ (¬ p 3905) ∨ (p 2406) ∨ (¬ p 3366) ∨ (¬ p 2493) :=
  ElevenRUP.step85709 (p 2406) (p 2493) (p 2573) (p 2579) (p 2608) (p 3238) (p 3366) (p 3905) (p 3954) (derived73498 p h) (derived73274 p h) (derived73374 p h) (derived60977 p h)

theorem derived85710 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 2573) ∨ (p 2406) ∨ (¬ p 2493) :=
  ElevenRUP.step85710 (p 2406) (p 2440) (p 2493) (p 2542) (p 2573) (p 2579) (p 3238) (derived73270 p h) (derived73274 p h) (derived73374 p h) (derived44855 p h)

theorem derived85713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (p 2839) ∨ (p 2573) ∨ (¬ p 3541) ∨ (¬ p 2493) ∨ (¬ p 3361) :=
  ElevenRUP.step85713 (p 2493) (p 2573) (p 2579) (p 2655) (p 2839) (p 3361) (p 3541) (p 3583) (derived73424 p h) (derived73274 p h) (derived67323 p h)

theorem derived85716 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 4108) ∨ (p 2177) ∨ (¬ p 2493) ∨ (p 2573) ∨ (¬ p 3921) :=
  ElevenRUP.step85716 (p 2177) (p 2299) (p 2493) (p 2573) (p 2579) (p 2922) (p 2928) (p 3921) (p 4108) (derived73320 p h) (derived73234 p h) (derived73274 p h) (derived51361 p h)

theorem derived85717 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2482) ∨ (p 2573) ∨ (¬ p 2088) ∨ (¬ p 2493) :=
  ElevenRUP.step85717 (p 2088) (p 2482) (p 2493) (p 2528) (p 2534) (p 2573) (p 2579) (derived73268 p h) (derived73274 p h) (derived45635 p h)

theorem derived85718 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2493) ∨ (p 2573) ∨ (¬ p 2230) :=
  ElevenRUP.step85718 (p 2230) (p 2493) (p 2573) (p 2579) (p 2922) (p 2928) (derived73320 p h) (derived73274 p h) (derived45504 p h)

theorem derived85722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2881) ∨ (p 2573) ∨ (¬ p 2132) ∨ (¬ p 4438) ∨ (¬ p 2493) ∨ (¬ p 4733) ∨ (¬ p 4108) ∨ (¬ p 2509) :=
  ElevenRUP.step85722 (p 2132) (p 2493) (p 2509) (p 2573) (p 2579) (p 2870) (p 2881) (p 4108) (p 4438) (p 4733) (derived73274 p h) (derived60685 p h)

theorem derived85723 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 2901) ∨ (p 2573) ∨ (¬ p 4108) ∨ (¬ p 4733) ∨ (¬ p 2132) ∨ (¬ p 2493) ∨ (p 2406) ∨ (¬ p 3115) :=
  ElevenRUP.step85723 (p 2132) (p 2406) (p 2493) (p 2573) (p 2579) (p 2870) (p 2901) (p 3115) (p 3238) (p 4108) (p 4320) (p 4733) (derived73552 p h) (derived73274 p h) (derived73374 p h) (derived57792 p h)

theorem derived85726 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2911) ∨ (¬ p 2493) ∨ (p 2573) :=
  ElevenRUP.step85726 (p 2493) (p 2573) (p 2579) (p 2911) (p 2922) (p 2928) (p 3644) (derived73320 p h) (derived73434 p h) (derived73274 p h) (derived48935 p h)

theorem derived85727 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3193) ∨ (¬ p 2493) ∨ (¬ p 4022) ∨ (p 3016) :=
  ElevenRUP.step85727 (p 2493) (p 3016) (p 3193) (p 3461) (p 3574) (p 4022) (p 4191) (derived73530 p h) (derived73422 p h) (derived52615 p h)

theorem derived85729 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 3016) ∨ (¬ p 4281) ∨ (¬ p 2493) :=
  ElevenRUP.step85729 (p 2493) (p 2992) (p 3016) (p 3574) (p 3662) (p 4281) (derived73440 p h) (derived73422 p h) (derived69654 p h)

theorem derived85739 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 4389) ∨ (¬ p 4814) ∨ (¬ p 2651) ∨ (¬ p 2493) :=
  ElevenRUP.step85739 (p 2331) (p 2493) (p 2651) (p 2963) (p 4389) (p 4814) (derived73338 p h) (derived50450 p h)

theorem derived85744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2651) ∨ (¬ p 4116) ∨ (p 2881) ∨ (¬ p 4133) ∨ (¬ p 2255) ∨ (¬ p 2957) ∨ (¬ p 2352) ∨ (p 3051) ∨ (p 2992) :=
  ElevenRUP.step85744 (p 2255) (p 2352) (p 2493) (p 2651) (p 2881) (p 2957) (p 2992) (p 3051) (p 3556) (p 3570) (p 3662) (p 4116) (p 4133) (derived73418 p h) (derived73414 p h) (derived73440 p h) (derived60170 p h)

theorem derived85745 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 2528) ∨ (¬ p 2493) ∨ (p 3422) :=
  ElevenRUP.step85745 (p 2493) (p 2509) (p 2528) (p 2534) (p 3422) (p 3584) (derived73268 p h) (derived73426 p h) (derived59905 p h)

theorem derived85747 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 3379) ∨ (¬ p 4133) ∨ (p 3256) ∨ (p 3166) ∨ (¬ p 2254) :=
  ElevenRUP.step85747 (p 2254) (p 2352) (p 2459) (p 2493) (p 3166) (p 3172) (p 3256) (p 3379) (p 4118) (p 4133) (derived73520 p h) (derived73356 p h) (derived49041 p h)

theorem derived85750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (¬ p 2307) ∨ (p 2383) :=
  ElevenRUP.step85750 (p 2307) (p 2352) (p 2383) (p 2387) (p 2493) (derived73246 p h) (derived43307 p h)

theorem derived85752 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (p 2901) ∨ (¬ p 2254) ∨ (¬ p 4133) ∨ (¬ p 2352) ∨ (¬ p 3379) ∨ (p 2881) ∨ (p 2946) :=
  ElevenRUP.step85752 (p 2254) (p 2352) (p 2493) (p 2881) (p 2901) (p 2946) (p 2952) (p 3379) (p 3570) (p 4133) (p 4320) (derived73552 p h) (derived73418 p h) (derived73330 p h) (derived49040 p h)

theorem derived85753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (¬ p 3379) ∨ (p 2241) :=
  ElevenRUP.step85753 (p 2241) (p 2247) (p 2352) (p 2493) (p 3379) (derived73226 p h) (derived54572 p h)

theorem derived85755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (p 3146) ∨ (¬ p 4133) ∨ (p 2220) ∨ (¬ p 3379) :=
  ElevenRUP.step85755 (p 2220) (p 2352) (p 2459) (p 2493) (p 3146) (p 3379) (p 3692) (p 4120) (p 4133) (p 4524) (derived73448 p h) (derived72962 p h) (derived73522 p h) (derived59460 p h)

theorem derived85756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (p 2406) ∨ (¬ p 4079) ∨ (¬ p 2230) :=
  ElevenRUP.step85756 (p 2230) (p 2352) (p 2406) (p 2493) (p 3238) (p 4079) (derived73374 p h) (derived49321 p h)

theorem derived85757 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (¬ p 2352) ∨ (¬ p 4133) ∨ (¬ p 2459) ∨ (¬ p 2493) ∨ (p 3256) ∨ (¬ p 3379) ∨ (¬ p 2254) ∨ (¬ p 3919) :=
  ElevenRUP.step85757 (p 2254) (p 2352) (p 2459) (p 2493) (p 2807) (p 3256) (p 3379) (p 3414) (p 3919) (p 4118) (p 4133) (derived73392 p h) (derived73520 p h) (derived59459 p h)

theorem derived85758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 4116) ∨ (p 2187) ∨ (¬ p 2352) ∨ (¬ p 2440) :=
  ElevenRUP.step85758 (p 2187) (p 2352) (p 2440) (p 2493) (p 3989) (p 4116) (derived73502 p h) (derived58369 p h)

theorem derived85759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (¬ p 4814) ∨ (p 2668) ∨ (¬ p 4194) :=
  ElevenRUP.step85759 (p 2352) (p 2493) (p 2668) (p 3324) (p 4194) (p 4814) (derived73386 p h) (derived41518 p h)

theorem derived85760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 2363) ∨ (¬ p 2493) ∨ (p 3016) ∨ (¬ p 4432) :=
  ElevenRUP.step85760 (p 2363) (p 2493) (p 2509) (p 3016) (p 3574) (p 4347) (p 4432) (derived73560 p h) (derived73422 p h) (derived43476 p h)

theorem derived85762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 2922) ∨ (¬ p 4624) ∨ (¬ p 2493) ∨ (¬ p 3921) :=
  ElevenRUP.step85762 (p 2493) (p 2922) (p 2928) (p 3564) (p 3921) (p 4624) (derived73320 p h) (derived49562 p h)

theorem derived85763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3146) ∨ (¬ p 2493) ∨ (¬ p 3379) ∨ (p 2946) ∨ (¬ p 2254) ∨ (p 3156) ∨ (¬ p 4330) :=
  ElevenRUP.step85763 (p 2254) (p 2493) (p 2946) (p 2952) (p 3146) (p 3156) (p 3379) (p 3497) (p 3564) (p 3692) (p 4330) (derived73448 p h) (derived73330 p h) (derived73400 p h) (derived49061 p h)

theorem derived85767 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 4116) ∨ (¬ p 2651) ∨ (¬ p 4717) ∨ (¬ p 3879) ∨ (¬ p 2493) :=
  ElevenRUP.step85767 (p 2493) (p 2651) (p 2946) (p 2952) (p 3879) (p 4116) (p 4717) (derived73330 p h) (derived63411 p h)

theorem derived85768 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2608) ∨ (¬ p 2493) ∨ (¬ p 3379) :=
  ElevenRUP.step85768 (p 2493) (p 2608) (p 3016) (p 3379) (p 3574) (p 3954) (derived73422 p h) (derived73498 p h) (derived46431 p h)

theorem derived85769 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2241) ∨ (¬ p 3379) ∨ (¬ p 2493) :=
  ElevenRUP.step85769 (p 2241) (p 2247) (p 2493) (p 3016) (p 3379) (p 3574) (derived73422 p h) (derived73226 p h) (derived46469 p h)

theorem derived85770 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2440) ∨ (¬ p 4281) ∨ (¬ p 2241) ∨ (¬ p 2493) :=
  ElevenRUP.step85770 (p 2241) (p 2440) (p 2493) (p 2542) (p 3016) (p 3574) (p 4281) (derived73422 p h) (derived73270 p h) (derived45175 p h)

theorem derived85780 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 3379) ∨ (¬ p 2493) ∨ (¬ p 4717) ∨ (¬ p 4034) :=
  ElevenRUP.step85780 (p 2210) (p 2493) (p 3379) (p 3555) (p 4034) (p 4717) (derived73412 p h) (derived41796 p h)

theorem derived85790 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 4203) ∨ (p 2406) ∨ (¬ p 2493) ∨ (¬ p 4533) :=
  ElevenRUP.step85790 (p 2156) (p 2406) (p 2493) (p 3238) (p 3646) (p 4203) (p 4533) (derived73436 p h) (derived73374 p h) (derived61001 p h)

theorem derived85791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4702) ∨ (p 2284) ∨ (p 2406) ∨ (¬ p 2493) ∨ (¬ p 4203) :=
  ElevenRUP.step85791 (p 2284) (p 2406) (p 2493) (p 3238) (p 3952) (p 4203) (p 4702) (derived73496 p h) (derived73374 p h) (derived52922 p h)

theorem derived85793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3921) ∨ (¬ p 2493) ∨ (¬ p 4405) ∨ (p 2922) ∨ (¬ p 4203) ∨ (¬ p 2187) :=
  ElevenRUP.step85793 (p 2187) (p 2493) (p 2922) (p 2928) (p 3921) (p 4203) (p 4405) (derived73320 p h) (derived41678 p h)

theorem derived85794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3654) ∨ (¬ p 4356) ∨ (¬ p 2493) ∨ (¬ p 2187) :=
  ElevenRUP.step85794 (p 2187) (p 2493) (p 3564) (p 3654) (p 3946) (p 4356) (derived73492 p h) (derived46129 p h)

theorem derived85797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2307) ∨ (p 2406) ∨ (¬ p 2493) ∨ (¬ p 2578) :=
  ElevenRUP.step85797 (p 2307) (p 2396) (p 2406) (p 2493) (p 2578) (p 3238) (derived73374 p h) (derived47764 p h)

theorem derived85798 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2417) ∨ (¬ p 2396) ∨ (¬ p 2493) :=
  ElevenRUP.step85798 (p 2396) (p 2417) (p 2493) (p 2922) (p 2928) (p 4278) (derived73320 p h) (derived73546 p h) (derived61300 p h)

theorem derived85799 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2295) ∨ (¬ p 2493) ∨ (¬ p 3379) :=
  ElevenRUP.step85799 (p 2295) (p 2493) (p 2553) (p 3379) (p 3568) (derived73416 p h) (derived42795 p h)

theorem derived85800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3193) ∨ (¬ p 2493) ∨ (¬ p 4022) ∨ (p 2295) :=
  ElevenRUP.step85800 (p 2295) (p 2493) (p 3193) (p 3323) (p 3568) (p 4022) (derived73416 p h) (derived56300 p h)

theorem derived85802 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2341) ∨ (¬ p 3741) ∨ (¬ p 2493) ∨ (¬ p 2926) ∨ (¬ p 3575) ∨ (¬ p 4717) :=
  ElevenRUP.step85802 (p 2341) (p 2493) (p 2926) (p 3527) (p 3548) (p 3575) (p 3741) (p 4717) (derived73404 p h) (derived41078 p h)

theorem derived85803 (p : Nat → Prop) (h : Inputs p) :
    (p 3631) ∨ (¬ p 2926) ∨ (¬ p 2417) ∨ (¬ p 2493) ∨ (¬ p 3741) ∨ (¬ p 4717) :=
  ElevenRUP.step85803 (p 2417) (p 2493) (p 2926) (p 3631) (p 3741) (p 3817) (p 4717) (derived73468 p h) (derived41974 p h)

theorem derived85804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2946) ∨ (¬ p 2254) ∨ (p 2284) ∨ (p 2187) ∨ (¬ p 3379) ∨ (¬ p 2493) :=
  ElevenRUP.step85804 (p 2187) (p 2254) (p 2284) (p 2493) (p 2553) (p 2946) (p 2952) (p 3379) (p 3952) (p 3989) (derived73330 p h) (derived73496 p h) (derived73502 p h) (derived71641 p h)

theorem derived85807 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2307) ∨ (¬ p 2586) ∨ (¬ p 2493) ∨ (¬ p 3921) :=
  ElevenRUP.step85807 (p 2307) (p 2493) (p 2586) (p 2922) (p 2928) (p 3921) (derived73320 p h) (derived41158 p h)

theorem derived85808 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 4555) ∨ (¬ p 2493) ∨ (¬ p 4203) ∨ (p 2406) :=
  ElevenRUP.step85808 (p 2406) (p 2427) (p 2493) (p 3238) (p 4203) (p 4235) (p 4555) (derived73536 p h) (derived73374 p h) (derived41051 p h)

theorem derived85810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 2274) ∨ (¬ p 3958) ∨ (¬ p 2493) ∨ (p 2922) ∨ (¬ p 4279) :=
  ElevenRUP.step85810 (p 2274) (p 2312) (p 2493) (p 2922) (p 2928) (p 3958) (p 4279) (derived73320 p h) (derived51885 p h)

theorem derived85817 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2307) ∨ (¬ p 5191) ∨ (¬ p 2493) ∨ (¬ p 2577) :=
  ElevenRUP.step85817 (p 2307) (p 2313) (p 2493) (p 2553) (p 2577) (p 5191) (derived73238 p h) (derived41407 p h)

theorem derived85823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2922) ∨ (¬ p 2493) ∨ (p 2230) :=
  ElevenRUP.step85823 (p 2230) (p 2493) (p 2589) (p 2922) (p 2928) (p 3389) (derived73320 p h) (derived73284 p h) (derived43811 p h)

theorem derived85831 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 4203) ∨ (¬ p 2493) ∨ (p 2406) :=
  ElevenRUP.step85831 (p 2373) (p 2406) (p 2493) (p 3238) (p 3880) (p 4203) (derived73490 p h) (derived73374 p h) (derived69506 p h)

theorem derived85833 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5433) ∨ (¬ p 5440) ∨ (¬ p 4203) ∨ (p 2406) ∨ (¬ p 2493) :=
  ElevenRUP.step85833 (p 2406) (p 2493) (p 3238) (p 4203) (p 5433) (p 5440) (derived73374 p h) (derived41057 p h)

theorem derived85838 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 3367) ∨ (¬ p 2493) ∨ (p 2608) :=
  ElevenRUP.step85838 (p 2493) (p 2608) (p 3367) (p 3422) (p 3584) (p 3585) (p 3954) (derived73426 p h) (derived73428 p h) (derived73498 p h) (derived61611 p h)

theorem derived85845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 4960) :=
  ElevenRUP.step85845 (p 2992) (p 4958) (p 4960) (derived73852 p h) (h 8248)

theorem derived85846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2946) ∨ (¬ p 2744) ∨ (¬ p 2245) ∨ (¬ p 2608) :=
  ElevenRUP.step85846 (p 2245) (p 2608) (p 2744) (p 2946) (p 2952) (p 2992) (derived73330 p h) (derived52369 p h)

theorem derived85848 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2992) ∨ (p 2630) ∨ (¬ p 2651) :=
  ElevenRUP.step85848 (p 2630) (p 2651) (p 2810) (p 2946) (p 2952) (p 2992) (derived73330 p h) (derived73316 p h) (derived44641 p h)

theorem derived85849 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2992) ∨ (p 2946) ∨ (p 2727) :=
  ElevenRUP.step85849 (p 2331) (p 2727) (p 2946) (p 2952) (p 2992) (p 4111) (derived73330 p h) (derived73518 p h) (derived61272 p h)

theorem derived85850 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 2946) ∨ (¬ p 2807) ∨ (¬ p 4652) :=
  ElevenRUP.step85850 (p 2727) (p 2807) (p 2946) (p 2952) (p 2992) (p 4111) (p 4652) (derived73518 p h) (derived73330 p h) (derived57730 p h)

theorem derived85851 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 2881) ∨ (¬ p 2901) :=
  ElevenRUP.step85851 (p 2727) (p 2881) (p 2901) (p 2992) (p 4111) (derived73518 p h) (derived46164 p h)

theorem derived85853 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 2427) ∨ (¬ p 2901) :=
  ElevenRUP.step85853 (p 2427) (p 2727) (p 2901) (p 2992) (p 4111) (p 4235) (derived73518 p h) (derived73536 p h) (derived62076 p h)

theorem derived85855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2363) ∨ (¬ p 4902) ∨ (¬ p 3955) ∨ (¬ p 2459) ∨ (¬ p 3156) ∨ (¬ p 2241) ∨ (p 2307) ∨ (¬ p 5021) :=
  ElevenRUP.step85855 (p 2241) (p 2307) (p 2313) (p 2363) (p 2459) (p 2992) (p 3156) (p 3955) (p 4347) (p 4902) (p 5021) (derived73560 p h) (derived73238 p h) (derived57107 p h)

theorem derived85856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2252) ∨ (¬ p 2284) ∨ (¬ p 2630) ∨ (p 2651) :=
  ElevenRUP.step85856 (p 2252) (p 2284) (p 2630) (p 2651) (p 2657) (p 2992) (derived73288 p h) (derived58442 p h)

theorem derived85857 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 2659) ∨ (p 2230) ∨ (¬ p 4241) :=
  ElevenRUP.step85857 (p 2230) (p 2589) (p 2659) (p 2727) (p 2992) (p 4111) (p 4241) (derived73518 p h) (derived73284 p h) (derived41378 p h)

theorem derived85859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 3680) ∨ (¬ p 2992) ∨ (p 2727) :=
  ElevenRUP.step85859 (p 2727) (p 2992) (p 3115) (p 3680) (p 4111) (derived73518 p h) (derived62490 p h)

theorem derived85860 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 2850) ∨ (¬ p 4241) ∨ (¬ p 4750) :=
  ElevenRUP.step85860 (p 2727) (p 2850) (p 2992) (p 3684) (p 4111) (p 4241) (p 4750) (derived73518 p h) (derived73442 p h) (derived50114 p h)

theorem derived85862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2946) ∨ (¬ p 2245) ∨ (¬ p 3379) ∨ (¬ p 4813) :=
  ElevenRUP.step85862 (p 2245) (p 2946) (p 2952) (p 2992) (p 3379) (p 4813) (derived73330 p h) (derived52499 p h)

theorem derived85863 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2727) ∨ (p 2493) ∨ (¬ p 4715) ∨ (p 2440) :=
  ElevenRUP.step85863 (p 2440) (p 2493) (p 2499) (p 2727) (p 2992) (p 4703) (p 4715) (p 4809) (derived73770 p h) (derived73260 p h) (derived73714 p h) (derived65966 p h)

theorem derived85864 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 3016) ∨ (¬ p 4241) ∨ (¬ p 4715) :=
  ElevenRUP.step85864 (p 2727) (p 2992) (p 3016) (p 3574) (p 4111) (p 4241) (p 4715) (derived73518 p h) (derived73422 p h) (derived41275 p h)

theorem derived85869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2881) ∨ (¬ p 2992) ∨ (¬ p 2951) ∨ (p 2727) :=
  ElevenRUP.step85869 (p 2727) (p 2881) (p 2951) (p 2992) (p 3051) (p 4111) (derived73518 p h) (derived46346 p h)

theorem derived85872 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (p 2295) ∨ (p 3136) :=
  ElevenRUP.step85872 (p 2295) (p 2641) (p 2992) (p 3136) (p 3568) (p 4154) (p 4315) (derived73526 p h) (derived73416 p h) (derived73550 p h) (derived62524 p h)

theorem derived85873 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (¬ p 3745) ∨ (p 2274) ∨ (p 3136) :=
  ElevenRUP.step85873 (p 2274) (p 2641) (p 2992) (p 3097) (p 3136) (p 3745) (p 4154) (p 4315) (derived73526 p h) (derived73352 p h) (derived73550 p h) (derived53191 p h)

theorem derived85875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2252) ∨ (p 2264) ∨ (p 3136) ∨ (p 2807) :=
  ElevenRUP.step85875 (p 2252) (p 2264) (p 2807) (p 2992) (p 3136) (p 3414) (p 3553) (p 4315) (derived73410 p h) (derived73550 p h) (derived73392 p h) (derived46607 p h)

theorem derived85878 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 2901) ∨ (¬ p 2992) ∨ (¬ p 2742) ∨ (p 2829) ∨ (¬ p 2785) ∨ (¬ p 2311) ∨ (¬ p 2696) ∨ (¬ p 4556) ∨ (¬ p 2177) :=
  ElevenRUP.step85878 (p 2177) (p 2311) (p 2341) (p 2696) (p 2742) (p 2785) (p 2829) (p 2901) (p 2992) (p 3551) (p 3688) (p 4556) (derived73408 p h) (derived73444 p h) (derived71644 p h)

theorem derived85882 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2992) ∨ (p 2187) ∨ (¬ p 4336) ∨ (p 2727) :=
  ElevenRUP.step85882 (p 2187) (p 2668) (p 2727) (p 2992) (p 3989) (p 4111) (p 4336) (derived73502 p h) (derived73518 p h) (derived55144 p h)

theorem derived85883 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 2274) ∨ (¬ p 2295) ∨ (¬ p 4336) :=
  ElevenRUP.step85883 (p 2274) (p 2295) (p 2727) (p 2992) (p 3097) (p 4111) (p 4336) (derived73518 p h) (derived73352 p h) (derived46255 p h)

theorem derived85890 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 4241) ∨ (¬ p 4644) ∨ (p 2437) :=
  ElevenRUP.step85890 (p 2437) (p 2727) (p 2992) (p 3742) (p 4111) (p 4241) (p 4644) (derived73518 p h) (derived73452 p h) (derived51415 p h)

theorem derived85892 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 4608) ∨ (¬ p 4241) ∨ (p 3083) :=
  ElevenRUP.step85892 (p 2727) (p 2992) (p 3083) (p 4111) (p 4241) (p 4256) (p 4608) (derived73518 p h) (derived73542 p h) (derived41356 p h)

theorem derived85894 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 2253) ∨ (¬ p 4241) ∨ (¬ p 2563) ∨ (¬ p 2651) :=
  ElevenRUP.step85894 (p 2253) (p 2563) (p 2651) (p 2727) (p 2992) (p 4111) (p 4241) (derived73518 p h) (derived43378 p h)

theorem derived85895 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3609) ∨ (p 2383) ∨ (¬ p 2241) ∨ (¬ p 3156) ∨ (¬ p 4746) ∨ (p 2363) ∨ (¬ p 5021) :=
  ElevenRUP.step85895 (p 2241) (p 2363) (p 2383) (p 2387) (p 2992) (p 3156) (p 3609) (p 4347) (p 4746) (p 5021) (derived73246 p h) (derived73560 p h) (derived63609 p h)

theorem derived85900 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3115) ∨ (¬ p 2241) ∨ (p 2177) ∨ (p 2307) ∨ (¬ p 4450) ∨ (¬ p 2992) ∨ (¬ p 5021) :=
  ElevenRUP.step85900 (p 2177) (p 2241) (p 2299) (p 2307) (p 2313) (p 2459) (p 2992) (p 3115) (p 4348) (p 4450) (p 5021) (derived73562 p h) (derived73234 p h) (derived73238 p h) (derived63968 p h)

theorem derived85903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 2992) ∨ (¬ p 2241) ∨ (¬ p 5193) ∨ (p 2363) ∨ (¬ p 4450) ∨ (p 2352) ∨ (p 2573) :=
  ElevenRUP.step85903 (p 2241) (p 2352) (p 2363) (p 2573) (p 2579) (p 2992) (p 3115) (p 3956) (p 4347) (p 4450) (p 5193) (derived73560 p h) (derived73500 p h) (derived73274 p h) (derived54246 p h)

theorem derived85906 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (¬ p 4702) ∨ (¬ p 2563) :=
  ElevenRUP.step85906 (p 2563) (p 2641) (p 2992) (p 4154) (p 4702) (derived73526 p h) (derived67014 p h)

theorem derived85918 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 2187) ∨ (¬ p 4133) ∨ (p 3527) ∨ (¬ p 2284) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2992) :=
  ElevenRUP.step85918 (p 2187) (p 2284) (p 2608) (p 2744) (p 2992) (p 3399) (p 3527) (p 3548) (p 4133) (p 4366) (derived73570 p h) (derived73404 p h) (derived58449 p h)

theorem derived85919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2187) ∨ (p 2727) ∨ (¬ p 2992) :=
  ElevenRUP.step85919 (p 2187) (p 2284) (p 2727) (p 2992) (p 4111) (derived73518 p h) (derived53791 p h)

theorem derived85920 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (p 2295) ∨ (¬ p 2992) ∨ (¬ p 2553) :=
  ElevenRUP.step85920 (p 2295) (p 2553) (p 2641) (p 2992) (p 3568) (p 4154) (derived73526 p h) (derived73416 p h) (derived44624 p h)

theorem derived85921 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2996) ∨ (¬ p 2253) ∨ (¬ p 2992) ∨ (¬ p 2807) :=
  ElevenRUP.step85921 (p 2253) (p 2608) (p 2807) (p 2992) (p 2996) (p 3954) (derived73498 p h) (derived49982 p h)

theorem derived85922 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2992) ∨ (¬ p 4237) :=
  ElevenRUP.step85922 (p 2992) (p 3189) (p 4237) (p 4360) (derived73566 p h) (h 10182)

theorem derived85925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2241) ∨ (p 2427) ∨ (¬ p 2901) :=
  ElevenRUP.step85925 (p 2241) (p 2427) (p 2901) (p 2992) (p 4235) (derived73536 p h) (derived43122 p h)

theorem derived85926 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 3189) ∨ (¬ p 3166) ∨ (¬ p 2901) :=
  ElevenRUP.step85926 (p 2901) (p 2992) (p 3166) (p 3189) (p 4360) (derived73566 p h) (derived47223 p h)

theorem derived85927 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2992) ∨ (¬ p 3166) ∨ (¬ p 2284) :=
  ElevenRUP.step85927 (p 2284) (p 2992) (p 3166) (p 3189) (p 4360) (derived73566 p h) (derived56447 p h)

theorem derived85930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4336) ∨ (¬ p 2187) ∨ (¬ p 2992) ∨ (¬ p 3323) ∨ (p 3125) :=
  ElevenRUP.step85930 (p 2187) (p 2992) (p 3125) (p 3323) (p 3744) (p 4336) (derived73454 p h) (derived42739 p h)

theorem derived85934 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2341) ∨ (¬ p 3031) ∨ (p 3527) ∨ (¬ p 2656) ∨ (¬ p 5201) :=
  ElevenRUP.step85934 (p 2341) (p 2656) (p 2992) (p 3031) (p 3527) (p 3548) (p 4704) (p 5201) (derived73046 p h) (derived73404 p h) (derived63083 p h)

theorem derived85935 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 3745) ∨ (¬ p 2156) ∨ (¬ p 2992) ∨ (¬ p 2960) :=
  ElevenRUP.step85935 (p 2156) (p 2641) (p 2960) (p 2992) (p 3745) (p 4154) (derived73526 p h) (derived49623 p h)

theorem derived85938 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 4558) ∨ (¬ p 2252) ∨ (¬ p 3745) ∨ (p 2331) ∨ (¬ p 2901) :=
  ElevenRUP.step85938 (p 2252) (p 2331) (p 2901) (p 2963) (p 2992) (p 3745) (p 4558) (derived73338 p h) (derived55461 p h)

theorem derived85939 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (¬ p 4509) ∨ (¬ p 3745) ∨ (¬ p 3156) :=
  ElevenRUP.step85939 (p 2641) (p 2992) (p 3156) (p 3745) (p 4154) (p 4509) (derived73526 p h) (derived50128 p h)

theorem derived85941 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (¬ p 2901) ∨ (¬ p 4558) ∨ (¬ p 3745) :=
  ElevenRUP.step85941 (p 2641) (p 2901) (p 2992) (p 3745) (p 4154) (p 4558) (derived73526 p h) (derived49250 p h)

theorem derived85943 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2742) ∨ (¬ p 4558) ∨ (¬ p 2901) ∨ (¬ p 2992) ∨ (¬ p 3745) :=
  ElevenRUP.step85943 (p 2742) (p 2797) (p 2901) (p 2992) (p 3745) (p 4195) (p 4558) (derived73532 p h) (derived55463 p h)

theorem derived85947 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2992) ∨ (¬ p 2619) ∨ (¬ p 4312) ∨ (¬ p 5053) :=
  ElevenRUP.step85947 (p 2619) (p 2992) (p 3189) (p 4312) (p 4360) (p 5053) (derived73566 p h) (derived48526 p h)

theorem derived85949 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2992) ∨ (¬ p 2373) ∨ (¬ p 4702) ∨ (¬ p 4312) :=
  ElevenRUP.step85949 (p 2373) (p 2992) (p 3189) (p 4312) (p 4360) (p 4702) (derived73566 p h) (derived48175 p h)

theorem derived85958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (¬ p 2992) ∨ (p 2563) ∨ (¬ p 2156) ∨ (¬ p 2951) :=
  ElevenRUP.step85958 (p 2156) (p 2563) (p 2951) (p 2992) (p 2996) (p 4110) (derived73516 p h) (derived56912 p h)

theorem derived85959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2951) ∨ (¬ p 2992) ∨ (p 2563) ∨ (¬ p 2156) ∨ (p 3189) :=
  ElevenRUP.step85959 (p 2156) (p 2563) (p 2951) (p 2992) (p 3189) (p 4110) (p 4360) (derived73516 p h) (derived73566 p h) (derived46373 p h)

theorem derived85960 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (¬ p 2284) ∨ (p 2563) :=
  ElevenRUP.step85960 (p 2284) (p 2563) (p 2727) (p 2992) (p 4110) (p 4111) (derived73518 p h) (derived73516 p h) (derived46242 p h)

theorem derived85962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2992) ∨ (¬ p 5193) ∨ (p 2573) ∨ (p 2177) ∨ (¬ p 2241) ∨ (¬ p 4902) ∨ (p 2553) :=
  ElevenRUP.step85962 (p 2177) (p 2241) (p 2299) (p 2553) (p 2573) (p 2579) (p 2588) (p 2992) (p 3156) (p 4902) (p 5193) (derived73274 p h) (derived73234 p h) (derived73282 p h) (derived61603 p h)

theorem derived85966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2951) ∨ (¬ p 3654) ∨ (p 3125) ∨ (¬ p 2992) ∨ (¬ p 2274) ∨ (¬ p 2962) :=
  ElevenRUP.step85966 (p 2274) (p 2951) (p 2962) (p 2992) (p 3125) (p 3654) (p 3744) (derived73454 p h) (derived44512 p h)

theorem derived85968 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (p 3323) ∨ (¬ p 3125) ∨ (¬ p 2992) :=
  ElevenRUP.step85968 (p 2641) (p 2992) (p 3125) (p 3323) (p 4037) (p 4154) (derived73526 p h) (derived73508 p h) (derived43792 p h)

theorem derived85972 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2245) ∨ (p 3189) ∨ (¬ p 4041) ∨ (¬ p 2992) ∨ (¬ p 2177) ∨ (¬ p 4733) ∨ (p 2946) :=
  ElevenRUP.step85972 (p 2122) (p 2177) (p 2245) (p 2774) (p 2946) (p 2952) (p 2992) (p 3189) (p 4041) (p 4360) (p 4733) (derived73566 p h) (derived73330 p h) (derived53301 p h)

theorem derived85973 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2641) ∨ (¬ p 4375) ∨ (p 3323) ∨ (¬ p 2992) :=
  ElevenRUP.step85973 (p 2641) (p 2992) (p 3323) (p 3483) (p 4037) (p 4154) (p 4375) (derived73526 p h) (derived73508 p h) (derived60316 p h)

theorem derived85974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3402) ∨ (¬ p 2992) ∨ (p 2922) ∨ (¬ p 2437) :=
  ElevenRUP.step85974 (p 2437) (p 2922) (p 2928) (p 2992) (p 3402) (p 4704) (derived73320 p h) (derived73046 p h) (derived41708 p h)

theorem derived85976 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 3743) ∨ (¬ p 2860) ∨ (¬ p 5053) ∨ (¬ p 2667) ∨ (¬ p 2992) :=
  ElevenRUP.step85976 (p 2641) (p 2667) (p 2860) (p 2992) (p 3743) (p 4154) (p 5053) (derived73526 p h) (derived41355 p h)

theorem derived85979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2950) ∨ (¬ p 2249) ∨ (¬ p 2284) ∨ (p 2156) :=
  ElevenRUP.step85979 (p 2156) (p 2249) (p 2284) (p 2950) (p 2992) (p 3646) (derived73436 p h) (derived41432 p h)

theorem derived85980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (¬ p 2996) ∨ (¬ p 2992) ∨ (p 2156) ∨ (¬ p 4155) ∨ (p 2187) :=
  ElevenRUP.step85980 (p 2156) (p 2187) (p 2992) (p 2996) (p 3646) (p 3989) (p 4155) (p 4988) (derived73436 p h) (derived73502 p h) (derived60317 p h)

theorem derived85984 (p : Nat → Prop) (h : Inputs p) :
    (p 2995) ∨ (¬ p 2901) :=
  ElevenRUP.step85984 (p 2901) (p 2995) (p 5948) (derived74271 p h) (h 12671)

theorem derived85985 (p : Nat → Prop) (h : Inputs p) :
    (p 3922) ∨ (¬ p 2641) :=
  ElevenRUP.step85985 (p 2641) (p 3922) (p 4758) (derived73746 p h) (h 7737)

theorem derived85986 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 4759) :=
  ElevenRUP.step85986 (p 2641) (p 4758) (p 4759) (derived73746 p h) (h 7738)

theorem derived85988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 4761) :=
  ElevenRUP.step85988 (p 2641) (p 4758) (p 4761) (derived73746 p h) (h 7741)

theorem derived85990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (p 2187) ∨ (p 2727) :=
  ElevenRUP.step85990 (p 2187) (p 2641) (p 2668) (p 2727) (p 3989) (p 4111) (derived73502 p h) (derived73518 p h) (derived54763 p h)

theorem derived85991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2241) ∨ (p 2187) :=
  ElevenRUP.step85991 (p 2187) (p 2241) (p 2641) (p 2668) (p 3989) (derived73502 p h) (derived57955 p h)

theorem derived85992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2331) ∨ (¬ p 2651) ∨ (p 2992) :=
  ElevenRUP.step85992 (p 2331) (p 2641) (p 2651) (p 2963) (p 2992) (p 3662) (derived73338 p h) (derived73440 p h) (derived42706 p h)

theorem derived85995 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2992) ∨ (p 2274) ∨ (¬ p 2641) :=
  ElevenRUP.step85995 (p 2274) (p 2295) (p 2641) (p 2992) (p 3097) (p 3662) (derived73440 p h) (derived73352 p h) (derived64310 p h)

theorem derived85996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2331) ∨ (¬ p 2651) ∨ (p 2630) :=
  ElevenRUP.step85996 (p 2331) (p 2630) (p 2641) (p 2651) (p 2810) (p 2963) (derived73338 p h) (derived73316 p h) (derived60565 p h)

theorem derived85998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2727) ∨ (¬ p 2630) ∨ (p 2331) :=
  ElevenRUP.step85998 (p 2331) (p 2630) (p 2641) (p 2727) (p 2963) (p 4111) (derived73518 p h) (derived73338 p h) (derived71646 p h)

theorem derived86000 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 4194) ∨ (p 2727) :=
  ElevenRUP.step86000 (p 2641) (p 2727) (p 4111) (p 4194) (derived73518 p h) (h 20024)

theorem derived86002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2331) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2245) :=
  ElevenRUP.step86002 (p 2245) (p 2331) (p 2608) (p 2641) (p 2744) (p 2963) (derived73338 p h) (derived52297 p h)

theorem derived86005 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2295) ∨ (¬ p 2651) ∨ (¬ p 2641) :=
  ElevenRUP.step86005 (p 2295) (p 2641) (p 2651) (p 2727) (p 4111) (derived73518 p h) (derived42742 p h)

theorem derived86006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2295) ∨ (p 2563) ∨ (p 2230) ∨ (¬ p 5193) ∨ (¬ p 4620) ∨ (p 3125) ∨ (¬ p 2241) :=
  ElevenRUP.step86006 (p 2230) (p 2241) (p 2295) (p 2563) (p 2589) (p 2641) (p 3125) (p 3744) (p 4110) (p 4620) (p 5193) (derived73516 p h) (derived73284 p h) (derived73454 p h) (derived50278 p h)

theorem derived86007 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2177) ∨ (¬ p 2641) ∨ (¬ p 3487) ∨ (p 2373) ∨ (p 2651) ∨ (¬ p 4905) ∨ (¬ p 2249) ∨ (p 2406) :=
  ElevenRUP.step86007 (p 2177) (p 2249) (p 2295) (p 2373) (p 2406) (p 2641) (p 2651) (p 2657) (p 3238) (p 3487) (p 3880) (p 4905) (derived73490 p h) (derived73288 p h) (derived73374 p h) (derived60562 p h)

theorem derived86014 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2641) ∨ (¬ p 2440) ∨ (¬ p 3984) ∨ (¬ p 4717) :=
  ElevenRUP.step86014 (p 2440) (p 2641) (p 2727) (p 3984) (p 4111) (p 4717) (derived73518 p h) (derived58149 p h)

theorem derived86016 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 3115) ∨ (¬ p 2641) ∨ (¬ p 5043) ∨ (¬ p 3986) :=
  ElevenRUP.step86016 (p 2641) (p 2992) (p 3115) (p 3662) (p 3986) (p 4208) (p 5043) (derived73440 p h) (derived73534 p h) (derived41037 p h)

theorem derived86017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2992) ∨ (¬ p 2946) ∨ (p 2797) :=
  ElevenRUP.step86017 (p 2641) (p 2797) (p 2946) (p 2992) (p 3662) (p 4195) (derived73440 p h) (derived73532 p h) (derived46001 p h)

theorem derived86019 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2641) ∨ (¬ p 3986) ∨ (p 3156) :=
  ElevenRUP.step86019 (p 2641) (p 2992) (p 3156) (p 3497) (p 3662) (p 3986) (derived73440 p h) (derived73400 p h) (derived69507 p h)

theorem derived86027 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3986) ∨ (p 2992) ∨ (p 2156) ∨ (¬ p 2954) ∨ (¬ p 2641) :=
  ElevenRUP.step86027 (p 2156) (p 2641) (p 2954) (p 2992) (p 3646) (p 3662) (p 3986) (derived73440 p h) (derived73436 p h) (derived41571 p h)

theorem derived86030 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 2341) ∨ (¬ p 2911) ∨ (¬ p 5197) ∨ (¬ p 2641) ∨ (¬ p 5193) ∨ (¬ p 4621) ∨ (¬ p 3323) ∨ (¬ p 2241) :=
  ElevenRUP.step86030 (p 2241) (p 2341) (p 2417) (p 2641) (p 2911) (p 3323) (p 3551) (p 4278) (p 4621) (p 5193) (p 5197) (derived73546 p h) (derived73408 p h) (derived54494 p h)

theorem derived86031 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2241) ∨ (¬ p 4405) ∨ (p 2274) ∨ (p 2563) ∨ (p 2230) ∨ (¬ p 5193) :=
  ElevenRUP.step86031 (p 2230) (p 2241) (p 2274) (p 2563) (p 2589) (p 2641) (p 2668) (p 3097) (p 4110) (p 4405) (p 5193) (derived73352 p h) (derived73516 p h) (derived73284 p h) (derived53722 p h)

theorem derived86033 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2668) ∨ (¬ p 2641) ∨ (¬ p 2651) :=
  ElevenRUP.step86033 (p 2641) (p 2651) (p 2668) (p 2727) (p 4111) (derived73518 p h) (derived62026 p h)

theorem derived86036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 2807) ∨ (¬ p 3986) ∨ (p 2563) :=
  ElevenRUP.step86036 (p 2563) (p 2641) (p 2807) (p 2996) (p 3986) (p 4110) (derived73516 p h) (derived43682 p h)

theorem derived86038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3368) ∨ (¬ p 2656) ∨ (¬ p 4975) ∨ (¬ p 2641) ∨ (p 2891) ∨ (¬ p 4399) :=
  ElevenRUP.step86038 (p 2641) (p 2656) (p 2891) (p 3051) (p 3368) (p 3486) (p 4399) (p 4975) (derived73398 p h) (derived62796 p h)

theorem derived86041 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 2641) ∨ (¬ p 4153) ∨ (¬ p 2737) ∨ (¬ p 2608) ∨ (¬ p 2440) ∨ (¬ p 2241) ∨ (¬ p 2427) :=
  ElevenRUP.step86041 (p 2241) (p 2427) (p 2440) (p 2608) (p 2641) (p 2737) (p 2797) (p 4153) (p 4699) (derived73712 p h) (derived67060 p h)

theorem derived86042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (p 2331) ∨ (¬ p 2608) ∨ (p 2727) ∨ (¬ p 2641) :=
  ElevenRUP.step86042 (p 2245) (p 2331) (p 2608) (p 2641) (p 2727) (p 2963) (p 4111) (derived73338 p h) (derived73518 p h) (derived55152 p h)

theorem derived86043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 2742) ∨ (p 2707) ∨ (¬ p 3959) ∨ (¬ p 4330) ∨ (p 2341) ∨ (¬ p 2641) ∨ (¬ p 2696) ∨ (p 2459) :=
  ElevenRUP.step86043 (p 2341) (p 2459) (p 2641) (p 2696) (p 2707) (p 2742) (p 3323) (p 3551) (p 3588) (p 3959) (p 4330) (p 4348) (derived73430 p h) (derived73408 p h) (derived73562 p h) (derived71648 p h)

theorem derived86047 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2274) ∨ (¬ p 3986) ∨ (¬ p 2641) ∨ (¬ p 2946) :=
  ElevenRUP.step86047 (p 2274) (p 2641) (p 2946) (p 2992) (p 3662) (p 3986) (derived73440 p h) (derived42954 p h)

theorem derived86048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2992) ∨ (p 3051) ∨ (¬ p 3986) ∨ (¬ p 2957) ∨ (¬ p 4555) :=
  ElevenRUP.step86048 (p 2641) (p 2957) (p 2992) (p 3051) (p 3556) (p 3662) (p 3986) (p 4555) (derived73440 p h) (derived73414 p h) (derived48448 p h)

theorem derived86049 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2331) ∨ (p 2440) ∨ (p 2406) ∨ (¬ p 3402) :=
  ElevenRUP.step86049 (p 2331) (p 2406) (p 2440) (p 2542) (p 2641) (p 2963) (p 3238) (p 3402) (derived73338 p h) (derived73270 p h) (derived73374 p h) (derived50078 p h)

theorem derived86050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2992) ∨ (¬ p 4705) ∨ (¬ p 3986) ∨ (p 2563) :=
  ElevenRUP.step86050 (p 2563) (p 2641) (p 2992) (p 3662) (p 3986) (p 4110) (p 4705) (derived73440 p h) (derived73516 p h) (derived57446 p h)

theorem derived86056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2727) ∨ (¬ p 3984) ∨ (p 2573) ∨ (¬ p 2659) :=
  ElevenRUP.step86056 (p 2573) (p 2579) (p 2641) (p 2659) (p 2727) (p 3984) (p 4111) (derived73518 p h) (derived73274 p h) (derived42036 p h)

theorem derived86058 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2911) ∨ (¬ p 5193) ∨ (p 2459) ∨ (¬ p 3323) ∨ (p 3389) ∨ (¬ p 2241) ∨ (¬ p 4330) :=
  ElevenRUP.step86058 (p 2241) (p 2459) (p 2641) (p 2911) (p 3323) (p 3389) (p 3540) (p 3644) (p 4330) (p 4348) (p 5193) (derived73434 p h) (derived73562 p h) (derived73402 p h) (derived54676 p h)

theorem derived86061 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 4322) ∨ (¬ p 2641) ∨ (p 3115) :=
  ElevenRUP.step86061 (p 2641) (p 2992) (p 3115) (p 3662) (p 4208) (p 4322) (derived73440 p h) (derived73534 p h) (derived47538 p h)

theorem derived86069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (p 3189) ∨ (p 2459) ∨ (¬ p 5190) ∨ (p 2331) ∨ (¬ p 2470) ∨ (¬ p 2641) ∨ (¬ p 4041) ∨ (¬ p 2528) :=
  ElevenRUP.step86069 (p 2245) (p 2331) (p 2459) (p 2470) (p 2528) (p 2641) (p 2963) (p 3189) (p 4041) (p 4348) (p 4360) (p 5190) (derived73566 p h) (derived73562 p h) (derived73338 p h) (derived42101 p h)

theorem derived86070 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2641) ∨ (p 2651) ∨ (¬ p 2946) :=
  ElevenRUP.step86070 (p 2641) (p 2651) (p 2657) (p 2946) (p 2992) (p 3662) (derived73440 p h) (derived73288 p h) (derived42864 p h)

theorem derived86071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 3166) ∨ (p 3189) ∨ (¬ p 4975) ∨ (p 2651) :=
  ElevenRUP.step86071 (p 2641) (p 2651) (p 2657) (p 3166) (p 3189) (p 4360) (p 4975) (derived73566 p h) (derived73288 p h) (derived60434 p h)

theorem derived86072 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 3567) ∨ (¬ p 2641) ∨ (¬ p 4356) ∨ (p 2563) ∨ (¬ p 4705) :=
  ElevenRUP.step86072 (p 2563) (p 2641) (p 2992) (p 3567) (p 3662) (p 4110) (p 4356) (p 4705) (derived73440 p h) (derived73516 p h) (derived42039 p h)

theorem derived86073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3567) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (¬ p 3487) ∨ (p 2651) ∨ (¬ p 2641) ∨ (¬ p 2509) ∨ (¬ p 2249) ∨ (p 2528) :=
  ElevenRUP.step86073 (p 2249) (p 2307) (p 2396) (p 2509) (p 2528) (p 2534) (p 2641) (p 2651) (p 2657) (p 3487) (p 3567) (p 3950) (derived73288 p h) (derived73268 p h) (derived62190 p h)

theorem derived86077 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (¬ p 3402) ∨ (¬ p 2230) ∨ (¬ p 2656) ∨ (¬ p 2641) ∨ (¬ p 4975) :=
  ElevenRUP.step86077 (p 2230) (p 2406) (p 2641) (p 2656) (p 3238) (p 3402) (p 4975) (derived73374 p h) (derived49513 p h)

theorem derived86078 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3323) ∨ (¬ p 2641) ∨ (¬ p 2241) ∨ (¬ p 5193) ∨ (¬ p 3266) ∨ (¬ p 4330) ∨ (¬ p 3346) :=
  ElevenRUP.step86078 (p 2241) (p 2641) (p 3266) (p 3276) (p 3323) (p 3346) (p 4330) (p 4425) (p 5193) (derived73578 p h) (derived49988 p h)

theorem derived86080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (¬ p 2641) ∨ (¬ p 4975) ∨ (¬ p 2807) ∨ (p 2651) :=
  ElevenRUP.step86080 (p 2641) (p 2651) (p 2657) (p 2807) (p 2996) (p 4975) (derived73288 p h) (derived60433 p h)

theorem derived86089 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3323) ∨ (¬ p 2641) ∨ (¬ p 2352) :=
  ElevenRUP.step86089 (p 2352) (p 2641) (p 3323) (p 3564) (p 4137) (derived73524 p h) (derived43757 p h)

theorem derived86090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 3189) ∨ (¬ p 4769) ∨ (¬ p 4564) ∨ (¬ p 2187) :=
  ElevenRUP.step86090 (p 2187) (p 2641) (p 3189) (p 4360) (p 4564) (p 4769) (derived73566 p h) (derived52244 p h)

theorem derived86091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 3189) ∨ (¬ p 3984) ∨ (¬ p 3958) ∨ (¬ p 4769) ∨ (¬ p 2187) :=
  ElevenRUP.step86091 (p 2187) (p 2641) (p 3189) (p 3958) (p 3984) (p 4360) (p 4769) (derived73566 p h) (derived60226 p h)

theorem derived86093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2187) ∨ (p 2992) ∨ (¬ p 2946) ∨ (¬ p 3986) :=
  ElevenRUP.step86093 (p 2187) (p 2641) (p 2946) (p 2992) (p 3662) (p 3986) (derived73440 p h) (derived47569 p h)

theorem derived86094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4341) ∨ (p 3189) ∨ (¬ p 2641) :=
  ElevenRUP.step86094 (p 2641) (p 3189) (p 4341) (p 4360) (derived73566 p h) (h 20133)

theorem derived86099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2373) ∨ (¬ p 4134) ∨ (¬ p 2668) ∨ (p 3051) ∨ (¬ p 2427) ∨ (¬ p 2241) :=
  ElevenRUP.step86099 (p 2241) (p 2373) (p 2427) (p 2641) (p 2668) (p 3051) (p 3556) (p 3880) (p 4134) (p 4524) (derived73490 p h) (derived72962 p h) (derived73414 p h) (derived51897 p h)

theorem derived86100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (¬ p 2668) ∨ (p 2383) ∨ (¬ p 2249) ∨ (¬ p 2641) :=
  ElevenRUP.step86100 (p 2249) (p 2383) (p 2387) (p 2641) (p 2668) (p 3983) (derived73246 p h) (derived52257 p h)

theorem derived86102 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2668) ∨ (¬ p 2641) ∨ (¬ p 3166) :=
  ElevenRUP.step86102 (p 2641) (p 2668) (p 3166) (p 3189) (p 4360) (derived73566 p h) (derived46010 p h)

theorem derived86108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2641) ∨ (p 2727) ∨ (p 2819) :=
  ElevenRUP.step86108 (p 2641) (p 2668) (p 2727) (p 2819) (p 4111) (p 4358) (derived73518 p h) (derived73564 p h) (derived44990 p h)

theorem derived86114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2274) ∨ (¬ p 2807) ∨ (¬ p 2996) ∨ (¬ p 5193) ∨ (¬ p 2253) ∨ (p 2553) ∨ (p 2573) ∨ (¬ p 4564) :=
  ElevenRUP.step86114 (p 2253) (p 2274) (p 2553) (p 2573) (p 2579) (p 2588) (p 2641) (p 2807) (p 2996) (p 4564) (p 5193) (derived73282 p h) (derived73274 p h) (derived49720 p h)

theorem derived86116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (¬ p 2307) ∨ (¬ p 2641) ∨ (p 2274) ∨ (¬ p 3125) :=
  ElevenRUP.step86116 (p 2274) (p 2307) (p 2641) (p 3097) (p 3125) (p 3567) (derived73352 p h) (derived60963 p h)

theorem derived86118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (p 2122) ∨ (¬ p 2307) ∨ (¬ p 2751) ∨ (¬ p 2641) ∨ (¬ p 3567) :=
  ElevenRUP.step86118 (p 2122) (p 2307) (p 2641) (p 2751) (p 3567) (p 3822) (p 4841) (derived73472 p h) (derived42548 p h)

theorem derived86119 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2307) ∨ (¬ p 3567) ∨ (p 2274) ∨ (¬ p 2641) :=
  ElevenRUP.step86119 (p 2274) (p 2307) (p 2641) (p 2727) (p 3097) (p 3567) (p 4111) (derived73518 p h) (derived73352 p h) (derived46371 p h)

theorem derived86121 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2307) ∨ (¬ p 2177) ∨ (¬ p 2641) ∨ (¬ p 3567) :=
  ElevenRUP.step86121 (p 2177) (p 2307) (p 2641) (p 2727) (p 3567) (p 4111) (derived73518 p h) (derived46285 p h)

theorem derived86126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 3212) ∨ (¬ p 4399) ∨ (¬ p 4975) ∨ (¬ p 2656) ∨ (¬ p 2641) ∨ (p 2972) :=
  ElevenRUP.step86126 (p 2641) (p 2656) (p 2972) (p 3212) (p 3368) (p 4363) (p 4399) (p 4975) (derived73568 p h) (derived58486 p h)

theorem derived86132 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2641) ∨ (¬ p 2807) ∨ (¬ p 2264) :=
  ElevenRUP.step86132 (p 2264) (p 2331) (p 2641) (p 2807) (p 2963) (derived73338 p h) (derived44027 p h)

theorem derived86139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (¬ p 4156) ∨ (¬ p 2641) :=
  ElevenRUP.step86139 (p 2641) (p 2996) (p 3027) (p 4156) (derived73339 p h) (h 26504)

theorem derived86141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (p 2727) ∨ (¬ p 2641) :=
  ElevenRUP.step86141 (p 2295) (p 2396) (p 2641) (p 2727) (p 4111) (derived73518 p h) (derived44989 p h)

theorem derived86142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 3189) ∨ (¬ p 2295) ∨ (¬ p 3166) :=
  ElevenRUP.step86142 (p 2295) (p 2641) (p 3166) (p 3189) (p 4360) (derived73566 p h) (derived47398 p h)

theorem derived86146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2427) ∨ (¬ p 4736) ∨ (¬ p 2241) ∨ (p 2598) ∨ (¬ p 4559) ∨ (¬ p 2641) ∨ (p 2850) :=
  ElevenRUP.step86146 (p 2241) (p 2295) (p 2427) (p 2598) (p 2641) (p 2850) (p 3055) (p 3684) (p 4235) (p 4559) (p 4736) (derived73536 p h) (derived73350 p h) (derived73442 p h) (derived49393 p h)

theorem derived86155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 2598) ∨ (p 2493) :=
  ElevenRUP.step86155 (p 2493) (p 2499) (p 2598) (p 3422) (p 3584) (derived73425 p h) (derived73260 p h) (derived71649 p h)

theorem derived86158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3920) ∨ (¬ p 3422) ∨ (¬ p 4343) ∨ (p 2437) :=
  ElevenRUP.step86158 (p 2437) (p 3422) (p 3584) (p 3742) (p 3920) (p 4343) (derived73425 p h) (derived73452 p h) (h 32587)

theorem derived86164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3325) ∨ (¬ p 2274) ∨ (p 2187) :=
  ElevenRUP.step86164 (p 2187) (p 2274) (p 3097) (p 3325) (p 3989) (derived73351 p h) (derived73502 p h) (h 26630)

theorem derived86171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2819) ∨ (¬ p 4669) ∨ (p 2696) ∨ (¬ p 2996) ∨ (¬ p 2748) ∨ (p 2449) ∨ (¬ p 2363) :=
  ElevenRUP.step86171 (p 2363) (p 2449) (p 2696) (p 2748) (p 2819) (p 2829) (p 2996) (p 3365) (p 3947) (p 4669) (p 4734) (derived72735 p h) (derived73390 p h) (derived73494 p h) (derived52246 p h)

theorem derived86173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 3516) ∨ (¬ p 2318) ∨ (¬ p 4666) ∨ (¬ p 3550) ∨ (p 2122) :=
  ElevenRUP.step86173 (p 2122) (p 2318) (p 2819) (p 3516) (p 3550) (p 3821) (p 3822) (p 4666) (derived73470 p h) (derived73472 p h) (derived42270 p h)

theorem derived86175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 4428) ∨ (p 2187) :=
  ElevenRUP.step86175 (p 2187) (p 2819) (p 3989) (p 4428) (derived73502 p h) (h 29866)

theorem derived86177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2122) ∨ (p 2911) ∨ (¬ p 4403) ∨ (¬ p 4276) ∨ (¬ p 4170) :=
  ElevenRUP.step86177 (p 2122) (p 2819) (p 2911) (p 3644) (p 3822) (p 4170) (p 4276) (p 4403) (derived73472 p h) (derived73434 p h) (derived60396 p h)

theorem derived86178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2122) ∨ (¬ p 4170) ∨ (p 2911) ∨ (¬ p 3569) ∨ (¬ p 4556) ∨ (¬ p 4403) :=
  ElevenRUP.step86178 (p 2122) (p 2819) (p 2911) (p 3569) (p 3644) (p 3822) (p 4170) (p 4403) (p 4556) (derived73472 p h) (derived73434 p h) (derived51056 p h)

theorem derived86179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 3146) ∨ (¬ p 2363) ∨ (p 2122) :=
  ElevenRUP.step86179 (p 2122) (p 2363) (p 2819) (p 3146) (p 3692) (p 3822) (derived73448 p h) (derived73472 p h) (derived43468 p h)

theorem derived86180 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3550) ∨ (¬ p 3266) ∨ (¬ p 2459) ∨ (p 2122) :=
  ElevenRUP.step86180 (p 2122) (p 2459) (p 2819) (p 3266) (p 3550) (p 3822) (derived73472 p h) (derived47345 p h)

theorem derived86181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2829) ∨ (p 2187) ∨ (¬ p 2274) :=
  ElevenRUP.step86181 (p 2187) (p 2274) (p 2819) (p 2829) (p 3989) (derived73502 p h) (derived58076 p h)

theorem derived86186 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2819) ∨ (p 2187) ∨ (p 2132) :=
  ElevenRUP.step86186 (p 2132) (p 2138) (p 2187) (p 2774) (p 2819) (p 3989) (derived73502 p h) (derived73214 p h) (derived45948 p h)

theorem derived86192 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2819) ∨ (¬ p 5021) ∨ (p 2383) ∨ (¬ p 4556) ∨ (¬ p 2427) ∨ (¬ p 2406) ∨ (¬ p 3379) :=
  ElevenRUP.step86192 (p 2122) (p 2383) (p 2387) (p 2406) (p 2427) (p 2819) (p 3379) (p 3822) (p 4556) (p 5021) (derived73472 p h) (derived73246 p h) (derived57203 p h)

theorem derived86194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2774) ∨ (p 2459) ∨ (¬ p 2363) :=
  ElevenRUP.step86194 (p 2363) (p 2459) (p 2774) (p 2819) (p 4348) (derived73562 p h) (derived46381 p h)

theorem derived86197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2363) ∨ (p 2598) :=
  ElevenRUP.step86197 (p 2363) (p 2598) (p 2774) (p 2819) (p 3055) (derived73350 p h) (derived52878 p h)

theorem derived86198 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2307) ∨ (¬ p 2786) ∨ (¬ p 2363) ∨ (¬ p 2819) :=
  ElevenRUP.step86198 (p 2122) (p 2307) (p 2363) (p 2786) (p 2819) (p 3822) (derived73472 p h) (derived59041 p h)

theorem derived86200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2819) ∨ (p 3367) ∨ (p 2352) :=
  ElevenRUP.step86200 (p 2352) (p 2819) (p 2829) (p 3367) (p 3585) (p 3956) (derived73428 p h) (derived73500 p h) (derived53317 p h)

theorem derived86202 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2373) ∨ (¬ p 2819) ∨ (¬ p 2307) ∨ (p 2406) ∨ (¬ p 5017) ∨ (¬ p 4134) ∨ (p 2122) :=
  ElevenRUP.step86202 (p 2122) (p 2307) (p 2373) (p 2406) (p 2819) (p 3238) (p 3379) (p 3452) (p 3822) (p 3880) (p 4134) (p 5017) (derived73394 p h) (derived73490 p h) (derived73374 p h) (derived73472 p h) (derived57530 p h)

theorem derived86206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 2608) ∨ (p 2187) :=
  ElevenRUP.step86206 (p 2187) (p 2608) (p 2819) (p 2829) (p 3989) (derived73502 p h) (derived43056 p h)

theorem derived86207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 4134) ∨ (p 3166) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (p 3256) ∨ (¬ p 3146) :=
  ElevenRUP.step86207 (p 2254) (p 2608) (p 2819) (p 2829) (p 3146) (p 3166) (p 3172) (p 3256) (p 4118) (p 4134) (derived73356 p h) (derived73520 p h) (derived56442 p h)

theorem derived86210 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2819) ∨ (p 2122) ∨ (p 2668) :=
  ElevenRUP.step86210 (p 2122) (p 2331) (p 2668) (p 2819) (p 2963) (p 3324) (p 3822) (derived73338 p h) (derived73472 p h) (derived73386 p h) (derived64040 p h)

theorem derived86219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2608) ∨ (¬ p 3093) ∨ (¬ p 4133) ∨ (¬ p 4024) ∨ (p 2807) ∨ (¬ p 2750) ∨ (¬ p 3919) ∨ (¬ p 2459) ∨ (p 3256) ∨ (¬ p 2252) :=
  ElevenRUP.step86219 (p 2252) (p 2459) (p 2608) (p 2750) (p 2807) (p 2819) (p 3093) (p 3256) (p 3414) (p 3919) (p 3954) (p 4024) (p 4118) (p 4133) (derived73498 p h) (derived73392 p h) (derived73520 p h) (derived55543 p h)

theorem derived86220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2819) ∨ (¬ p 2254) ∨ (¬ p 4133) ∨ (¬ p 2608) ∨ (¬ p 2459) ∨ (p 3256) ∨ (p 3166) :=
  ElevenRUP.step86220 (p 2254) (p 2459) (p 2608) (p 2819) (p 2829) (p 3166) (p 3172) (p 3256) (p 4118) (p 4133) (derived73520 p h) (derived73356 p h) (derived48989 p h)

theorem derived86224 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2819) ∨ (¬ p 4426) ∨ (¬ p 2745) ∨ (¬ p 2667) ∨ (p 2383) :=
  ElevenRUP.step86224 (p 2383) (p 2387) (p 2641) (p 2667) (p 2745) (p 2819) (p 4154) (p 4426) (derived73526 p h) (derived73246 p h) (derived41270 p h)

theorem derived86225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2819) ∨ (¬ p 4625) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (p 2383) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 2246) ∨ (¬ p 2778) ∨ (¬ p 2901) :=
  ElevenRUP.step86225 (p 2246) (p 2383) (p 2387) (p 2744) (p 2778) (p 2819) (p 2901) (p 2946) (p 3246) (p 3366) (p 3917) (p 4625) (derived73246 p h) (derived63982 p h)

theorem derived86229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2528) ∨ (¬ p 2363) ∨ (¬ p 5225) ∨ (¬ p 3573) :=
  ElevenRUP.step86229 (p 2363) (p 2528) (p 2534) (p 2819) (p 3573) (p 5225) (derived73268 p h) (derived53397 p h)

theorem derived86231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2819) ∨ (¬ p 3654) ∨ (¬ p 2750) ∨ (¬ p 2786) ∨ (p 2437) ∨ (p 2911) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 4133) :=
  ElevenRUP.step86231 (p 2252) (p 2437) (p 2651) (p 2657) (p 2750) (p 2753) (p 2786) (p 2819) (p 2911) (p 3644) (p 3654) (p 3742) (p 3917) (p 4133) (derived73452 p h) (derived73434 p h) (derived73288 p h) (derived63140 p h)

theorem derived86234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2829) ∨ (p 2274) ∨ (p 2563) ∨ (¬ p 2608) ∨ (p 2230) ∨ (¬ p 4405) ∨ (¬ p 5193) :=
  ElevenRUP.step86234 (p 2230) (p 2274) (p 2563) (p 2589) (p 2608) (p 2819) (p 2829) (p 3097) (p 4110) (p 4405) (p 5193) (derived73352 p h) (derived73516 p h) (derived73284 p h) (derived60249 p h)

theorem derived86236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2573) ∨ (p 2352) ∨ (¬ p 4375) :=
  ElevenRUP.step86236 (p 2352) (p 2573) (p 2579) (p 2819) (p 3956) (p 4375) (derived73274 p h) (derived73500 p h) (derived71652 p h)

theorem derived86237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2459) ∨ (¬ p 2363) ∨ (p 2122) :=
  ElevenRUP.step86237 (p 2122) (p 2363) (p 2459) (p 2819) (p 3822) (p 4348) (derived73562 p h) (derived73472 p h) (derived53945 p h)

theorem derived86240 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2819) ∨ (¬ p 2363) ∨ (p 2737) :=
  ElevenRUP.step86240 (p 2363) (p 2737) (p 2743) (p 2819) (p 2829) (derived73298 p h) (derived52593 p h)

theorem derived86242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (p 2220) ∨ (¬ p 4401) ∨ (¬ p 2819) ∨ (¬ p 2284) ∨ (¬ p 4506) :=
  ElevenRUP.step86242 (p 2220) (p 2284) (p 2819) (p 2957) (p 4120) (p 4401) (p 4506) (derived73522 p h) (derived42178 p h)

theorem derived86244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2829) ∨ (p 2553) ∨ (p 2651) ∨ (p 3016) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (¬ p 4405) :=
  ElevenRUP.step86244 (p 2254) (p 2553) (p 2588) (p 2608) (p 2651) (p 2657) (p 2819) (p 2829) (p 3016) (p 3574) (p 4405) (derived73282 p h) (derived73288 p h) (derived73422 p h) (derived56713 p h)

theorem derived86248 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2819) ∨ (¬ p 4753) ∨ (¬ p 4375) ∨ (¬ p 2386) ∨ (p 2383) :=
  ElevenRUP.step86248 (p 2383) (p 2386) (p 2387) (p 2819) (p 3016) (p 3574) (p 4375) (p 4753) (derived73422 p h) (derived73246 p h) (derived42360 p h)

theorem derived86249 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2819) ∨ (¬ p 2274) ∨ (¬ p 3958) ∨ (p 2352) :=
  ElevenRUP.step86249 (p 2122) (p 2274) (p 2352) (p 2819) (p 3822) (p 3956) (p 3958) (derived73472 p h) (derived73500 p h) (derived51887 p h)

theorem derived86250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 2819) ∨ (¬ p 3550) ∨ (¬ p 2307) ∨ (p 2122) ∨ (¬ p 3941) ∨ (¬ p 2786) ∨ (p 3083) ∨ (¬ p 2750) ∨ (¬ p 2252) ∨ (p 2651) ∨ (p 2528) :=
  ElevenRUP.step86250 (p 2122) (p 2252) (p 2307) (p 2528) (p 2534) (p 2651) (p 2657) (p 2750) (p 2753) (p 2786) (p 2819) (p 3083) (p 3550) (p 3822) (p 3941) (p 4256) (derived73472 p h) (derived73542 p h) (derived73288 p h) (derived73268 p h) (derived46841 p h)

theorem derived86255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2819) ∨ (p 2383) ∨ (¬ p 2440) ∨ (¬ p 4426) ∨ (¬ p 2577) :=
  ElevenRUP.step86255 (p 2230) (p 2383) (p 2387) (p 2440) (p 2577) (p 2819) (p 4426) (derived73246 p h) (derived61761 p h)

theorem derived86259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4428) ∨ (¬ p 2819) ∨ (p 2383) ∨ (¬ p 4198) ∨ (¬ p 2957) ∨ (¬ p 2901) ∨ (¬ p 4558) :=
  ElevenRUP.step86259 (p 2383) (p 2387) (p 2819) (p 2901) (p 2957) (p 4198) (p 4428) (p 4558) (derived73246 p h) (derived51200 p h)

theorem derived86261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2819) ∨ (¬ p 2786) ∨ (¬ p 4789) ∨ (p 3083) ∨ (¬ p 2655) ∨ (p 2122) ∨ (p 2230) ∨ (¬ p 4384) ∨ (p 2440) :=
  ElevenRUP.step86261 (p 2122) (p 2230) (p 2307) (p 2440) (p 2542) (p 2589) (p 2655) (p 2786) (p 2819) (p 3083) (p 3822) (p 4256) (p 4384) (p 4789) (derived73542 p h) (derived73472 p h) (derived73284 p h) (derived73270 p h) (derived61964 p h)

theorem derived86262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2295) ∨ (¬ p 4426) ∨ (p 2668) ∨ (¬ p 2696) :=
  ElevenRUP.step86262 (p 2295) (p 2668) (p 2696) (p 2819) (p 3324) (p 4426) (derived73386 p h) (derived43292 p h)

theorem derived86265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2753) ∨ (p 2230) ∨ (¬ p 2819) ∨ (¬ p 3979) ∨ (p 2982) ∨ (¬ p 2774) ∨ (¬ p 3347) ∨ (¬ p 5119) :=
  ElevenRUP.step86265 (p 2230) (p 2589) (p 2753) (p 2774) (p 2819) (p 2982) (p 3347) (p 3979) (p 4322) (p 4948) (p 5119) (derived73284 p h) (derived73846 p h) (derived71653 p h)

theorem derived86268 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 2819) ∨ (¬ p 2528) ∨ (¬ p 3979) :=
  ElevenRUP.step86268 (p 2528) (p 2819) (p 3979) (p 4149) (p 4286) (derived73548 p h) (derived61606 p h)

theorem derived86269 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 2819) ∨ (¬ p 5225) ∨ (¬ p 3573) ∨ (¬ p 3979) :=
  ElevenRUP.step86269 (p 2819) (p 3573) (p 3979) (p 4149) (p 4286) (p 5225) (derived73548 p h) (derived54402 p h)

theorem derived86274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4869) ∨ (p 2122) ∨ (¬ p 2608) ∨ (¬ p 2819) :=
  ElevenRUP.step86274 (p 2122) (p 2608) (p 2819) (p 3309) (p 3822) (p 4869) (derived73472 p h) (derived43079 p h)

theorem derived86275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2509) ∨ (¬ p 3979) ∨ (¬ p 4733) ∨ (¬ p 2774) ∨ (p 3379) ∨ (p 2528) ∨ (¬ p 5122) :=
  ElevenRUP.step86275 (p 2509) (p 2528) (p 2534) (p 2774) (p 2819) (p 3379) (p 3452) (p 3979) (p 4733) (p 5122) (derived73394 p h) (derived73268 p h) (derived50366 p h)

theorem derived86277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2192) ∨ (¬ p 4875) ∨ (p 2383) ∨ (¬ p 4356) ∨ (¬ p 3985) :=
  ElevenRUP.step86277 (p 2192) (p 2383) (p 2387) (p 2819) (p 3985) (p 4173) (p 4356) (p 4875) (derived73528 p h) (derived73246 p h) (derived62782 p h)

theorem derived86282 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3389) ∨ (¬ p 2819) ∨ (¬ p 4786) ∨ (¬ p 3343) ∨ (¬ p 2136) ∨ (p 3125) ∨ (¬ p 5322) ∨ (¬ p 4198) ∨ (¬ p 4428) ∨ (¬ p 2663) ∨ (p 2383) :=
  ElevenRUP.step86282 (p 2136) (p 2383) (p 2387) (p 2437) (p 2663) (p 2819) (p 3125) (p 3343) (p 3389) (p 3742) (p 3744) (p 4198) (p 4428) (p 4786) (p 5322) (derived73452 p h) (derived73454 p h) (derived73246 p h) (derived57914 p h)

theorem derived86287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 4861) :=
  ElevenRUP.step86287 (p 2819) (p 4860) (p 4861) (derived73796 p h) (h 7988)

theorem derived86290 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (p 2911) ∨ (¬ p 2187) ∨ (¬ p 3550) ∨ (¬ p 4276) :=
  ElevenRUP.step86290 (p 2187) (p 2274) (p 2911) (p 3097) (p 3550) (p 3644) (p 4276) (derived73352 p h) (derived73434 p h) (derived41718 p h)

theorem derived86294 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2788) :=
  ElevenRUP.step86294 (p 2774) (p 2780) (p 2788) (derived73308 p h) (derived42713 p h)

theorem derived86295 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 4472) :=
  ElevenRUP.step86295 (p 2774) (p 2780) (p 4472) (derived73308 p h) (derived45807 p h)

theorem derived86296 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2787) :=
  ElevenRUP.step86296 (p 2774) (p 2780) (p 2787) (derived73308 p h) (derived48116 p h)

end ElevenLogic
