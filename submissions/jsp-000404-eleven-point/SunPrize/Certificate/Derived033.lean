import SunPrize.Certificate.Derived032
import SunPrize.Certificate.Logic033
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived74853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3389) ∨ (p 2449) ∨ (¬ p 2665) ∨ (¬ p 4112) :=
  ElevenRUP.step74853 (p 2417) (p 2449) (p 2665) (p 3389) (p 3947) (p 4112) (derived73494 p h) (derived49441 p h)

theorem derived74857 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 5008) :=
  ElevenRUP.step74857 (p 3083) (p 5007) (p 5008) (derived73872 p h) (h 8370)

theorem derived74861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 4169) ∨ (p 2881) :=
  ElevenRUP.step74861 (p 2717) (p 2881) (p 3570) (p 3659) (p 4169) (derived73437 p h) (derived73418 p h) (h 6234)

theorem derived74864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2109) ∨ (¬ p 3609) ∨ (p 2088) :=
  ElevenRUP.step74864 (p 2088) (p 2109) (p 3609) (p 3857) (derived73480 p h) (h 6604)

theorem derived74870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2102) ∨ (p 2088) ∨ (¬ p 3537) :=
  ElevenRUP.step74870 (p 2088) (p 2102) (p 3537) (p 3609) (p 3857) (p 4734) (derived73480 p h) (derived72735 p h) (derived55843 p h)

theorem derived74871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (¬ p 3609) ∨ (p 2737) ∨ (p 2088) :=
  ElevenRUP.step74871 (p 2088) (p 2737) (p 2743) (p 3537) (p 3609) (p 3857) (derived73298 p h) (derived73480 p h) (derived45730 p h)

theorem derived74876 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 4031) ∨ (¬ p 4354) ∨ (p 2088) ∨ (p 2406) ∨ (p 3422) ∨ (¬ p 3697) :=
  ElevenRUP.step74876 (p 2088) (p 2406) (p 3238) (p 3422) (p 3584) (p 3609) (p 3697) (p 3857) (p 4031) (p 4354) (derived73480 p h) (derived73374 p h) (derived73426 p h) (derived43101 p h)

theorem derived74877 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2088) ∨ (¬ p 4115) ∨ (¬ p 4744) ∨ (p 2563) ∨ (¬ p 3988) ∨ (¬ p 4885) :=
  ElevenRUP.step74877 (p 2088) (p 2563) (p 3609) (p 3857) (p 3988) (p 4110) (p 4115) (p 4744) (p 4885) (derived73480 p h) (derived73516 p h) (derived48172 p h)

theorem derived74881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4354) ∨ (¬ p 3609) ∨ (p 2850) ∨ (¬ p 4717) ∨ (¬ p 4197) ∨ (¬ p 2386) ∨ (p 2088) :=
  ElevenRUP.step74881 (p 2088) (p 2386) (p 2850) (p 3609) (p 3684) (p 3857) (p 4197) (p 4354) (p 4717) (derived73442 p h) (derived73480 p h) (derived54884 p h)

theorem derived74883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 4861) ∨ (¬ p 3609) ∨ (¬ p 3961) ∨ (p 2088) ∨ (p 2274) ∨ (¬ p 4401) :=
  ElevenRUP.step74883 (p 2088) (p 2274) (p 2318) (p 3097) (p 3609) (p 3857) (p 3961) (p 4401) (p 4861) (derived73480 p h) (derived73352 p h) (derived42426 p h)

theorem derived74893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2363) ∨ (p 2922) ∨ (¬ p 4133) ∨ (p 3379) ∨ (¬ p 2098) ∨ (p 2911) ∨ (¬ p 4733) :=
  ElevenRUP.step74893 (p 2098) (p 2363) (p 2911) (p 2922) (p 2928) (p 3379) (p 3452) (p 3609) (p 3644) (p 4133) (p 4347) (p 4733) (derived73560 p h) (derived73320 p h) (derived73394 p h) (derived73434 p h) (derived62833 p h)

theorem derived74896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2241) ∨ (p 2668) ∨ (¬ p 2098) ∨ (p 2641) ∨ (p 2459) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step74896 (p 2098) (p 2241) (p 2247) (p 2459) (p 2641) (p 2668) (p 3324) (p 3609) (p 4154) (p 4348) (p 4503) (p 4733) (derived73226 p h) (derived73386 p h) (derived73526 p h) (derived73562 p h) (derived54277 p h)

theorem derived74899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2363) ∨ (¬ p 2774) ∨ (¬ p 2241) ∨ (¬ p 4134) ∨ (¬ p 4861) ∨ (¬ p 2753) ∨ (¬ p 2750) ∨ (p 2210) ∨ (p 2166) :=
  ElevenRUP.step74899 (p 2166) (p 2191) (p 2210) (p 2241) (p 2363) (p 2750) (p 2753) (p 2774) (p 3555) (p 3609) (p 4134) (p 4347) (p 4861) (derived73560 p h) (derived73412 p h) (derived73222 p h) (derived50982 p h)

theorem derived74902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3379) ∨ (¬ p 4134) ∨ (¬ p 4733) ∨ (p 2373) ∨ (p 2406) ∨ (p 2363) ∨ (¬ p 4861) ∨ (¬ p 2774) :=
  ElevenRUP.step74902 (p 2363) (p 2373) (p 2406) (p 2774) (p 3238) (p 3379) (p 3452) (p 3609) (p 3880) (p 4134) (p 4347) (p 4733) (p 4861) (derived73394 p h) (derived73490 p h) (derived73374 p h) (derived73560 p h) (derived60554 p h)

theorem derived74906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 4744) ∨ (p 3156) ∨ (p 3146) ∨ (¬ p 5053) :=
  ElevenRUP.step74906 (p 3146) (p 3156) (p 3497) (p 3609) (p 3692) (p 4744) (p 5053) (derived73400 p h) (derived73448 p h) (derived63670 p h)

theorem derived74907 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 4744) ∨ (¬ p 3609) ∨ (p 3146) ∨ (¬ p 4509) :=
  ElevenRUP.step74907 (p 2860) (p 3146) (p 3609) (p 3692) (p 3758) (p 4509) (p 4744) (derived73456 p h) (derived73448 p h) (derived64071 p h)

theorem derived74913 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2753) ∨ (¬ p 3609) ∨ (¬ p 3923) ∨ (¬ p 2098) ∨ (¬ p 2750) ∨ (¬ p 4433) ∨ (p 3146) ∨ (¬ p 2241) :=
  ElevenRUP.step74913 (p 2098) (p 2241) (p 2750) (p 2753) (p 3093) (p 3146) (p 3591) (p 3609) (p 3692) (p 3923) (p 4433) (derived73432 p h) (derived73448 p h) (derived65213 p h)

theorem derived74916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2528) ∨ (¬ p 5214) ∨ (¬ p 4186) ∨ (¬ p 4354) ∨ (p 2922) :=
  ElevenRUP.step74916 (p 2528) (p 2534) (p 2922) (p 2928) (p 3609) (p 4186) (p 4354) (p 5214) (derived73268 p h) (derived73320 p h) (derived58109 p h)

theorem derived74917 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3609) ∨ (p 2192) ∨ (p 2210) ∨ (p 2187) ∨ (¬ p 2098) ∨ (¬ p 4733) ∨ (¬ p 4503) :=
  ElevenRUP.step74917 (p 2098) (p 2187) (p 2192) (p 2210) (p 2459) (p 3555) (p 3609) (p 3989) (p 4173) (p 4348) (p 4503) (p 4733) (derived73562 p h) (derived73528 p h) (derived73412 p h) (derived73502 p h) (derived54293 p h)

theorem derived74919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 4354) ∨ (p 2850) ∨ (¬ p 2509) ∨ (p 2528) :=
  ElevenRUP.step74919 (p 2509) (p 2528) (p 2534) (p 2850) (p 3609) (p 3684) (p 4354) (derived73442 p h) (derived73268 p h) (derived45752 p h)

theorem derived74925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3146) ∨ (¬ p 4744) ∨ (p 2870) ∨ (¬ p 3988) ∨ (¬ p 4555) :=
  ElevenRUP.step74925 (p 2870) (p 3146) (p 3609) (p 3692) (p 3988) (p 4244) (p 4555) (p 4744) (derived73448 p h) (derived73540 p h) (derived50146 p h)

theorem derived74927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2098) ∨ (p 3016) ∨ (p 2459) ∨ (¬ p 2753) ∨ (p 2651) ∨ (¬ p 2252) ∨ (p 2352) ∨ (¬ p 2750) ∨ (¬ p 4503) :=
  ElevenRUP.step74927 (p 2098) (p 2252) (p 2352) (p 2459) (p 2651) (p 2657) (p 2750) (p 2753) (p 3016) (p 3574) (p 3609) (p 3956) (p 4348) (p 4503) (derived73422 p h) (derived73562 p h) (derived73288 p h) (derived73500 p h) (derived64557 p h)

theorem derived74928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4744) ∨ (¬ p 3609) ∨ (p 2373) ∨ (p 3146) ∨ (¬ p 4885) :=
  ElevenRUP.step74928 (p 2373) (p 3146) (p 3609) (p 3692) (p 3880) (p 4744) (p 4885) (derived73490 p h) (derived73448 p h) (derived59166 p h)

theorem derived74930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (p 2946) ∨ (¬ p 3609) ∨ (p 3246) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (p 2901) ∨ (¬ p 4669) :=
  ElevenRUP.step74930 (p 2254) (p 2608) (p 2901) (p 2946) (p 2952) (p 3246) (p 3537) (p 3609) (p 3690) (p 4320) (p 4669) (derived73330 p h) (derived73446 p h) (derived73552 p h) (derived52090 p h)

theorem derived74934 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (¬ p 3609) ∨ (p 3367) ∨ (p 3146) :=
  ElevenRUP.step74934 (p 3146) (p 3367) (p 3537) (p 3585) (p 3609) (p 3692) (derived73428 p h) (derived73448 p h) (derived46301 p h)

theorem derived74936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (p 2241) ∨ (p 2264) ∨ (¬ p 4733) ∨ (¬ p 2098) ∨ (¬ p 3609) ∨ (¬ p 4902) ∨ (p 3146) :=
  ElevenRUP.step74936 (p 2098) (p 2241) (p 2247) (p 2264) (p 2996) (p 3146) (p 3553) (p 3609) (p 3692) (p 4733) (p 4902) (derived73226 p h) (derived73410 p h) (derived73448 p h) (derived51508 p h)

theorem derived74937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4744) ∨ (p 2737) ∨ (p 2177) ∨ (¬ p 3873) ∨ (¬ p 4902) ∨ (¬ p 2839) ∨ (¬ p 3609) ∨ (p 3146) ∨ (p 2774) ∨ (p 2122) :=
  ElevenRUP.step74937 (p 2122) (p 2177) (p 2299) (p 2737) (p 2743) (p 2774) (p 2780) (p 2839) (p 3146) (p 3609) (p 3692) (p 3822) (p 3873) (p 4744) (p 4902) (derived73298 p h) (derived73234 p h) (derived73448 p h) (derived73308 p h) (derived73472 p h) (derived61515 p h)

theorem derived74939 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4805) ∨ (¬ p 2651) ∨ (¬ p 2248) ∨ (p 2440) ∨ (¬ p 2427) ∨ (p 2459) ∨ (¬ p 5206) ∨ (p 2341) ∨ (¬ p 4898) ∨ (¬ p 3609) :=
  ElevenRUP.step74939 (p 2248) (p 2341) (p 2427) (p 2440) (p 2459) (p 2542) (p 2651) (p 3551) (p 3609) (p 4348) (p 4805) (p 4898) (p 5206) (derived73270 p h) (derived73562 p h) (derived73408 p h) (derived64039 p h)

theorem derived74942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 3093) ∨ (¬ p 4319) ∨ (¬ p 4503) ∨ (p 2459) ∨ (¬ p 3609) ∨ (¬ p 2750) ∨ (p 2668) ∨ (¬ p 4805) ∨ (p 3425) ∨ (¬ p 2241) :=
  ElevenRUP.step74942 (p 2241) (p 2459) (p 2668) (p 2750) (p 2753) (p 3093) (p 3324) (p 3425) (p 3471) (p 3591) (p 3609) (p 4319) (p 4348) (p 4503) (p 4805) (derived73432 p h) (derived73562 p h) (derived73386 p h) (derived73396 p h) (derived54534 p h)

theorem derived74943 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3146) ∨ (¬ p 2608) ∨ (¬ p 3537) :=
  ElevenRUP.step74943 (p 2608) (p 3146) (p 3537) (p 3609) (p 3692) (derived73448 p h) (derived46988 p h)

theorem derived74945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2608) ∨ (p 3246) ∨ (¬ p 3537) ∨ (p 2427) ∨ (p 2230) ∨ (¬ p 4669) ∨ (¬ p 5193) :=
  ElevenRUP.step74945 (p 2230) (p 2427) (p 2589) (p 2608) (p 3246) (p 3537) (p 3609) (p 3690) (p 4235) (p 4669) (p 5193) (derived73446 p h) (derived73536 p h) (derived73284 p h) (derived48095 p h)

theorem derived74950 (p : Nat → Prop) (h : Inputs p) :
    (p 2972) ∨ (¬ p 3609) ∨ (¬ p 2166) ∨ (¬ p 4746) ∨ (¬ p 3949) :=
  ElevenRUP.step74950 (p 2166) (p 2972) (p 3609) (p 3949) (p 4363) (p 4746) (derived73568 p h) (derived42313 p h)

theorem derived74952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3125) ∨ (¬ p 2608) ∨ (p 2946) ∨ (¬ p 2254) ∨ (¬ p 3537) ∨ (¬ p 4604) ∨ (p 2284) :=
  ElevenRUP.step74952 (p 2254) (p 2284) (p 2608) (p 2946) (p 2952) (p 3125) (p 3537) (p 3609) (p 3744) (p 3952) (p 4604) (derived73454 p h) (derived73330 p h) (derived73496 p h) (derived48363 p h)

theorem derived74954 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3256) ∨ (¬ p 3609) ∨ (¬ p 4373) ∨ (¬ p 2745) :=
  ElevenRUP.step74954 (p 2745) (p 3189) (p 3256) (p 3609) (p 4118) (p 4360) (p 4373) (derived73566 p h) (derived73520 p h) (derived41311 p h)

theorem derived74955 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 3609) ∨ (p 2363) ∨ (¬ p 2753) ∨ (¬ p 2098) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (p 3527) ∨ (¬ p 4133) :=
  ElevenRUP.step74955 (p 2098) (p 2241) (p 2363) (p 2750) (p 2753) (p 3399) (p 3527) (p 3548) (p 3609) (p 4133) (p 4347) (p 4366) (derived73570 p h) (derived73560 p h) (derived73404 p h) (derived65151 p h)

theorem derived74957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5307) ∨ (¬ p 5206) ∨ (p 3073) ∨ (¬ p 2946) ∨ (¬ p 3609) ∨ (¬ p 2248) ∨ (¬ p 2284) ∨ (¬ p 2187) ∨ (¬ p 4863) ∨ (p 2341) :=
  ElevenRUP.step74957 (p 2187) (p 2248) (p 2284) (p 2341) (p 2946) (p 3073) (p 3551) (p 3609) (p 4261) (p 4863) (p 5206) (p 5307) (derived73544 p h) (derived73408 p h) (derived61836 p h)

theorem derived74961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4288) ∨ (p 3073) ∨ (¬ p 3609) ∨ (¬ p 4373) ∨ (p 3166) :=
  ElevenRUP.step74961 (p 3073) (p 3166) (p 3172) (p 3609) (p 4261) (p 4288) (p 4373) (derived73544 p h) (derived73356 p h) (derived71248 p h)

theorem derived74966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4354) ∨ (p 3073) ∨ (¬ p 3609) ∨ (p 3449) ∨ (p 2850) :=
  ElevenRUP.step74966 (p 2850) (p 3073) (p 3449) (p 3609) (p 3684) (p 3860) (p 4261) (p 4354) (derived73544 p h) (derived73482 p h) (derived73442 p h) (derived58332 p h)

theorem derived74967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4354) ∨ (p 3073) ∨ (¬ p 3609) ∨ (p 3449) ∨ (p 3422) :=
  ElevenRUP.step74967 (p 3073) (p 3422) (p 3449) (p 3584) (p 3609) (p 3860) (p 4261) (p 4354) (derived73544 p h) (derived73482 p h) (derived73426 p h) (derived52183 p h)

theorem derived74972 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (p 2331) ∨ (p 2295) ∨ (¬ p 4669) ∨ (p 2396) ∨ (¬ p 2254) ∨ (¬ p 3609) ∨ (¬ p 2608) :=
  ElevenRUP.step74972 (p 2254) (p 2295) (p 2331) (p 2396) (p 2608) (p 2963) (p 3537) (p 3568) (p 3609) (p 4107) (p 4669) (derived73338 p h) (derived73416 p h) (derived73514 p h) (derived52092 p h)

theorem derived74977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (¬ p 2608) ∨ (p 2651) ∨ (¬ p 2440) ∨ (¬ p 3609) ∨ (¬ p 2254) ∨ (p 2982) ∨ (¬ p 5059) :=
  ElevenRUP.step74977 (p 2254) (p 2440) (p 2608) (p 2651) (p 2657) (p 2982) (p 3537) (p 3609) (p 4948) (p 5059) (derived73288 p h) (derived73846 p h) (derived59908 p h)

theorem derived74980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 3256) ∨ (p 2630) ∨ (¬ p 4373) ∨ (¬ p 5011) :=
  ElevenRUP.step74980 (p 2630) (p 2810) (p 3256) (p 3609) (p 4118) (p 4373) (p 5011) (derived73520 p h) (derived73316 p h) (derived41808 p h)

theorem derived74983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3609) ∨ (p 3256) ∨ (p 2696) :=
  ElevenRUP.step74983 (p 2098) (p 2696) (p 3256) (p 3365) (p 3609) (p 4118) (derived73520 p h) (derived73390 p h) (derived46064 p h)

theorem derived74985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2363) ∨ (¬ p 2608) ∨ (¬ p 3537) :=
  ElevenRUP.step74985 (p 2363) (p 2608) (p 3537) (p 3609) (p 4347) (derived73560 p h) (derived46903 p h)

theorem derived74990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4861) ∨ (p 2528) ∨ (¬ p 4375) ∨ (¬ p 4753) ∨ (¬ p 3609) ∨ (p 3083) :=
  ElevenRUP.step74990 (p 2528) (p 2534) (p 3083) (p 3609) (p 4256) (p 4375) (p 4753) (p 4861) (derived73268 p h) (derived73542 p h) (derived42429 p h)

theorem derived74991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (¬ p 3609) ∨ (p 2363) ∨ (p 2839) :=
  ElevenRUP.step74991 (p 2363) (p 2839) (p 3537) (p 3583) (p 3609) (p 4347) (derived73560 p h) (derived73424 p h) (derived61513 p h)

theorem derived74992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2363) ∨ (¬ p 4857) :=
  ElevenRUP.step74992 (p 2363) (p 3609) (p 4347) (p 4857) (derived73560 p h) (h 20476)

theorem derived74994 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4861) ∨ (¬ p 3609) ∨ (p 2807) ∨ (¬ p 3363) ∨ (¬ p 2663) ∨ (¬ p 2774) ∨ (p 2449) ∨ (¬ p 4133) ∨ (¬ p 3945) ∨ (p 3367) :=
  ElevenRUP.step74994 (p 2363) (p 2449) (p 2663) (p 2774) (p 2807) (p 3363) (p 3367) (p 3414) (p 3585) (p 3609) (p 3945) (p 3947) (p 4133) (p 4347) (p 4861) (derived73560 p h) (derived73392 p h) (derived73494 p h) (derived73428 p h) (derived71251 p h)

theorem derived74996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3609) ∨ (p 2891) ∨ (p 2210) ∨ (p 2881) ∨ (¬ p 4733) ∨ (¬ p 4133) ∨ (p 2363) :=
  ElevenRUP.step74996 (p 2098) (p 2210) (p 2363) (p 2881) (p 2891) (p 3486) (p 3555) (p 3570) (p 3609) (p 4133) (p 4347) (p 4733) (derived73398 p h) (derived73412 p h) (derived73418 p h) (derived73560 p h) (derived62399 p h)

theorem derived74998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2363) ∨ (¬ p 4134) ∨ (¬ p 4877) ∨ (p 3051) ∨ (¬ p 3609) ∨ (p 3156) ∨ (¬ p 3645) ∨ (¬ p 2901) ∨ (¬ p 2753) :=
  ElevenRUP.step74998 (p 2098) (p 2363) (p 2753) (p 2901) (p 3051) (p 3156) (p 3497) (p 3556) (p 3609) (p 3645) (p 4134) (p 4347) (p 4877) (derived73560 p h) (derived73414 p h) (derived73400 p h) (derived65089 p h)

theorem derived75000 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4861) ∨ (p 2122) ∨ (¬ p 4405) ∨ (p 2363) ∨ (¬ p 3609) :=
  ElevenRUP.step75000 (p 2122) (p 2363) (p 3609) (p 3822) (p 4347) (p 4405) (p 4861) (derived73472 p h) (derived73560 p h) (derived60053 p h)

theorem derived75009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4805) ∨ (¬ p 2274) ∨ (p 3073) ∨ (¬ p 5190) ∨ (¬ p 2230) ∨ (¬ p 2284) ∨ (¬ p 3879) ∨ (¬ p 4477) ∨ (¬ p 3609) ∨ (p 3449) :=
  ElevenRUP.step75009 (p 2230) (p 2274) (p 2284) (p 3073) (p 3449) (p 3609) (p 3860) (p 3879) (p 4261) (p 4477) (p 4805) (p 5190) (derived73544 p h) (derived73482 p h) (derived60513 p h)

theorem derived75015 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (p 3189) ∨ (¬ p 2245) ∨ (¬ p 2098) ∨ (¬ p 4733) ∨ (p 2363) ∨ (¬ p 4774) ∨ (¬ p 3609) ∨ (p 2807) :=
  ElevenRUP.step75015 (p 2098) (p 2245) (p 2363) (p 2807) (p 2996) (p 3027) (p 3189) (p 3414) (p 3609) (p 4347) (p 4360) (p 4733) (p 4774) (derived73340 p h) (derived73566 p h) (derived73560 p h) (derived73392 p h) (derived57377 p h)

theorem derived75017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3609) ∨ (¬ p 3537) ∨ (¬ p 5118) ∨ (p 2573) ∨ (p 2352) ∨ (¬ p 5193) ∨ (¬ p 2608) :=
  ElevenRUP.step75017 (p 2352) (p 2573) (p 2579) (p 2608) (p 3537) (p 3609) (p 3956) (p 5118) (p 5193) (p 5580) (derived73274 p h) (derived73500 p h) (derived63698 p h)

theorem derived75019 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3609) ∨ (p 2363) ∨ (p 2264) ∨ (¬ p 2996) ∨ (¬ p 4733) ∨ (¬ p 4133) ∨ (p 2241) :=
  ElevenRUP.step75019 (p 2098) (p 2241) (p 2247) (p 2264) (p 2363) (p 2996) (p 3553) (p 3609) (p 4133) (p 4347) (p 4733) (derived73560 p h) (derived73410 p h) (derived73226 p h) (derived51495 p h)

theorem derived75020 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2098) ∨ (p 2901) ∨ (p 2881) ∨ (¬ p 4133) ∨ (p 2946) ∨ (¬ p 4789) ∨ (p 2363) :=
  ElevenRUP.step75020 (p 2098) (p 2363) (p 2881) (p 2901) (p 2946) (p 2952) (p 3570) (p 3609) (p 4133) (p 4320) (p 4347) (p 4789) (derived73552 p h) (derived73418 p h) (derived73330 p h) (derived73560 p h) (derived65105 p h)

theorem derived75022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4318) ∨ (p 3073) ∨ (p 2307) ∨ (¬ p 3955) ∨ (¬ p 2782) ∨ (¬ p 4861) ∨ (¬ p 3609) :=
  ElevenRUP.step75022 (p 2307) (p 2313) (p 2782) (p 3073) (p 3609) (p 3955) (p 4261) (p 4318) (p 4861) (derived73544 p h) (derived73238 p h) (derived52821 p h)

theorem derived75029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2098) ∨ (¬ p 4134) ∨ (p 2992) ∨ (p 3156) ∨ (p 2363) ∨ (¬ p 4733) ∨ (p 2241) :=
  ElevenRUP.step75029 (p 2098) (p 2241) (p 2247) (p 2363) (p 2992) (p 3156) (p 3497) (p 3609) (p 3662) (p 4134) (p 4347) (p 4733) (derived73440 p h) (derived73400 p h) (derived73560 p h) (derived73226 p h) (derived51510 p h)

theorem derived75030 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (p 2363) ∨ (¬ p 2253) ∨ (¬ p 3609) ∨ (¬ p 3189) ∨ (p 2383) ∨ (¬ p 2651) ∨ (¬ p 4969) ∨ (¬ p 5021) :=
  ElevenRUP.step75030 (p 2253) (p 2363) (p 2383) (p 2387) (p 2651) (p 2727) (p 3189) (p 3609) (p 4111) (p 4347) (p 4969) (p 5021) (derived73518 p h) (derived73560 p h) (derived73246 p h) (derived60398 p h)

theorem derived75032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3609) ∨ (¬ p 2553) ∨ (¬ p 4604) ∨ (¬ p 4030) ∨ (p 2696) ∨ (p 3564) ∨ (¬ p 3347) ∨ (p 2307) ∨ (¬ p 4752) ∨ (¬ p 2577) :=
  ElevenRUP.step75032 (p 2098) (p 2307) (p 2313) (p 2553) (p 2577) (p 2696) (p 3347) (p 3365) (p 3564) (p 3609) (p 4030) (p 4137) (p 4604) (p 4752) (derived73390 p h) (derived73524 p h) (derived73238 p h) (derived55281 p h)

theorem derived75033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 3379) ∨ (¬ p 3609) ∨ (p 2373) ∨ (¬ p 4905) ∨ (¬ p 3660) ∨ (¬ p 4733) ∨ (p 2459) ∨ (p 2493) :=
  ElevenRUP.step75033 (p 2098) (p 2373) (p 2459) (p 2493) (p 2499) (p 3379) (p 3452) (p 3609) (p 3660) (p 3880) (p 4348) (p 4733) (p 4905) (derived73394 p h) (derived73490 p h) (derived73562 p h) (derived73260 p h) (derived60475 p h)

theorem derived75038 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 2761) ∨ (¬ p 4669) ∨ (¬ p 5193) ∨ (¬ p 2608) ∨ (¬ p 3609) ∨ (¬ p 3346) ∨ (¬ p 3537) :=
  ElevenRUP.step75038 (p 2608) (p 2761) (p 3276) (p 3346) (p 3537) (p 3609) (p 4425) (p 4669) (p 5193) (derived73578 p h) (derived52913 p h)

theorem derived75039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4744) ∨ (p 3449) ∨ (¬ p 3609) ∨ (p 2860) ∨ (p 3073) :=
  ElevenRUP.step75039 (p 2860) (p 3073) (p 3449) (p 3609) (p 3758) (p 3860) (p 4261) (p 4744) (derived73482 p h) (derived73456 p h) (derived73544 p h) (derived47434 p h)

theorem derived75042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (p 2440) ∨ (¬ p 2655) ∨ (p 2230) ∨ (¬ p 3609) ∨ (¬ p 4947) ∨ (p 3343) ∨ (¬ p 5059) :=
  ElevenRUP.step75042 (p 2230) (p 2254) (p 2440) (p 2542) (p 2589) (p 2608) (p 2655) (p 3343) (p 3359) (p 3537) (p 3609) (p 4947) (p 5059) (derived73270 p h) (derived73284 p h) (derived73388 p h) (derived59931 p h)

theorem derived75049 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3609) ∨ (¬ p 2573) ∨ (¬ p 2437) ∨ (p 2459) ∨ (¬ p 4805) ∨ (¬ p 4419) ∨ (¬ p 3820) ∨ (p 3016) ∨ (¬ p 5087) :=
  ElevenRUP.step75049 (p 2341) (p 2437) (p 2459) (p 2573) (p 3016) (p 3551) (p 3574) (p 3609) (p 3820) (p 4348) (p 4419) (p 4805) (p 5087) (derived73408 p h) (derived73562 p h) (derived73422 p h) (derived47059 p h)

theorem derived75051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (p 2737) ∨ (p 2946) ∨ (p 2459) ∨ (p 3156) ∨ (¬ p 4905) ∨ (¬ p 2098) ∨ (¬ p 3361) :=
  ElevenRUP.step75051 (p 2098) (p 2459) (p 2737) (p 2743) (p 2946) (p 2952) (p 3156) (p 3361) (p 3497) (p 3609) (p 4348) (p 4905) (derived73298 p h) (derived73330 p h) (derived73562 p h) (derived73400 p h) (derived71258 p h)

theorem derived75052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2331) ∨ (¬ p 4503) ∨ (p 2737) ∨ (¬ p 3609) ∨ (p 2459) ∨ (p 2668) ∨ (¬ p 3361) :=
  ElevenRUP.step75052 (p 2098) (p 2331) (p 2459) (p 2668) (p 2737) (p 2743) (p 2963) (p 3324) (p 3361) (p 3609) (p 4348) (p 4503) (derived73338 p h) (derived73298 p h) (derived73562 p h) (derived73386 p h) (derived71259 p h)

theorem derived75062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4700) ∨ (p 2284) ∨ (¬ p 2230) ∨ (¬ p 2665) ∨ (¬ p 2563) :=
  ElevenRUP.step75062 (p 2230) (p 2284) (p 2563) (p 2665) (p 3952) (p 4700) (derived73496 p h) (derived48348 p h)

theorem derived75063 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 4700) ∨ (p 2901) ∨ (¬ p 2665) :=
  ElevenRUP.step75063 (p 2230) (p 2427) (p 2665) (p 2901) (p 4320) (p 4700) (derived73552 p h) (derived48356 p h)

theorem derived75064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4399) ∨ (¬ p 2440) ∨ (¬ p 2665) ∨ (¬ p 2156) ∨ (p 2563) :=
  ElevenRUP.step75064 (p 2156) (p 2440) (p 2563) (p 2665) (p 4110) (p 4399) (derived73516 p h) (derived48344 p h)

theorem derived75065 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3016) ∨ (¬ p 4194) ∨ (¬ p 2573) ∨ (¬ p 2665) ∨ (p 2668) :=
  ElevenRUP.step75065 (p 2383) (p 2573) (p 2583) (p 2665) (p 2668) (p 3016) (p 3324) (p 3574) (p 4194) (derived73422 p h) (derived73278 p h) (derived73386 p h) (derived66995 p h)

theorem derived75066 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2553) ∨ (¬ p 4194) ∨ (¬ p 2573) ∨ (¬ p 2665) :=
  ElevenRUP.step75066 (p 2295) (p 2553) (p 2573) (p 2665) (p 3568) (p 4194) (derived73416 p h) (derived62621 p h)

theorem derived75067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3878) ∨ (p 3256) ∨ (¬ p 2528) ∨ (¬ p 2665) :=
  ElevenRUP.step75067 (p 2470) (p 2528) (p 2665) (p 3256) (p 3878) (p 4118) (derived73520 p h) (derived48766 p h)

theorem derived75069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2427) ∨ (¬ p 2665) ∨ (¬ p 4399) ∨ (¬ p 2440) :=
  ElevenRUP.step75069 (p 2427) (p 2440) (p 2665) (p 3051) (p 4235) (p 4399) (derived73536 p h) (derived50836 p h)

theorem derived75070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (¬ p 4129) ∨ (¬ p 3425) ∨ (p 2881) ∨ (¬ p 4736) ∨ (p 3193) ∨ (¬ p 3276) ∨ (¬ p 3379) :=
  ElevenRUP.step75070 (p 2881) (p 3193) (p 3222) (p 3276) (p 3379) (p 3425) (p 3570) (p 4129) (p 4423) (p 4736) (derived73418 p h) (derived73364 p h) (derived55572 p h)

theorem derived75071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (¬ p 3868) ∨ (p 2331) ∨ (¬ p 3333) ∨ (p 3461) ∨ (p 3323) ∨ (¬ p 3389) ∨ (¬ p 3362) ∨ (¬ p 3686) ∨ (¬ p 4789) :=
  ElevenRUP.step75071 (p 2331) (p 2963) (p 3323) (p 3333) (p 3362) (p 3389) (p 3461) (p 3686) (p 3868) (p 4037) (p 4191) (p 4423) (p 4789) (derived73338 p h) (derived73530 p h) (derived73508 p h) (derived47879 p h)

theorem derived75074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (¬ p 3791) ∨ (¬ p 3425) ∨ (p 2177) :=
  ElevenRUP.step75074 (p 2177) (p 2299) (p 3425) (p 3791) (p 4423) (derived73234 p h) (derived53848 p h)

theorem derived75078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (¬ p 5559) ∨ (¬ p 3609) ∨ (p 2459) ∨ (¬ p 4805) :=
  ElevenRUP.step75078 (p 2459) (p 3609) (p 4348) (p 4423) (p 4805) (p 5559) (derived73562 p h) (derived50337 p h)

theorem derived75083 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2707) ∨ (¬ p 2573) ∨ (¬ p 5190) ∨ (¬ p 3564) ∨ (¬ p 4831) ∨ (¬ p 4423) ∨ (¬ p 3461) :=
  ElevenRUP.step75083 (p 2573) (p 2608) (p 2707) (p 3461) (p 3564) (p 3588) (p 3954) (p 4423) (p 4831) (p 5190) (derived73498 p h) (derived73430 p h) (derived58666 p h)

theorem derived75084 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (p 2707) ∨ (¬ p 2248) ∨ (p 2608) ∨ (¬ p 3166) ∨ (¬ p 3266) ∨ (¬ p 4831) ∨ (¬ p 3256) :=
  ElevenRUP.step75084 (p 2248) (p 2608) (p 2707) (p 3166) (p 3256) (p 3266) (p 3588) (p 3954) (p 4423) (p 4831) (derived73430 p h) (derived73498 p h) (derived51299 p h)

theorem derived75086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 3343) ∨ (¬ p 4831) ∨ (p 2210) ∨ (¬ p 3371) ∨ (¬ p 3276) ∨ (¬ p 2248) ∨ (¬ p 2651) ∨ (¬ p 4423) :=
  ElevenRUP.step75086 (p 2210) (p 2248) (p 2651) (p 3276) (p 3343) (p 3366) (p 3371) (p 3425) (p 3555) (p 4423) (p 4831) (derived73412 p h) (derived57353 p h)

theorem derived75089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4423) ∨ (¬ p 5559) ∨ (¬ p 3609) ∨ (¬ p 4805) ∨ (¬ p 3550) ∨ (p 2363) :=
  ElevenRUP.step75089 (p 2363) (p 3550) (p 3609) (p 4347) (p 4423) (p 4805) (p 5559) (derived73560 p h) (derived56625 p h)

theorem derived75095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 4805) ∨ (p 2459) ∨ (p 2406) ∨ (p 2373) ∨ (¬ p 4905) ∨ (p 2598) ∨ (¬ p 4030) ∨ (¬ p 2707) :=
  ElevenRUP.step75095 (p 2373) (p 2406) (p 2459) (p 2598) (p 2707) (p 3055) (p 3238) (p 3609) (p 3880) (p 4030) (p 4348) (p 4734) (p 4805) (p 4905) (derived73562 p h) (derived72735 p h) (derived73374 p h) (derived73490 p h) (derived73350 p h) (derived56825 p h)

theorem derived75096 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 2707) ∨ (p 2459) ∨ (¬ p 4805) ∨ (¬ p 2608) :=
  ElevenRUP.step75096 (p 2459) (p 2608) (p 2707) (p 3609) (p 4348) (p 4805) (derived73562 p h) (derived48279 p h)

theorem derived75099 (p : Nat → Prop) (h : Inputs p) :
    (p 3740) ∨ (p 2437) :=
  ElevenRUP.step75099 (p 2437) (p 3740) (p 4649) (derived73688 p h) (h 7446)

theorem derived75100 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 4650) :=
  ElevenRUP.step75100 (p 2437) (p 4649) (p 4650) (derived73688 p h) (h 7448)

theorem derived75101 (p : Nat → Prop) (h : Inputs p) :
    (p 4327) ∨ (p 2437) :=
  ElevenRUP.step75101 (p 2437) (p 4327) (p 4649) (derived73688 p h) (h 7449)

theorem derived75102 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 4652) :=
  ElevenRUP.step75102 (p 2437) (p 3742) (p 4652) (derived73452 p h) (derived47216 p h)

theorem derived75105 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 4811) :=
  ElevenRUP.step75105 (p 2437) (p 3742) (p 4811) (derived73452 p h) (derived59204 p h)

theorem derived75108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2437) ∨ (¬ p 3923) ∨ (¬ p 3083) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (p 3093) ∨ (¬ p 4376) ∨ (¬ p 4596) :=
  ElevenRUP.step75108 (p 2437) (p 2608) (p 3083) (p 3093) (p 3389) (p 3519) (p 3591) (p 3742) (p 3923) (p 4376) (p 4596) (derived73452 p h) (derived73432 p h) (derived63994 p h)

theorem derived75109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2210) ∨ (¬ p 3083) ∨ (p 2437) ∨ (p 2192) ∨ (¬ p 4596) ∨ (p 2187) ∨ (¬ p 5190) :=
  ElevenRUP.step75109 (p 2187) (p 2192) (p 2210) (p 2437) (p 3083) (p 3389) (p 3555) (p 3742) (p 3989) (p 4173) (p 4596) (p 5190) (derived73412 p h) (derived73452 p h) (derived73528 p h) (derived73502 p h) (derived57198 p h)

theorem derived75111 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2922) ∨ (¬ p 3083) ∨ (¬ p 2528) :=
  ElevenRUP.step75111 (p 2437) (p 2528) (p 2922) (p 3083) (p 3742) (derived73452 p h) (derived47228 p h)

theorem derived75112 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3389) ∨ (¬ p 2352) ∨ (¬ p 3016) ∨ (¬ p 2663) :=
  ElevenRUP.step75112 (p 2352) (p 2437) (p 2663) (p 3016) (p 3389) (p 3742) (derived73452 p h) (derived43083 p h)

theorem derived75113 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2437) ∨ (¬ p 3475) ∨ (¬ p 3201) :=
  ElevenRUP.step75113 (p 2437) (p 2651) (p 2657) (p 3201) (p 3475) (p 3742) (derived73288 p h) (derived73452 p h) (derived71260 p h)

theorem derived75118 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3016) ∨ (¬ p 3364) ∨ (p 2911) ∨ (p 3422) :=
  ElevenRUP.step75118 (p 2437) (p 2911) (p 3016) (p 3364) (p 3422) (p 3584) (p 3644) (p 3742) (derived73452 p h) (derived73434 p h) (derived73426 p h) (derived43293 p h)

theorem derived75119 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2440) ∨ (¬ p 4001) ∨ (p 2230) ∨ (¬ p 2655) ∨ (p 2881) :=
  ElevenRUP.step75119 (p 2230) (p 2437) (p 2440) (p 2542) (p 2589) (p 2655) (p 2881) (p 3570) (p 3742) (p 4001) (derived73452 p h) (derived73270 p h) (derived73284 p h) (derived73418 p h) (derived48561 p h)

theorem derived75120 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 2655) ∨ (¬ p 3083) ∨ (¬ p 3361) ∨ (p 2470) ∨ (p 2437) :=
  ElevenRUP.step75120 (p 2437) (p 2470) (p 2476) (p 2655) (p 2737) (p 2743) (p 3083) (p 3361) (p 3742) (derived73298 p h) (derived73250 p h) (derived73452 p h) (derived44753 p h)

theorem derived75122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 2437) ∨ (p 2406) ∨ (p 2651) :=
  ElevenRUP.step75122 (p 2406) (p 2437) (p 2651) (p 2657) (p 2922) (p 3238) (p 3742) (derived73452 p h) (derived73374 p h) (derived73288 p h) (derived63426 p h)

theorem derived75123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2437) ∨ (p 2651) ∨ (p 2911) ∨ (¬ p 2156) ∨ (¬ p 2144) ∨ (¬ p 4902) ∨ (p 2860) ∨ (¬ p 4789) :=
  ElevenRUP.step75123 (p 2144) (p 2156) (p 2437) (p 2619) (p 2651) (p 2657) (p 2860) (p 2911) (p 3644) (p 3742) (p 3758) (p 4789) (p 4902) (derived73452 p h) (derived73288 p h) (derived73434 p h) (derived73456 p h) (derived50979 p h)

theorem derived75125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2911) ∨ (¬ p 2254) ∨ (¬ p 2187) ∨ (p 2651) ∨ (p 2437) ∨ (¬ p 2210) ∨ (¬ p 4133) :=
  ElevenRUP.step75125 (p 2187) (p 2192) (p 2210) (p 2254) (p 2437) (p 2651) (p 2657) (p 2911) (p 3644) (p 3742) (p 4133) (derived73434 p h) (derived73288 p h) (derived73452 p h) (derived50488 p h)

theorem derived75127 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2177) ∨ (p 2651) ∨ (p 2437) :=
  ElevenRUP.step75127 (p 2177) (p 2437) (p 2651) (p 2657) (p 2911) (p 3644) (p 3742) (derived73434 p h) (derived73288 p h) (derived73452 p h) (derived45832 p h)

theorem derived75128 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3309) ∨ (p 2651) ∨ (¬ p 2254) ∨ (¬ p 3093) ∨ (¬ p 4666) ∨ (p 2437) ∨ (¬ p 2177) :=
  ElevenRUP.step75128 (p 2177) (p 2254) (p 2417) (p 2437) (p 2651) (p 2657) (p 3093) (p 3309) (p 3742) (p 4278) (p 4666) (derived73546 p h) (derived73288 p h) (derived73452 p h) (derived63278 p h)

theorem derived75129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2870) ∨ (¬ p 2132) ∨ (¬ p 4789) ∨ (p 2651) ∨ (¬ p 4668) ∨ (p 2437) ∨ (p 2911) :=
  ElevenRUP.step75129 (p 2132) (p 2437) (p 2651) (p 2657) (p 2870) (p 2911) (p 3246) (p 3644) (p 3742) (p 4668) (p 4789) (derived73288 p h) (derived73452 p h) (derived73434 p h) (derived56597 p h)

theorem derived75131 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2651) ∨ (p 2437) ∨ (p 2911) :=
  ElevenRUP.step75131 (p 2437) (p 2651) (p 2657) (p 2911) (p 3527) (p 3644) (p 3742) (derived73288 p h) (derived73452 p h) (derived73434 p h) (derived51838 p h)

theorem derived75133 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3389) ∨ (p 2946) ∨ (¬ p 2663) :=
  ElevenRUP.step75133 (p 2437) (p 2663) (p 2946) (p 2952) (p 3389) (p 3742) (derived73452 p h) (derived73330 p h) (derived69598 p h)

theorem derived75136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5307) ∨ (¬ p 4370) ∨ (p 2437) ∨ (¬ p 4712) ∨ (¬ p 3083) ∨ (p 2177) :=
  ElevenRUP.step75136 (p 2177) (p 2299) (p 2437) (p 3083) (p 3742) (p 4370) (p 4712) (p 5307) (derived73452 p h) (derived73234 p h) (derived55882 p h)

theorem derived75138 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2881) ∨ (p 2437) ∨ (p 2651) :=
  ElevenRUP.step75138 (p 2437) (p 2651) (p 2657) (p 2881) (p 2911) (p 3644) (p 3742) (derived73434 p h) (derived73452 p h) (derived73288 p h) (derived52502 p h)

theorem derived75139 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2459) ∨ (p 2437) ∨ (p 2651) :=
  ElevenRUP.step75139 (p 2437) (p 2459) (p 2651) (p 2657) (p 2911) (p 3644) (p 3742) (p 4348) (derived73434 p h) (derived73562 p h) (derived73452 p h) (derived73288 p h) (derived44724 p h)

theorem derived75142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2651) ∨ (¬ p 4241) ∨ (p 2437) ∨ (¬ p 4644) :=
  ElevenRUP.step75142 (p 2437) (p 2651) (p 2657) (p 2946) (p 3742) (p 4241) (p 4644) (derived73288 p h) (derived73452 p h) (derived50089 p h)

theorem derived75144 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2396) ∨ (p 2437) ∨ (¬ p 3016) :=
  ElevenRUP.step75144 (p 2396) (p 2417) (p 2437) (p 3016) (p 3742) (p 4278) (derived73546 p h) (derived73452 p h) (derived61299 p h)

theorem derived75147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3156) ∨ (¬ p 4556) ∨ (¬ p 2210) ∨ (¬ p 2166) ∨ (p 2417) ∨ (¬ p 2396) ∨ (p 2437) :=
  ElevenRUP.step75147 (p 2166) (p 2210) (p 2396) (p 2417) (p 2437) (p 2901) (p 3156) (p 3497) (p 3742) (p 4278) (p 4556) (derived73400 p h) (derived73546 p h) (derived73452 p h) (derived50106 p h)

theorem derived75150 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2440) ∨ (¬ p 4001) ∨ (¬ p 4539) ∨ (¬ p 3051) :=
  ElevenRUP.step75150 (p 2437) (p 2440) (p 2542) (p 3051) (p 3742) (p 4001) (p 4539) (derived73452 p h) (derived73270 p h) (derived56972 p h)

theorem derived75152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 2437) ∨ (¬ p 4001) ∨ (¬ p 2982) ∨ (¬ p 4343) ∨ (¬ p 5046) ∨ (¬ p 3872) :=
  ElevenRUP.step75152 (p 2437) (p 2850) (p 2982) (p 3742) (p 3872) (p 4001) (p 4343) (p 5046) (derived73452 p h) (derived49396 p h)

theorem derived75153 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3872) ∨ (p 2437) ∨ (¬ p 2881) ∨ (p 2727) :=
  ElevenRUP.step75153 (p 2437) (p 2727) (p 2881) (p 2911) (p 3644) (p 3742) (p 3872) (p 4111) (derived73434 p h) (derived73452 p h) (derived73518 p h) (derived43602 p h)

theorem derived75155 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3016) ∨ (¬ p 3920) :=
  ElevenRUP.step75155 (p 2437) (p 3016) (p 3574) (p 3742) (p 3920) (derived73452 p h) (derived73421 p h) (h 6413)

theorem derived75161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3921) ∨ (p 2437) ∨ (¬ p 2586) ∨ (¬ p 3016) :=
  ElevenRUP.step75161 (p 2307) (p 2437) (p 2586) (p 3016) (p 3742) (p 3921) (derived73452 p h) (derived49139 p h)

theorem derived75162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (p 2437) ∨ (p 2459) ∨ (¬ p 2656) ∨ (¬ p 2528) :=
  ElevenRUP.step75162 (p 2437) (p 2459) (p 2470) (p 2528) (p 2656) (p 3742) (p 4348) (derived73452 p h) (derived73562 p h) (derived43418 p h)

theorem derived75164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2437) ∨ (¬ p 3367) ∨ (¬ p 3016) ∨ (¬ p 3759) :=
  ElevenRUP.step75164 (p 2437) (p 3016) (p 3367) (p 3389) (p 3742) (p 3759) (derived73452 p h) (derived47455 p h)

theorem derived75166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (¬ p 3389) ∨ (p 2437) :=
  ElevenRUP.step75166 (p 2437) (p 2656) (p 3389) (p 3742) (derived73452 p h) (h 5811)

theorem derived75170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (p 2437) ∨ (¬ p 3389) :=
  ElevenRUP.step75170 (p 2437) (p 2656) (p 3389) (p 3540) (p 3742) (derived73452 p h) (derived73401 p h) (h 34092)

theorem derived75171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3019) ∨ (p 2493) ∨ (p 2437) ∨ (p 3564) :=
  ElevenRUP.step75171 (p 2437) (p 2493) (p 2499) (p 3019) (p 3323) (p 3564) (p 3742) (p 4137) (derived73260 p h) (derived73452 p h) (derived73524 p h) (derived43022 p h)

theorem derived75173 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2440) ∨ (¬ p 3741) :=
  ElevenRUP.step75173 (p 2437) (p 2440) (p 2542) (p 3741) (p 3742) (derived73452 p h) (derived73270 p h) (h 5483)

theorem derived75175 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 2437) ∨ (¬ p 4001) ∨ (¬ p 2373) ∨ (¬ p 4904) :=
  ElevenRUP.step75175 (p 2373) (p 2437) (p 2440) (p 2542) (p 3742) (p 4001) (p 4904) (derived73270 p h) (derived73452 p h) (derived41888 p h)

theorem derived75177 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 2437) ∨ (¬ p 2563) ∨ (¬ p 4555) :=
  ElevenRUP.step75177 (p 2437) (p 2440) (p 2542) (p 2563) (p 3742) (p 4555) (derived73270 p h) (derived73452 p h) (derived70045 p h)

theorem derived75180 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2528) ∨ (¬ p 2253) ∨ (¬ p 4121) ∨ (p 2177) ∨ (p 2274) ∨ (p 2156) ∨ (¬ p 4420) ∨ (¬ p 2651) :=
  ElevenRUP.step75180 (p 2156) (p 2177) (p 2253) (p 2274) (p 2299) (p 2528) (p 2534) (p 2651) (p 3097) (p 3256) (p 3646) (p 4121) (p 4420) (p 4524) (derived73268 p h) (derived73234 p h) (derived73352 p h) (derived73436 p h) (derived72962 p h) (derived52399 p h)

theorem derived75183 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 4044) ∨ (p 2459) ∨ (¬ p 4653) ∨ (¬ p 3256) :=
  ElevenRUP.step75183 (p 2459) (p 2911) (p 3256) (p 3644) (p 4044) (p 4348) (p 4653) (derived73434 p h) (derived73562 p h) (derived41699 p h)

theorem derived75186 (p : Nat → Prop) (h : Inputs p) :
    (p 2177) ∨ (¬ p 3256) ∨ (¬ p 4044) ∨ (p 2459) ∨ (¬ p 4361) :=
  ElevenRUP.step75186 (p 2177) (p 2299) (p 2459) (p 3256) (p 4044) (p 4348) (p 4361) (derived73234 p h) (derived73562 p h) (derived62446 p h)

theorem derived75187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4548) ∨ (¬ p 3256) ∨ (p 2459) :=
  ElevenRUP.step75187 (p 2459) (p 3256) (p 4348) (p 4548) (derived73562 p h) (h 20502)

theorem derived75190 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3256) ∨ (¬ p 2850) ∨ (¬ p 4121) ∨ (p 3641) :=
  ElevenRUP.step75190 (p 2528) (p 2534) (p 2850) (p 3256) (p 3641) (p 3874) (p 4121) (derived73268 p h) (derived73484 p h) (derived47926 p h)

theorem derived75191 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3256) ∨ (¬ p 4121) ∨ (¬ p 4750) ∨ (p 3641) :=
  ElevenRUP.step75191 (p 2528) (p 2534) (p 3256) (p 3641) (p 3874) (p 4121) (p 4750) (derived73268 p h) (derived73484 p h) (derived55540 p h)

theorem derived75194 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3379) ∨ (p 2352) ∨ (¬ p 3256) ∨ (p 2459) ∨ (¬ p 4044) ∨ (¬ p 2807) ∨ (¬ p 2248) ∨ (¬ p 4503) :=
  ElevenRUP.step75194 (p 2248) (p 2352) (p 2459) (p 2493) (p 2499) (p 2807) (p 3256) (p 3379) (p 3452) (p 3956) (p 4044) (p 4348) (p 4503) (derived73260 p h) (derived73394 p h) (derived73500 p h) (derived73562 p h) (derived54120 p h)

theorem derived75204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2528) ∨ (p 2470) ∨ (¬ p 4121) ∨ (¬ p 2659) :=
  ElevenRUP.step75204 (p 2470) (p 2476) (p 2528) (p 2534) (p 2659) (p 3256) (p 4121) (derived73268 p h) (derived73250 p h) (derived41874 p h)

theorem derived75207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3005) ∨ (p 2528) ∨ (p 2630) :=
  ElevenRUP.step75207 (p 2528) (p 2534) (p 2630) (p 2810) (p 3005) (p 3256) (derived73268 p h) (derived73316 p h) (derived56301 p h)

theorem derived75216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 3146) ∨ (p 2122) ∨ (¬ p 2253) ∨ (p 2774) ∨ (¬ p 2946) ∨ (¬ p 4736) ∨ (p 2177) ∨ (¬ p 4902) ∨ (¬ p 4237) :=
  ElevenRUP.step75216 (p 2122) (p 2177) (p 2253) (p 2299) (p 2774) (p 2780) (p 2946) (p 3146) (p 3256) (p 3692) (p 3822) (p 4237) (p 4736) (p 4902) (derived73448 p h) (derived73472 p h) (derived73308 p h) (derived73234 p h) (derived54429 p h)

theorem derived75217 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3309) ∨ (¬ p 2248) ∨ (¬ p 2946) ∨ (p 3093) ∨ (p 2177) ∨ (¬ p 3256) ∨ (¬ p 4902) ∨ (¬ p 4237) :=
  ElevenRUP.step75217 (p 2177) (p 2248) (p 2299) (p 2946) (p 3093) (p 3146) (p 3256) (p 3309) (p 3549) (p 3591) (p 3692) (p 4237) (p 4902) (derived73448 p h) (derived73406 p h) (derived73432 p h) (derived73234 p h) (derived50873 p h)

theorem derived75218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2363) ∨ (¬ p 3166) ∨ (p 2946) :=
  ElevenRUP.step75218 (p 2363) (p 2946) (p 2952) (p 3166) (p 3256) (p 4347) (derived73560 p h) (derived73330 p h) (derived42704 p h)

theorem derived75219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2363) ∨ (p 2132) ∨ (¬ p 4786) ∨ (¬ p 4133) ∨ (p 2870) ∨ (p 2881) ∨ (¬ p 3166) :=
  ElevenRUP.step75219 (p 2132) (p 2138) (p 2363) (p 2870) (p 2881) (p 3166) (p 3256) (p 3570) (p 4133) (p 4244) (p 4347) (p 4786) (derived73560 p h) (derived73214 p h) (derived73540 p h) (derived73418 p h) (derived52725 p h)

theorem derived75220 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3256) ∨ (¬ p 2811) ∨ (¬ p 3166) ∨ (¬ p 2737) :=
  ElevenRUP.step75220 (p 2528) (p 2534) (p 2737) (p 2811) (p 3166) (p 3256) (derived73268 p h) (derived47517 p h)

theorem derived75224 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3166) ∨ (p 2881) ∨ (¬ p 4117) ∨ (¬ p 4729) ∨ (p 2427) ∨ (¬ p 3256) ∨ (¬ p 4133) ∨ (p 2230) :=
  ElevenRUP.step75224 (p 2230) (p 2363) (p 2427) (p 2589) (p 2881) (p 3166) (p 3256) (p 3570) (p 4117) (p 4133) (p 4235) (p 4347) (p 4729) (derived73560 p h) (derived73418 p h) (derived73536 p h) (derived73284 p h) (derived56676 p h)

theorem derived75233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2363) ∨ (¬ p 3166) ∨ (p 2331) :=
  ElevenRUP.step75233 (p 2331) (p 2363) (p 2963) (p 3166) (p 3256) (p 4347) (derived73560 p h) (derived73338 p h) (derived43611 p h)

theorem derived75234 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2255) ∨ (¬ p 3166) ∨ (p 2573) ∨ (¬ p 3256) ∨ (p 2459) ∨ (p 2352) ∨ (¬ p 2662) ∨ (¬ p 4503) :=
  ElevenRUP.step75234 (p 2255) (p 2352) (p 2459) (p 2573) (p 2579) (p 2662) (p 2727) (p 3166) (p 3256) (p 3956) (p 4111) (p 4348) (p 4503) (derived73518 p h) (derived73274 p h) (derived73562 p h) (derived73500 p h) (derived54217 p h)

theorem derived75235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (¬ p 3256) ∨ (p 2440) ∨ (p 2088) ∨ (¬ p 2474) ∨ (¬ p 2662) :=
  ElevenRUP.step75235 (p 2088) (p 2440) (p 2474) (p 2542) (p 2662) (p 3166) (p 3256) (p 3857) (derived73270 p h) (derived73480 p h) (derived45536 p h)

theorem derived75236 (p : Nat → Prop) (h : Inputs p) :
    (p 5242) ∨ (¬ p 2248) ∨ (¬ p 3166) ∨ (p 2088) ∨ (¬ p 3256) :=
  ElevenRUP.step75236 (p 2088) (p 2248) (p 3166) (p 3256) (p 3857) (p 5242) (derived73480 p h) (derived48587 p h)

theorem derived75237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3170) ∨ (¬ p 3256) ∨ (p 2088) ∨ (¬ p 2807) ∨ (¬ p 2996) :=
  ElevenRUP.step75237 (p 2088) (p 2807) (p 2996) (p 3170) (p 3256) (p 3857) (derived73480 p h) (derived55606 p h)

theorem derived75245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (p 2528) ∨ (p 2774) ∨ (p 2122) ∨ (¬ p 3256) ∨ (¬ p 4420) ∨ (p 2177) ∨ (¬ p 4786) :=
  ElevenRUP.step75245 (p 2122) (p 2177) (p 2299) (p 2528) (p 2534) (p 2774) (p 2780) (p 3166) (p 3256) (p 3822) (p 4420) (p 4786) (derived73268 p h) (derived73308 p h) (derived73472 p h) (derived73234 p h) (derived52047 p h)

theorem derived75254 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2528) ∨ (¬ p 3189) ∨ (p 2727) :=
  ElevenRUP.step75254 (p 2528) (p 2534) (p 2727) (p 3189) (p 3256) (p 4111) (derived73268 p h) (derived73518 p h) (derived64328 p h)

theorem derived75255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2528) ∨ (¬ p 2241) ∨ (¬ p 3189) :=
  ElevenRUP.step75255 (p 2241) (p 2528) (p 2534) (p 3189) (p 3256) (derived73268 p h) (derived54197 p h)

theorem derived75258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4341) ∨ (p 2363) ∨ (p 2187) :=
  ElevenRUP.step75258 (p 2187) (p 2363) (p 3256) (p 3989) (p 4341) (p 4347) (p 4560) (derived72955 p h) (derived73560 p h) (derived73502 p h) (derived50980 p h)

theorem derived75260 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3266) ∨ (¬ p 4041) ∨ (¬ p 3657) ∨ (¬ p 3256) :=
  ElevenRUP.step75260 (p 2761) (p 3256) (p 3266) (p 3657) (p 4041) (p 4381) (derived73574 p h) (derived57131 p h)

theorem derived75261 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 3266) ∨ (¬ p 3256) ∨ (¬ p 4041) ∨ (¬ p 3657) ∨ (¬ p 4623) :=
  ElevenRUP.step75261 (p 3256) (p 3266) (p 3461) (p 3657) (p 4041) (p 4191) (p 4623) (derived73530 p h) (derived42188 p h)

theorem derived75267 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 5503) ∨ (¬ p 2248) ∨ (¬ p 3256) ∨ (¬ p 3166) ∨ (¬ p 4831) ∨ (p 3379) ∨ (¬ p 3266) :=
  ElevenRUP.step75267 (p 2248) (p 2922) (p 2928) (p 3166) (p 3256) (p 3266) (p 3379) (p 3452) (p 4831) (p 5503) (derived73320 p h) (derived73394 p h) (derived48623 p h)

theorem derived75272 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3201) ∨ (¬ p 4133) ∨ (¬ p 3166) ∨ (¬ p 4736) ∨ (¬ p 2253) ∨ (¬ p 3256) ∨ (p 2598) ∨ (p 2911) :=
  ElevenRUP.step75272 (p 2253) (p 2363) (p 2598) (p 2911) (p 3055) (p 3166) (p 3201) (p 3256) (p 3644) (p 3876) (p 4133) (p 4347) (p 4736) (derived73560 p h) (derived73486 p h) (derived73350 p h) (derived73434 p h) (derived57776 p h)

theorem derived75275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 4736) ∨ (¬ p 2241) ∨ (p 2417) ∨ (¬ p 4669) ∨ (p 2598) ∨ (p 3201) :=
  ElevenRUP.step75275 (p 2241) (p 2417) (p 2598) (p 3055) (p 3189) (p 3201) (p 3256) (p 3876) (p 4278) (p 4669) (p 4736) (derived73546 p h) (derived73350 p h) (derived73486 p h) (derived59325 p h)

theorem derived75277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4341) ∨ (¬ p 3170) ∨ (p 2088) ∨ (¬ p 2249) ∨ (¬ p 2641) ∨ (¬ p 3256) :=
  ElevenRUP.step75277 (p 2088) (p 2249) (p 2641) (p 3170) (p 3256) (p 3857) (p 4341) (derived73480 p h) (derived62583 p h)

theorem derived75278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2811) ∨ (¬ p 2737) ∨ (¬ p 3166) ∨ (p 2598) ∨ (¬ p 4604) ∨ (¬ p 3256) ∨ (p 3422) ∨ (p 3564) :=
  ElevenRUP.step75278 (p 2598) (p 2737) (p 2811) (p 3055) (p 3166) (p 3256) (p 3422) (p 3564) (p 3584) (p 4137) (p 4604) (p 4734) (derived73350 p h) (derived73426 p h) (derived72735 p h) (derived73524 p h) (derived49896 p h)

theorem derived75283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3256) ∨ (p 2088) ∨ (p 2630) :=
  ElevenRUP.step75283 (p 2088) (p 2630) (p 2810) (p 3005) (p 3256) (p 3857) (derived73480 p h) (derived73316 p h) (derived43464 p h)

theorem derived75284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3170) ∨ (¬ p 3256) ∨ (¬ p 3005) ∨ (¬ p 2745) ∨ (¬ p 2252) ∨ (p 2088) :=
  ElevenRUP.step75284 (p 2088) (p 2252) (p 2745) (p 3005) (p 3170) (p 3256) (p 3857) (derived73480 p h) (derived42304 p h)

theorem derived75285 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2753) ∨ (¬ p 3166) ∨ (¬ p 3379) ∨ (¬ p 2498) ∨ (¬ p 3256) ∨ (p 2352) ∨ (p 2459) ∨ (¬ p 4117) ∨ (¬ p 4503) :=
  ElevenRUP.step75285 (p 2352) (p 2459) (p 2498) (p 2753) (p 3093) (p 3166) (p 3256) (p 3379) (p 3591) (p 3956) (p 4117) (p 4348) (p 4503) (derived73432 p h) (derived73500 p h) (derived73562 p h) (derived71264 p h)

theorem derived75288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (p 2598) ∨ (¬ p 4503) ∨ (p 2352) ∨ (p 3422) ∨ (p 2459) ∨ (¬ p 3256) ∨ (¬ p 4312) :=
  ElevenRUP.step75288 (p 2139) (p 2220) (p 2352) (p 2459) (p 2598) (p 3055) (p 3256) (p 3422) (p 3584) (p 3956) (p 4312) (p 4348) (p 4503) (derived73350 p h) (derived73500 p h) (derived73426 p h) (derived73562 p h) (derived63904 p h)

theorem derived75291 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 4171) ∨ (¬ p 3256) ∨ (¬ p 2187) ∨ (¬ p 4774) :=
  ElevenRUP.step75291 (p 2187) (p 3125) (p 3256) (p 3744) (p 4171) (p 4774) (derived73454 p h) (derived59575 p h)

theorem derived75293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (¬ p 4509) ∨ (¬ p 3256) ∨ (p 2459) :=
  ElevenRUP.step75293 (p 2284) (p 2459) (p 3156) (p 3256) (p 3952) (p 4348) (p 4509) (p 5064) (derived73902 p h) (derived73496 p h) (derived73562 p h) (derived66897 p h)

theorem derived75295 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4341) ∨ (¬ p 4976) ∨ (p 2363) ∨ (p 2553) ∨ (¬ p 3955) :=
  ElevenRUP.step75295 (p 2363) (p 2553) (p 2588) (p 3256) (p 3955) (p 4341) (p 4347) (p 4976) (derived73560 p h) (derived73282 p h) (derived52042 p h)

theorem derived75300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 2668) ∨ (p 2295) ∨ (¬ p 5559) ∨ (¬ p 3550) :=
  ElevenRUP.step75300 (p 2295) (p 2668) (p 3550) (p 3568) (p 4260) (p 5559) (derived73416 p h) (derived55163 p h)

theorem derived75309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 4260) ∨ (p 2295) ∨ (p 2352) ∨ (¬ p 4194) ∨ (¬ p 3920) :=
  ElevenRUP.step75309 (p 2295) (p 2352) (p 3568) (p 3868) (p 3920) (p 3956) (p 4194) (p 4260) (derived73416 p h) (derived73500 p h) (derived44388 p h)

theorem derived75313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 4260) ∨ (p 2352) ∨ (¬ p 3920) :=
  ElevenRUP.step75313 (p 2352) (p 3868) (p 3920) (p 3956) (p 4260) (derived73500 p h) (derived71266 p h)

theorem derived75314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 4260) ∨ (p 2187) ∨ (¬ p 3872) ∨ (p 2553) :=
  ElevenRUP.step75314 (p 2187) (p 2553) (p 2588) (p 3872) (p 3989) (p 4129) (p 4260) (derived73502 p h) (derived73282 p h) (derived56949 p h)

theorem derived75316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 4129) ∨ (p 2187) ∨ (p 2122) ∨ (¬ p 3872) :=
  ElevenRUP.step75316 (p 2122) (p 2187) (p 3822) (p 3872) (p 3989) (p 4129) (p 4260) (derived73502 p h) (derived73472 p h) (derived57880 p h)

theorem derived75317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 4129) ∨ (p 2307) ∨ (¬ p 2577) ∨ (¬ p 3872) ∨ (p 2187) :=
  ElevenRUP.step75317 (p 2187) (p 2307) (p 2313) (p 2577) (p 3872) (p 3989) (p 4129) (p 4260) (derived73238 p h) (derived73502 p h) (derived55750 p h)

theorem derived75321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2667) ∨ (¬ p 4260) ∨ (¬ p 5559) ∨ (¬ p 3550) ∨ (p 2307) ∨ (¬ p 2187) ∨ (¬ p 3986) :=
  ElevenRUP.step75321 (p 2187) (p 2307) (p 2313) (p 2667) (p 3550) (p 3986) (p 4260) (p 5559) (derived73238 p h) (derived49991 p h)

theorem derived75323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (p 2331) ∨ (p 2295) ∨ (¬ p 4831) ∨ (¬ p 3276) ∨ (p 3193) ∨ (¬ p 3379) ∨ (¬ p 2254) :=
  ElevenRUP.step75323 (p 2254) (p 2295) (p 2331) (p 2963) (p 3193) (p 3222) (p 3276) (p 3379) (p 3568) (p 4260) (p 4831) (derived73338 p h) (derived73416 p h) (derived73364 p h) (derived50815 p h)

theorem derived75327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 4260) ∨ (¬ p 3920) ∨ (¬ p 2581) ∨ (p 2307) :=
  ElevenRUP.step75327 (p 2307) (p 2313) (p 2581) (p 3868) (p 3920) (p 4260) (derived73238 p h) (derived48699 p h)

theorem derived75328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 3922) ∨ (¬ p 2727) ∨ (p 3309) ∨ (p 2331) ∨ (¬ p 4831) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 2656) ∨ (¬ p 2249) :=
  ElevenRUP.step75328 (p 2249) (p 2331) (p 2656) (p 2727) (p 2963) (p 3276) (p 3309) (p 3355) (p 3549) (p 3922) (p 4260) (p 4831) (derived73406 p h) (derived73338 p h) (derived52075 p h)

theorem derived75333 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2417) ∨ (¬ p 2177) ∨ (¬ p 3920) ∨ (¬ p 3422) :=
  ElevenRUP.step75333 (p 2177) (p 2396) (p 2417) (p 3422) (p 3920) (p 4107) (derived73514 p h) (derived43073 p h)

theorem derived75334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 2911) ∨ (p 3564) ∨ (¬ p 3920) ∨ (¬ p 2962) ∨ (p 2177) :=
  ElevenRUP.step75334 (p 2177) (p 2299) (p 2911) (p 2962) (p 3564) (p 3654) (p 3920) (p 4137) (derived73524 p h) (derived73234 p h) (derived46720 p h)

theorem derived75336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 3920) ∨ (p 2295) ∨ (¬ p 4973) ∨ (p 2177) :=
  ElevenRUP.step75336 (p 2177) (p 2295) (p 2299) (p 2911) (p 3568) (p 3920) (p 4973) (derived73416 p h) (derived73234 p h) (derived41478 p h)

theorem derived75337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (p 2307) ∨ (¬ p 2581) ∨ (p 2177) ∨ (¬ p 3920) :=
  ElevenRUP.step75337 (p 2177) (p 2299) (p 2307) (p 2313) (p 2581) (p 2911) (p 3920) (derived73238 p h) (derived73234 p h) (derived48556 p h)

theorem derived75339 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2230) ∨ (p 2352) ∨ (¬ p 2187) ∨ (¬ p 3920) :=
  ElevenRUP.step75339 (p 2187) (p 2230) (p 2352) (p 3389) (p 3540) (p 3920) (p 3956) (derived73402 p h) (derived73500 p h) (derived47717 p h)

theorem derived75342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3246) ∨ (p 2901) ∨ (¬ p 3660) ∨ (¬ p 3920) ∨ (¬ p 4702) :=
  ElevenRUP.step75342 (p 2417) (p 2901) (p 3246) (p 3660) (p 3690) (p 3920) (p 4320) (p 4702) (derived73446 p h) (derived73552 p h) (derived57430 p h)

theorem derived75347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3516) ∨ (¬ p 3920) ∨ (¬ p 2318) ∨ (p 2352) :=
  ElevenRUP.step75347 (p 2318) (p 2352) (p 2417) (p 3516) (p 3821) (p 3920) (p 3956) (derived73470 p h) (derived73500 p h) (derived71270 p h)

theorem derived75350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 5564) ∨ (p 2177) ∨ (¬ p 2307) ∨ (¬ p 3920) ∨ (¬ p 2578) ∨ (p 2352) :=
  ElevenRUP.step75350 (p 2177) (p 2307) (p 2352) (p 2578) (p 3868) (p 3920) (p 3956) (p 4500) (p 5564) (derived73602 p h) (derived73500 p h) (derived67113 p h)

theorem derived75362 (p : Nat → Prop) (h : Inputs p) :
    (p 3519) ∨ (p 3379) :=
  ElevenRUP.step75362 (p 3379) (p 3519) (p 5189) (derived73948 p h) (h 8798)

theorem derived75363 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 5190) :=
  ElevenRUP.step75363 (p 3379) (p 5189) (p 5190) (derived73948 p h) (h 8800)

theorem derived75366 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2245) :=
  ElevenRUP.step75366 (p 2241) (p 2244) (p 2245) (derived73224 p h) (h 2623)

theorem derived75367 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2246) :=
  ElevenRUP.step75367 (p 2241) (p 2244) (p 2246) (derived73224 p h) (h 2624)

theorem derived75368 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2248) :=
  ElevenRUP.step75368 (p 2241) (p 2244) (p 2248) (derived73224 p h) (h 2626)

theorem derived75369 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2249) :=
  ElevenRUP.step75369 (p 2241) (p 2244) (p 2249) (derived73224 p h) (h 2627)

theorem derived75370 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2992) ∨ (p 2307) ∨ (¬ p 3879) ∨ (¬ p 4533) ∨ (¬ p 2440) ∨ (¬ p 4198) ∨ (¬ p 2274) :=
  ElevenRUP.step75370 (p 2241) (p 2244) (p 2274) (p 2307) (p 2313) (p 2440) (p 2992) (p 3662) (p 3879) (p 4198) (p 4533) (derived73224 p h) (derived73440 p h) (derived73238 p h) (derived66717 p h)

theorem derived75372 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4445) ∨ (¬ p 4438) ∨ (¬ p 2881) ∨ (¬ p 2528) :=
  ElevenRUP.step75372 (p 2528) (p 2881) (p 3246) (p 3690) (p 4438) (p 4445) (derived73446 p h) (derived48291 p h)

theorem derived75373 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 4445) ∨ (¬ p 2177) ∨ (¬ p 2528) ∨ (¬ p 4438) :=
  ElevenRUP.step75373 (p 2177) (p 2396) (p 2528) (p 4107) (p 4438) (p 4445) (derived73514 p h) (derived53032 p h)

theorem derived75376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 4624) :=
  ElevenRUP.step75376 (p 2396) (p 4622) (p 4624) (derived73674 p h) (h 7385)

theorem derived75377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 4625) :=
  ElevenRUP.step75377 (p 2396) (p 4622) (p 4625) (derived73674 p h) (h 7386)

theorem derived75380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4386) ∨ (p 2946) ∨ (¬ p 2807) :=
  ElevenRUP.step75380 (p 2807) (p 2946) (p 2952) (p 4386) (derived73330 p h) (h 15543)

theorem derived75385 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2992) ∨ (¬ p 2807) ∨ (¬ p 2264) :=
  ElevenRUP.step75385 (p 2264) (p 2807) (p 2946) (p 2952) (p 2992) (derived73330 p h) (derived61248 p h)

theorem derived75386 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 3136) :=
  ElevenRUP.step75386 (p 2264) (p 2807) (p 2946) (p 2952) (p 3136) (derived73330 p h) (derived46980 p h)

theorem derived75388 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2946) ∨ (¬ p 2807) ∨ (¬ p 3136) :=
  ElevenRUP.step75388 (p 2797) (p 2807) (p 2946) (p 2952) (p 3136) (p 4195) (derived73532 p h) (derived73330 p h) (derived63459 p h)

theorem derived75389 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3246) ∨ (¬ p 3136) ∨ (¬ p 2807) ∨ (¬ p 4333) :=
  ElevenRUP.step75389 (p 2807) (p 2946) (p 2952) (p 3136) (p 3246) (p 4333) (derived73330 p h) (derived44221 p h)

theorem derived75392 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2630) ∨ (p 2685) ∨ (¬ p 2807) :=
  ElevenRUP.step75392 (p 2630) (p 2685) (p 2807) (p 2946) (p 2952) (p 3572) (derived73330 p h) (derived73420 p h) (derived44655 p h)

theorem derived75398 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4333) ∨ (p 2946) ∨ (¬ p 4957) ∨ (p 2891) ∨ (¬ p 2807) :=
  ElevenRUP.step75398 (p 2807) (p 2891) (p 2946) (p 2952) (p 3486) (p 4333) (p 4957) (derived73330 p h) (derived73398 p h) (derived48281 p h)

theorem derived75399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4333) ∨ (p 2946) ∨ (¬ p 4705) ∨ (¬ p 2807) ∨ (p 2427) :=
  ElevenRUP.step75399 (p 2427) (p 2807) (p 2946) (p 2952) (p 4235) (p 4333) (p 4705) (derived73330 p h) (derived73536 p h) (derived41061 p h)

theorem derived75400 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2284) ∨ (¬ p 4333) ∨ (¬ p 4558) ∨ (¬ p 2807) :=
  ElevenRUP.step75400 (p 2284) (p 2807) (p 2946) (p 2952) (p 3952) (p 4333) (p 4558) (derived73330 p h) (derived73496 p h) (derived49780 p h)

theorem derived75402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 2881) ∨ (¬ p 2248) ∨ (¬ p 4556) ∨ (p 2553) ∨ (¬ p 2807) ∨ (p 2493) ∨ (p 3379) :=
  ElevenRUP.step75402 (p 2248) (p 2264) (p 2493) (p 2499) (p 2553) (p 2588) (p 2807) (p 2881) (p 3379) (p 3452) (p 3570) (p 4556) (derived73418 p h) (derived73282 p h) (derived73260 p h) (derived73394 p h) (derived49815 p h)

theorem derived75410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 2553) ∨ (p 2573) ∨ (¬ p 2807) ∨ (¬ p 2797) ∨ (¬ p 4729) ∨ (p 2685) ∨ (¬ p 4564) ∨ (¬ p 4117) :=
  ElevenRUP.step75410 (p 2274) (p 2553) (p 2573) (p 2579) (p 2588) (p 2685) (p 2797) (p 2807) (p 3572) (p 4117) (p 4564) (p 4729) (derived73282 p h) (derived73274 p h) (derived73420 p h) (derived52205 p h)

theorem derived75414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (p 4854) :=
  ElevenRUP.step75414 (p 2807) (p 4852) (p 4854) (derived73792 p h) (h 7973)

theorem derived75418 (p : Nat → Prop) (h : Inputs p) :
    (p 4041) ∨ (¬ p 2264) :=
  ElevenRUP.step75418 (p 2264) (p 4041) (p 4551) (derived73632 p h) (h 7193)

theorem derived75420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (p 2241) ∨ (¬ p 2248) ∨ (¬ p 2807) :=
  ElevenRUP.step75420 (p 2241) (p 2247) (p 2248) (p 2807) (p 2996) (derived73226 p h) (derived48547 p h)

theorem derived75421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4625) ∨ (p 3379) ∨ (p 2493) ∨ (p 3564) ∨ (¬ p 2946) ∨ (¬ p 2901) ∨ (¬ p 2248) ∨ (¬ p 3246) :=
  ElevenRUP.step75421 (p 2248) (p 2493) (p 2499) (p 2901) (p 2946) (p 3246) (p 3379) (p 3452) (p 3564) (p 4137) (p 4625) (derived73394 p h) (derived73260 p h) (derived73524 p h) (derived60627 p h)

theorem derived75422 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3246) ∨ (p 3093) ∨ (¬ p 2946) ∨ (¬ p 2248) ∨ (¬ p 3923) ∨ (¬ p 2901) ∨ (¬ p 3950) :=
  ElevenRUP.step75422 (p 2248) (p 2363) (p 2901) (p 2946) (p 3093) (p 3246) (p 3591) (p 3923) (p 3950) (p 4347) (derived73560 p h) (derived73432 p h) (derived54885 p h)

theorem derived75426 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3016) ∨ (p 2210) ∨ (p 2274) ∨ (¬ p 2352) ∨ (p 2192) ∨ (¬ p 2248) ∨ (¬ p 4405) :=
  ElevenRUP.step75426 (p 2192) (p 2210) (p 2248) (p 2274) (p 2352) (p 2651) (p 3016) (p 3097) (p 3555) (p 4173) (p 4405) (derived73412 p h) (derived73352 p h) (derived73528 p h) (derived63756 p h)

theorem derived75431 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2911) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (p 3379) ∨ (¬ p 4133) ∨ (¬ p 2248) ∨ (p 2363) :=
  ElevenRUP.step75431 (p 2248) (p 2363) (p 2911) (p 2922) (p 2928) (p 3166) (p 3256) (p 3379) (p 3452) (p 3644) (p 4133) (p 4347) (derived73320 p h) (derived73434 p h) (derived73394 p h) (derived73560 p h) (derived52611 p h)

theorem derived75432 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3093) ∨ (¬ p 2417) ∨ (¬ p 3923) ∨ (¬ p 2248) ∨ (¬ p 3950) ∨ (¬ p 2651) ∨ (¬ p 2437) :=
  ElevenRUP.step75432 (p 2248) (p 2363) (p 2417) (p 2437) (p 2651) (p 3093) (p 3591) (p 3923) (p 3950) (p 4347) (derived73560 p h) (derived73432 p h) (derived48998 p h)

theorem derived75433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3093) ∨ (¬ p 2437) ∨ (p 3309) ∨ (¬ p 2248) ∨ (¬ p 2651) ∨ (p 2177) ∨ (¬ p 4668) :=
  ElevenRUP.step75433 (p 2177) (p 2248) (p 2299) (p 2417) (p 2437) (p 2651) (p 3093) (p 3309) (p 3549) (p 3591) (p 4668) (derived73432 p h) (derived73406 p h) (derived73234 p h) (derived56975 p h)

theorem derived75434 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 2509) ∨ (¬ p 5118) ∨ (¬ p 3156) ∨ (¬ p 2248) ∨ (¬ p 3146) ∨ (p 3379) ∨ (¬ p 2946) :=
  ElevenRUP.step75434 (p 2248) (p 2509) (p 2946) (p 3146) (p 3156) (p 3379) (p 3452) (p 4149) (p 4286) (p 5118) (derived73548 p h) (derived73394 p h) (derived57403 p h)

theorem derived75436 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2651) ∨ (¬ p 3950) ∨ (¬ p 2248) ∨ (¬ p 2417) ∨ (p 3146) ∨ (¬ p 2437) ∨ (p 2166) :=
  ElevenRUP.step75436 (p 2166) (p 2191) (p 2210) (p 2248) (p 2417) (p 2437) (p 2651) (p 3146) (p 3555) (p 3692) (p 3950) (derived73412 p h) (derived73448 p h) (derived73222 p h) (derived49135 p h)

theorem derived75442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2210) ∨ (¬ p 2295) ∨ (p 2891) ∨ (¬ p 2331) ∨ (¬ p 4668) ∨ (p 2881) ∨ (¬ p 2248) :=
  ElevenRUP.step75442 (p 2210) (p 2248) (p 2295) (p 2331) (p 2396) (p 2881) (p 2891) (p 3486) (p 3555) (p 3570) (p 4668) (derived73412 p h) (derived73398 p h) (derived73418 p h) (derived51236 p h)

theorem derived75444 (p : Nat → Prop) (h : Inputs p) :
    (p 3370) ∨ (p 2210) :=
  ElevenRUP.step75444 (p 2210) (p 3370) (p 4520) (derived73614 p h) (h 7106)

theorem derived75445 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 4521) :=
  ElevenRUP.step75445 (p 2210) (p 4520) (p 4521) (derived73614 p h) (h 7108)

theorem derived75446 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 4522) :=
  ElevenRUP.step75446 (p 2210) (p 4520) (p 4522) (derived73614 p h) (h 7109)

theorem derived75447 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2210) ∨ (p 2156) ∨ (p 2187) ∨ (p 2166) :=
  ElevenRUP.step75447 (p 2156) (p 2166) (p 2187) (p 2191) (p 2210) (p 2363) (p 3646) (p 4347) (p 4505) (p 4520) (derived73560 p h) (derived73614 p h) (derived73436 p h) (derived73606 p h) (derived73222 p h) (derived66777 p h)

theorem derived75448 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 4875) :=
  ElevenRUP.step75448 (p 2210) (p 3555) (p 4875) (derived73412 p h) (derived46340 p h)

theorem derived75450 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 2210) ∨ (¬ p 2241) ∨ (¬ p 2737) :=
  ElevenRUP.step75450 (p 2210) (p 2241) (p 2737) (p 2747) (p 2839) (p 3555) (p 4873) (derived73802 p h) (derived73412 p h) (derived73302 p h) (derived67361 p h)

theorem derived75451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 2210) ∨ (¬ p 2750) ∨ (p 2608) ∨ (¬ p 2651) ∨ (¬ p 3412) :=
  ElevenRUP.step75451 (p 2210) (p 2241) (p 2608) (p 2651) (p 2657) (p 2750) (p 3412) (p 3555) (p 3954) (derived73412 p h) (derived73498 p h) (derived73287 p h) (derived66829 p h)

theorem derived75453 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 3412) ∨ (¬ p 2727) ∨ (¬ p 2241) :=
  ElevenRUP.step75453 (p 2210) (p 2241) (p 2727) (p 3412) (p 3555) (derived73412 p h) (derived69600 p h)

theorem derived75456 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2241) ∨ (¬ p 4365) :=
  ElevenRUP.step75456 (p 2210) (p 2241) (p 3555) (p 4365) (derived73412 p h) (h 20301)

theorem derived75460 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2241) ∨ (¬ p 3412) ∨ (¬ p 3136) ∨ (¬ p 2745) :=
  ElevenRUP.step75460 (p 2210) (p 2241) (p 2745) (p 3136) (p 3412) (p 3555) (derived73412 p h) (derived41930 p h)

theorem derived75461 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2210) ∨ (p 2187) ∨ (p 2192) :=
  ElevenRUP.step75461 (p 2187) (p 2192) (p 2210) (p 2363) (p 3555) (p 3989) (p 4173) (p 4347) (derived73560 p h) (derived73412 p h) (derived73502 p h) (derived73528 p h) (derived44977 p h)

theorem derived75463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 2210) ∨ (p 2274) ∨ (p 2192) :=
  ElevenRUP.step75463 (p 2192) (p 2210) (p 2241) (p 2274) (p 3097) (p 3555) (p 4173) (derived73412 p h) (derived73352 p h) (derived73528 p h) (derived64809 p h)

theorem derived75465 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2192) ∨ (¬ p 2563) ∨ (¬ p 2241) :=
  ElevenRUP.step75465 (p 2192) (p 2210) (p 2241) (p 2563) (p 3555) (p 4173) (derived73412 p h) (derived73528 p h) (derived42642 p h)

theorem derived75467 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2850) ∨ (p 2210) ∨ (¬ p 2753) ∨ (¬ p 2598) ∨ (¬ p 2563) ∨ (¬ p 3093) ∨ (¬ p 4870) ∨ (¬ p 4555) :=
  ElevenRUP.step75467 (p 2210) (p 2563) (p 2598) (p 2753) (p 2850) (p 2891) (p 3093) (p 3486) (p 3555) (p 4555) (p 4870) (derived73398 p h) (derived73412 p h) (derived61622 p h)

theorem derived75469 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2210) ∨ (¬ p 2177) ∨ (p 2891) :=
  ElevenRUP.step75469 (p 2177) (p 2210) (p 2881) (p 2891) (p 3486) (p 3555) (p 3570) (derived73418 p h) (derived73412 p h) (derived73398 p h) (derived44964 p h)

theorem derived75471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3246) ∨ (¬ p 4669) ∨ (¬ p 3083) ∨ (p 2210) ∨ (p 2891) ∨ (¬ p 2651) ∨ (¬ p 2248) :=
  ElevenRUP.step75471 (p 2210) (p 2248) (p 2528) (p 2651) (p 2891) (p 3083) (p 3246) (p 3486) (p 3555) (p 3690) (p 4669) (derived73446 p h) (derived73412 p h) (derived73398 p h) (derived57778 p h)

theorem derived75473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (p 2210) ∨ (p 2891) ∨ (p 2881) :=
  ElevenRUP.step75473 (p 2210) (p 2881) (p 2891) (p 2911) (p 3486) (p 3555) (p 3570) (derived73412 p h) (derived73398 p h) (derived73418 p h) (derived58572 p h)

theorem derived75474 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (p 3246) ∨ (p 2891) ∨ (¬ p 2911) ∨ (p 2210) ∨ (¬ p 2248) ∨ (¬ p 2651) ∨ (¬ p 4666) :=
  ElevenRUP.step75474 (p 2210) (p 2248) (p 2437) (p 2651) (p 2891) (p 2911) (p 3246) (p 3486) (p 3555) (p 3690) (p 4666) (derived73446 p h) (derived73398 p h) (derived73412 p h) (derived48865 p h)

theorem derived75475 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 2210) ∨ (p 3246) ∨ (¬ p 2651) ∨ (p 2891) ∨ (¬ p 3016) ∨ (¬ p 4621) ∨ (¬ p 2248) :=
  ElevenRUP.step75475 (p 2210) (p 2248) (p 2651) (p 2891) (p 3016) (p 3246) (p 3486) (p 3555) (p 3564) (p 3690) (p 4621) (derived73412 p h) (derived73446 p h) (derived73398 p h) (derived64167 p h)

theorem derived75476 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2284) ∨ (¬ p 2608) ∨ (p 2210) :=
  ElevenRUP.step75476 (p 2192) (p 2210) (p 2284) (p 2608) (p 3555) (p 4173) (derived73528 p h) (derived73412 p h) (derived46321 p h)

theorem derived75477 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2284) ∨ (¬ p 2241) ∨ (p 2210) :=
  ElevenRUP.step75477 (p 2192) (p 2210) (p 2241) (p 2284) (p 3555) (p 4173) (derived73528 p h) (derived73412 p h) (derived47854 p h)

theorem derived75479 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2295) ∨ (p 3146) ∨ (¬ p 3950) ∨ (p 2210) ∨ (p 2166) ∨ (¬ p 2331) ∨ (¬ p 2248) :=
  ElevenRUP.step75479 (p 2166) (p 2191) (p 2210) (p 2248) (p 2295) (p 2331) (p 2396) (p 3146) (p 3555) (p 3692) (p 3950) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived48837 p h)

theorem derived75481 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2363) ∨ (p 2210) ∨ (p 2891) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 4669) ∨ (p 3246) :=
  ElevenRUP.step75481 (p 2210) (p 2248) (p 2331) (p 2363) (p 2668) (p 2891) (p 3246) (p 3486) (p 3555) (p 3690) (p 4669) (derived73412 p h) (derived73398 p h) (derived73446 p h) (derived52189 p h)

theorem derived75484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2210) ∨ (¬ p 2608) ∨ (p 2972) ∨ (¬ p 2246) ∨ (¬ p 5059) ∨ (¬ p 2744) ∨ (¬ p 2331) ∨ (¬ p 2363) :=
  ElevenRUP.step75484 (p 2210) (p 2246) (p 2331) (p 2363) (p 2608) (p 2668) (p 2744) (p 2972) (p 3555) (p 4363) (p 5059) (derived73412 p h) (derived73568 p h) (derived60100 p h)

theorem derived75486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 2248) ∨ (p 2192) ∨ (¬ p 4604) ∨ (p 2210) ∨ (¬ p 2459) ∨ (p 3125) :=
  ElevenRUP.step75486 (p 2192) (p 2210) (p 2248) (p 2264) (p 2459) (p 2807) (p 3125) (p 3555) (p 3744) (p 4173) (p 4604) (derived73528 p h) (derived73412 p h) (derived73454 p h) (derived49116 p h)

theorem derived75488 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 3156) ∨ (¬ p 2608) ∨ (p 2210) :=
  ElevenRUP.step75488 (p 2166) (p 2191) (p 2210) (p 2608) (p 3156) (p 3555) (derived73222 p h) (derived73412 p h) (derived47236 p h)

theorem derived75489 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 3156) ∨ (p 2284) ∨ (p 2210) :=
  ElevenRUP.step75489 (p 2166) (p 2191) (p 2210) (p 2284) (p 3156) (p 3555) (p 3952) (derived73222 p h) (derived73496 p h) (derived73412 p h) (derived56141 p h)

theorem derived75493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 3461) ∨ (p 2166) ∨ (p 2210) ∨ (¬ p 2331) ∨ (¬ p 4421) ∨ (p 3246) ∨ (¬ p 4621) ∨ (¬ p 2248) ∨ (¬ p 3747) :=
  ElevenRUP.step75493 (p 2166) (p 2191) (p 2210) (p 2248) (p 2331) (p 3246) (p 3461) (p 3506) (p 3555) (p 3690) (p 3747) (p 4191) (p 4421) (p 4621) (derived73530 p h) (derived73222 p h) (derived73412 p h) (derived73446 p h) (derived53985 p h)

theorem derived75496 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2210) ∨ (p 2891) ∨ (¬ p 2459) ∨ (¬ p 4119) :=
  ElevenRUP.step75496 (p 2210) (p 2459) (p 2891) (p 3146) (p 3486) (p 3555) (p 3692) (p 4119) (derived73448 p h) (derived73412 p h) (derived73398 p h) (derived48606 p h)

theorem derived75497 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2761) ∨ (p 2891) ∨ (p 2210) :=
  ElevenRUP.step75497 (p 2210) (p 2761) (p 2891) (p 3246) (p 3486) (p 3555) (p 3690) (p 4381) (derived73446 p h) (derived73574 p h) (derived73398 p h) (derived73412 p h) (derived45936 p h)

theorem derived75499 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4075) ∨ (p 3276) ∨ (¬ p 4826) ∨ (p 3343) ∨ (¬ p 2741) ∨ (p 2210) ∨ (p 2651) ∨ (¬ p 2252) ∨ (¬ p 4377) ∨ (¬ p 3399) :=
  ElevenRUP.step75499 (p 2210) (p 2252) (p 2651) (p 2657) (p 2741) (p 3276) (p 3343) (p 3359) (p 3399) (p 3555) (p 4075) (p 4377) (p 4425) (p 4826) (derived73578 p h) (derived73388 p h) (derived73412 p h) (derived73288 p h) (derived64512 p h)

theorem derived75502 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2901) ∨ (p 2210) ∨ (p 2284) :=
  ElevenRUP.step75502 (p 2210) (p 2284) (p 2891) (p 2901) (p 3486) (p 3555) (p 3952) (derived73398 p h) (derived73412 p h) (derived73496 p h) (derived44967 p h)

theorem derived75503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2210) ∨ (¬ p 2573) ∨ (¬ p 2248) ∨ (p 3246) ∨ (¬ p 4389) ∨ (¬ p 2663) ∨ (¬ p 4666) ∨ (¬ p 2177) ∨ (p 2891) :=
  ElevenRUP.step75503 (p 2177) (p 2210) (p 2248) (p 2295) (p 2573) (p 2663) (p 2891) (p 3246) (p 3486) (p 3555) (p 3690) (p 4389) (p 4666) (derived73412 p h) (derived73446 p h) (derived73398 p h) (derived57215 p h)

theorem derived75504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 2210) ∨ (¬ p 3571) ∨ (¬ p 4960) ∨ (p 2901) :=
  ElevenRUP.step75504 (p 2210) (p 2901) (p 3399) (p 3555) (p 3571) (p 4320) (p 4960) (derived73412 p h) (derived73552 p h) (derived48312 p h)

theorem derived75505 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2274) ∨ (¬ p 4034) ∨ (¬ p 3379) ∨ (p 2563) :=
  ElevenRUP.step75505 (p 2210) (p 2274) (p 2563) (p 3097) (p 3379) (p 3555) (p 4034) (p 4110) (derived73412 p h) (derived73352 p h) (derived73516 p h) (derived62896 p h)

theorem derived75506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 2210) ∨ (p 2563) ∨ (p 2972) :=
  ElevenRUP.step75506 (p 2210) (p 2563) (p 2972) (p 2982) (p 3555) (p 4110) (p 4363) (derived73412 p h) (derived73516 p h) (derived73568 p h) (derived44081 p h)

theorem derived75508 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 3379) ∨ (p 2427) ∨ (¬ p 4034) ∨ (p 2881) :=
  ElevenRUP.step75508 (p 2210) (p 2427) (p 2881) (p 3379) (p 3555) (p 3570) (p 4034) (p 4235) (derived73412 p h) (derived73536 p h) (derived73418 p h) (derived43893 p h)

theorem derived75510 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 2210) ∨ (p 2427) ∨ (¬ p 2563) :=
  ElevenRUP.step75510 (p 2192) (p 2210) (p 2427) (p 2563) (p 3555) (p 4173) (p 4235) (derived73528 p h) (derived73412 p h) (derived73536 p h) (derived43891 p h)

theorem derived75514 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2573) ∨ (p 2210) ∨ (¬ p 4257) ∨ (¬ p 4079) ∨ (¬ p 4377) :=
  ElevenRUP.step75514 (p 2210) (p 2493) (p 2499) (p 2573) (p 3555) (p 4079) (p 4257) (p 4377) (derived73260 p h) (derived73412 p h) (derived42216 p h)

theorem derived75516 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2210) ∨ (¬ p 4257) ∨ (¬ p 4079) ∨ (¬ p 3389) ∨ (¬ p 4377) :=
  ElevenRUP.step75516 (p 2210) (p 2922) (p 2928) (p 3389) (p 3555) (p 4079) (p 4257) (p 4377) (derived73320 p h) (derived73412 p h) (derived42396 p h)

theorem derived75520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (p 2210) ∨ (p 2440) ∨ (¬ p 4811) :=
  ElevenRUP.step75520 (p 2210) (p 2440) (p 2542) (p 3379) (p 3555) (p 4811) (derived73412 p h) (derived73270 p h) (derived68354 p h)

theorem derived75522 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2437) ∨ (p 2881) ∨ (¬ p 4668) ∨ (¬ p 2417) ∨ (¬ p 2248) ∨ (p 2210) ∨ (¬ p 2651) :=
  ElevenRUP.step75522 (p 2210) (p 2248) (p 2417) (p 2437) (p 2651) (p 2881) (p 2891) (p 3486) (p 3555) (p 3570) (p 4668) (derived73398 p h) (derived73418 p h) (derived73412 p h) (derived51235 p h)

theorem derived75524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4341) ∨ (p 2363) ∨ (p 2881) ∨ (p 2891) ∨ (¬ p 2331) ∨ (¬ p 2248) ∨ (¬ p 4133) ∨ (p 2210) :=
  ElevenRUP.step75524 (p 2210) (p 2248) (p 2331) (p 2363) (p 2881) (p 2891) (p 3256) (p 3486) (p 3555) (p 3570) (p 4133) (p 4341) (p 4347) (derived73560 p h) (derived73418 p h) (derived73398 p h) (derived73412 p h) (derived49118 p h)

theorem derived75525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 4322) ∨ (p 2210) ∨ (p 2972) ∨ (¬ p 2295) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 4826) :=
  ElevenRUP.step75525 (p 2210) (p 2248) (p 2295) (p 2331) (p 2972) (p 3555) (p 3791) (p 4322) (p 4363) (p 4826) (derived73412 p h) (derived73568 p h) (derived48836 p h)

theorem derived75528 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2427) ∨ (p 2373) ∨ (p 2210) :=
  ElevenRUP.step75528 (p 2210) (p 2373) (p 2427) (p 2891) (p 3486) (p 3555) (p 3880) (derived73398 p h) (derived73490 p h) (derived73412 p h) (derived44052 p h)

theorem derived75529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 5118) ∨ (p 2210) ∨ (¬ p 2264) ∨ (p 2166) ∨ (¬ p 2807) ∨ (¬ p 2459) ∨ (¬ p 2248) :=
  ElevenRUP.step75529 (p 2166) (p 2191) (p 2210) (p 2248) (p 2264) (p 2459) (p 2807) (p 3555) (p 5118) (p 5568) (derived73412 p h) (derived73222 p h) (derived51081 p h)

theorem derived75530 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3276) ∨ (¬ p 2651) ∨ (p 2166) ∨ (p 2210) ∨ (¬ p 2248) ∨ (¬ p 3343) ∨ (¬ p 5123) :=
  ElevenRUP.step75530 (p 2166) (p 2191) (p 2210) (p 2248) (p 2651) (p 3276) (p 3343) (p 3555) (p 5123) (p 5568) (derived73222 p h) (derived73412 p h) (derived49194 p h)

theorem derived75531 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3286) ∨ (¬ p 3506) ∨ (¬ p 5059) ∨ (p 3266) ∨ (p 2982) ∨ (¬ p 2246) ∨ (¬ p 4034) :=
  ElevenRUP.step75531 (p 2210) (p 2246) (p 2608) (p 2744) (p 2982) (p 3266) (p 3286) (p 3506) (p 3555) (p 4034) (p 4444) (p 4948) (p 5059) (derived73412 p h) (derived73580 p h) (derived73846 p h) (derived52778 p h)

theorem derived75532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2761) ∨ (p 2210) ∨ (p 2972) :=
  ElevenRUP.step75532 (p 2210) (p 2761) (p 2972) (p 3555) (p 4322) (p 4363) (derived73412 p h) (derived73568 p h) (derived58074 p h)

theorem derived75533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3266) ∨ (p 2210) ∨ (p 2972) :=
  ElevenRUP.step75533 (p 2210) (p 2972) (p 3266) (p 3555) (p 4322) (p 4363) (derived73412 p h) (derived73568 p h) (derived45568 p h)

theorem derived75536 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2210) ∨ (¬ p 2573) ∨ (p 2881) ∨ (¬ p 5190) ∨ (¬ p 4420) ∨ (p 2891) ∨ (¬ p 3083) :=
  ElevenRUP.step75536 (p 2210) (p 2573) (p 2881) (p 2891) (p 3016) (p 3083) (p 3486) (p 3555) (p 3570) (p 3574) (p 4420) (p 5190) (derived73422 p h) (derived73412 p h) (derived73418 p h) (derived73398 p h) (derived56471 p h)

theorem derived75538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 4442) ∨ (p 2881) ∨ (p 2210) ∨ (¬ p 3554) :=
  ElevenRUP.step75538 (p 2210) (p 2881) (p 3554) (p 3555) (p 3570) (p 4129) (p 4442) (derived73418 p h) (derived73412 p h) (derived47891 p h)

theorem derived75541 (p : Nat → Prop) (h : Inputs p) :
    (p 4376) ∨ (p 3367) :=
  ElevenRUP.step75541 (p 3367) (p 4376) (p 5213) (derived73960 p h) (h 8854)

theorem derived75542 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 5214) :=
  ElevenRUP.step75542 (p 3367) (p 5213) (p 5214) (derived73960 p h) (h 8855)

theorem derived75543 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 5217) :=
  ElevenRUP.step75543 (p 3367) (p 3585) (p 5217) (derived73428 p h) (derived42801 p h)

theorem derived75544 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (p 2850) ∨ (p 3367) ∨ (p 2563) :=
  ElevenRUP.step75544 (p 2274) (p 2563) (p 2850) (p 3097) (p 3367) (p 3585) (p 3684) (p 4110) (derived73352 p h) (derived73442 p h) (derived73428 p h) (derived73516 p h) (derived42991 p h)

theorem derived75545 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 3363) ∨ (p 3367) ∨ (p 2881) ∨ (p 2230) :=
  ElevenRUP.step75545 (p 2230) (p 2427) (p 2589) (p 2881) (p 3363) (p 3367) (p 3570) (p 3585) (p 4235) (derived73536 p h) (derived73428 p h) (derived73418 p h) (derived73284 p h) (derived42816 p h)

theorem derived75548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 2982) ∨ (p 3367) ∨ (¬ p 3363) ∨ (p 2230) :=
  ElevenRUP.step75548 (p 2230) (p 2589) (p 2982) (p 3363) (p 3367) (p 3585) (p 4322) (p 4948) (derived73846 p h) (derived73428 p h) (derived73284 p h) (derived45392 p h)

theorem derived75550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2470) ∨ (¬ p 3083) ∨ (p 3367) ∨ (¬ p 3363) :=
  ElevenRUP.step75550 (p 2470) (p 2476) (p 2829) (p 3083) (p 3363) (p 3367) (p 3585) (derived73250 p h) (derived73428 p h) (derived46519 p h)

theorem derived75551 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (p 2363) ∨ (p 2352) ∨ (¬ p 3363) ∨ (p 3367) :=
  ElevenRUP.step75551 (p 2352) (p 2363) (p 2573) (p 2579) (p 3363) (p 3367) (p 3585) (p 3956) (p 4347) (derived73274 p h) (derived73560 p h) (derived73500 p h) (derived73428 p h) (derived45351 p h)

theorem derived75552 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 3363) ∨ (p 3367) ∨ (p 2156) ∨ (¬ p 2563) ∨ (¬ p 3904) :=
  ElevenRUP.step75552 (p 2156) (p 2427) (p 2563) (p 3363) (p 3367) (p 3585) (p 3646) (p 3904) (p 4235) (derived73536 p h) (derived73428 p h) (derived73436 p h) (derived43011 p h)

theorem derived75554 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (p 2440) ∨ (p 3367) ∨ (p 2230) ∨ (¬ p 3363) :=
  ElevenRUP.step75554 (p 2230) (p 2437) (p 2440) (p 2542) (p 2589) (p 3363) (p 3367) (p 3585) (p 3742) (derived73452 p h) (derived73270 p h) (derived73428 p h) (derived73284 p h) (derived43004 p h)

theorem derived75555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (p 3051) ∨ (¬ p 2598) ∨ (p 3367) ∨ (¬ p 2427) :=
  ElevenRUP.step75555 (p 2136) (p 2427) (p 2598) (p 3051) (p 3367) (p 3556) (p 3585) (derived73414 p h) (derived73428 p h) (derived45385 p h)

theorem derived75556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (p 2553) ∨ (p 3367) ∨ (¬ p 3363) ∨ (p 2573) :=
  ElevenRUP.step75556 (p 2553) (p 2573) (p 2579) (p 2588) (p 2737) (p 3363) (p 3367) (p 3585) (derived73282 p h) (derived73428 p h) (derived73274 p h) (derived45615 p h)

theorem derived75560 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2656) ∨ (p 3367) ∨ (¬ p 2737) ∨ (¬ p 3363) ∨ (p 2437) :=
  ElevenRUP.step75560 (p 2417) (p 2437) (p 2656) (p 2737) (p 3363) (p 3367) (p 3585) (p 3742) (p 4278) (derived73546 p h) (derived73428 p h) (derived73452 p h) (derived46995 p h)

theorem derived75561 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (p 3564) ∨ (p 3367) ∨ (p 3422) :=
  ElevenRUP.step75561 (p 3367) (p 3422) (p 3461) (p 3564) (p 3584) (p 3585) (p 4137) (p 4191) (derived73530 p h) (derived73524 p h) (derived73428 p h) (derived73426 p h) (derived42998 p h)

theorem derived75563 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) ∨ (p 3422) ∨ (p 2177) ∨ (p 3367) :=
  ElevenRUP.step75563 (p 2177) (p 2299) (p 2553) (p 2588) (p 3367) (p 3422) (p 3584) (p 3585) (derived73282 p h) (derived73426 p h) (derived73234 p h) (derived73428 p h) (derived43890 p h)

theorem derived75567 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3422) ∨ (¬ p 2363) ∨ (p 3367) ∨ (¬ p 3573) :=
  ElevenRUP.step75567 (p 2363) (p 2528) (p 2534) (p 3367) (p 3422) (p 3573) (p 3584) (p 3585) (derived73268 p h) (derived73426 p h) (derived73428 p h) (derived43037 p h)

theorem derived75569 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3016) ∨ (p 2573) ∨ (¬ p 3363) ∨ (p 3367) :=
  ElevenRUP.step75569 (p 2573) (p 2579) (p 2737) (p 3016) (p 3363) (p 3367) (p 3585) (derived73274 p h) (derived73428 p h) (derived63258 p h)

theorem derived75570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 3641) ∨ (p 3367) ∨ (¬ p 2440) :=
  ElevenRUP.step75570 (p 2440) (p 3083) (p 3367) (p 3585) (p 3641) (p 3874) (derived73484 p h) (derived73428 p h) (derived45899 p h)

theorem derived75572 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3389) ∨ (¬ p 2459) ∨ (p 3367) ∨ (¬ p 4186) ∨ (¬ p 3363) :=
  ElevenRUP.step75572 (p 2459) (p 2528) (p 2534) (p 3363) (p 3367) (p 3389) (p 3540) (p 3585) (p 4186) (derived73268 p h) (derived73402 p h) (derived73428 p h) (derived44742 p h)

theorem derived75575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2742) ∨ (¬ p 2901) ∨ (¬ p 4647) ∨ (¬ p 2992) ∨ (¬ p 5197) ∨ (p 3367) ∨ (p 2341) ∨ (¬ p 2696) ∨ (¬ p 3363) :=
  ElevenRUP.step75575 (p 2341) (p 2696) (p 2742) (p 2901) (p 2911) (p 2992) (p 3363) (p 3367) (p 3551) (p 3585) (p 4647) (p 5197) (derived73428 p h) (derived73408 p h) (derived71277 p h)

theorem derived75576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (¬ p 3577) ∨ (¬ p 2911) ∨ (¬ p 2707) ∨ (¬ p 2459) ∨ (p 3367) :=
  ElevenRUP.step75576 (p 2459) (p 2707) (p 2911) (p 3367) (p 3577) (p 3585) (p 4279) (derived73428 p h) (derived55692 p h)

theorem derived75577 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 2996) ∨ (¬ p 2749) ∨ (¬ p 4749) ∨ (¬ p 3361) ∨ (p 2807) :=
  ElevenRUP.step75577 (p 2749) (p 2807) (p 2996) (p 3027) (p 3361) (p 3367) (p 3414) (p 3585) (p 4749) (derived73428 p h) (derived73340 p h) (derived73392 p h) (derived42071 p h)

theorem derived75578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3201) ∨ (p 2911) ∨ (p 3367) :=
  ElevenRUP.step75578 (p 2341) (p 2911) (p 3201) (p 3367) (p 3585) (p 3644) (p 3876) (derived73486 p h) (derived73434 p h) (derived73428 p h) (derived42854 p h)

theorem derived75579 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 3201) ∨ (p 2911) ∨ (p 3367) :=
  ElevenRUP.step75579 (p 2608) (p 2911) (p 3201) (p 3367) (p 3585) (p 3644) (p 3876) (p 3954) (derived73498 p h) (derived73486 p h) (derived73434 p h) (derived73428 p h) (derived45543 p h)

theorem derived75583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2992) ∨ (p 2573) ∨ (¬ p 3363) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (p 3367) ∨ (p 2553) ∨ (¬ p 4556) :=
  ElevenRUP.step75583 (p 2553) (p 2573) (p 2579) (p 2588) (p 2696) (p 2742) (p 2901) (p 2992) (p 3363) (p 3367) (p 3585) (p 4556) (derived73274 p h) (derived73428 p h) (derived73282 p h) (derived71278 p h)

theorem derived75584 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3422) ∨ (p 2352) ∨ (p 3367) :=
  ElevenRUP.step75584 (p 2352) (p 2363) (p 3367) (p 3422) (p 3584) (p 3585) (p 3956) (p 4347) (derived73560 p h) (derived73426 p h) (derived73500 p h) (derived73428 p h) (derived54029 p h)

theorem derived75586 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2459) ∨ (p 3389) ∨ (¬ p 3363) ∨ (p 3367) :=
  ElevenRUP.step75586 (p 2459) (p 2911) (p 3363) (p 3367) (p 3389) (p 3540) (p 3585) (p 3644) (p 4348) (derived73434 p h) (derived73562 p h) (derived73402 p h) (derived73428 p h) (derived43272 p h)

theorem derived75587 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3425) ∨ (¬ p 4106) ∨ (p 3367) ∨ (¬ p 2598) :=
  ElevenRUP.step75587 (p 2598) (p 2911) (p 3367) (p 3425) (p 3585) (p 3644) (p 4106) (derived73434 p h) (derived73428 p h) (derived47006 p h)

theorem derived75589 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 2470) ∨ (¬ p 3363) ∨ (p 3367) ∨ (¬ p 3146) :=
  ElevenRUP.step75589 (p 2470) (p 2476) (p 2528) (p 2534) (p 3146) (p 3363) (p 3367) (p 3585) (derived73268 p h) (derived73250 p h) (derived73428 p h) (derived45696 p h)

theorem derived75590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2608) ∨ (¬ p 2248) ∨ (p 3367) ∨ (p 2668) ∨ (p 3201) ∨ (¬ p 2383) ∨ (¬ p 3987) ∨ (¬ p 4712) :=
  ElevenRUP.step75590 (p 2248) (p 2295) (p 2383) (p 2608) (p 2668) (p 3201) (p 3324) (p 3367) (p 3585) (p 3876) (p 3954) (p 3987) (p 4712) (derived73498 p h) (derived73428 p h) (derived73386 p h) (derived73486 p h) (derived49468 p h)

theorem derived75591 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3367) ∨ (p 2373) ∨ (p 2230) ∨ (¬ p 3363) :=
  ElevenRUP.step75591 (p 2230) (p 2373) (p 2589) (p 3146) (p 3363) (p 3367) (p 3585) (p 3692) (p 3880) (derived73448 p h) (derived73428 p h) (derived73490 p h) (derived73284 p h) (derived45225 p h)

theorem derived75593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4424) ∨ (p 2427) ∨ (p 3425) ∨ (¬ p 4559) ∨ (¬ p 3363) ∨ (p 2177) ∨ (p 3367) ∨ (¬ p 3527) ∨ (p 2230) :=
  ElevenRUP.step75593 (p 2177) (p 2230) (p 2299) (p 2427) (p 2589) (p 3363) (p 3367) (p 3425) (p 3471) (p 3527) (p 3585) (p 4235) (p 4424) (p 4559) (derived73536 p h) (derived73396 p h) (derived73234 p h) (derived73428 p h) (derived73284 p h) (derived71279 p h)

theorem derived75594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (¬ p 2274) ∨ (¬ p 2156) ∨ (¬ p 4438) ∨ (¬ p 4377) ∨ (¬ p 5368) ∨ (¬ p 2528) ∨ (¬ p 2177) ∨ (p 3367) ∨ (p 3609) :=
  ElevenRUP.step75594 (p 2156) (p 2177) (p 2274) (p 2528) (p 3367) (p 3370) (p 3585) (p 3609) (p 4340) (p 4377) (p 4438) (p 5368) (derived73428 p h) (derived73558 p h) (derived48922 p h)

theorem derived75597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3687) ∨ (¬ p 5086) ∨ (p 2341) ∨ (¬ p 3959) ∨ (p 3367) :=
  ElevenRUP.step75597 (p 2341) (p 3367) (p 3527) (p 3551) (p 3585) (p 3687) (p 3959) (p 5086) (derived73408 p h) (derived73428 p h) (derived41906 p h)

theorem derived75598 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3641) ∨ (p 2608) ∨ (p 3367) :=
  ElevenRUP.step75598 (p 2528) (p 2534) (p 2608) (p 3367) (p 3585) (p 3641) (p 3874) (p 3954) (derived73268 p h) (derived73484 p h) (derived73498 p h) (derived73428 p h) (derived43516 p h)

theorem derived75600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (p 3016) ∨ (p 3389) ∨ (p 3367) ∨ (¬ p 3363) :=
  ElevenRUP.step75600 (p 2437) (p 3016) (p 3363) (p 3367) (p 3389) (p 3540) (p 3574) (p 3585) (derived73422 p h) (derived73402 p h) (derived73428 p h) (derived46819 p h)

theorem derived75601 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (p 3609) ∨ (p 3367) ∨ (p 2553) ∨ (¬ p 2528) ∨ (¬ p 5368) :=
  ElevenRUP.step75601 (p 2510) (p 2528) (p 2553) (p 2588) (p 3367) (p 3585) (p 3609) (p 4340) (p 5368) (derived73558 p h) (derived73428 p h) (derived73282 p h) (derived48924 p h)

theorem derived75602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5160) ∨ (¬ p 2187) ∨ (p 2608) ∨ (¬ p 4521) ∨ (p 3367) ∨ (¬ p 2363) ∨ (¬ p 4697) ∨ (¬ p 2156) :=
  ElevenRUP.step75602 (p 2156) (p 2187) (p 2363) (p 2608) (p 3367) (p 3585) (p 3954) (p 4521) (p 4697) (p 5160) (derived73498 p h) (derived73428 p h) (derived51667 p h)

theorem derived75603 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 3125) ∨ (¬ p 2663) ∨ (¬ p 2132) ∨ (¬ p 4437) ∨ (¬ p 2192) ∨ (p 3367) ∨ (¬ p 3363) ∨ (¬ p 4330) ∨ (¬ p 4418) ∨ (p 2528) :=
  ElevenRUP.step75603 (p 2132) (p 2192) (p 2528) (p 2534) (p 2663) (p 3125) (p 3166) (p 3172) (p 3363) (p 3367) (p 3585) (p 4330) (p 4418) (p 4437) (derived73356 p h) (derived73428 p h) (derived73268 p h) (derived71280 p h)

theorem derived75607 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3266) ∨ (¬ p 3363) ∨ (p 3367) ∨ (¬ p 3346) :=
  ElevenRUP.step75607 (p 3266) (p 3276) (p 3346) (p 3363) (p 3367) (p 3585) (p 4425) (derived73578 p h) (derived73428 p h) (derived54916 p h)

theorem derived75613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 2417) ∨ (¬ p 3658) ∨ (¬ p 2761) ∨ (p 3425) ∨ (p 3367) :=
  ElevenRUP.step75613 (p 2417) (p 2753) (p 2761) (p 3367) (p 3425) (p 3471) (p 3585) (p 3658) (derived73396 p h) (derived73428 p h) (derived46411 p h)

theorem derived75614 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 2608) ∨ (p 3201) ∨ (p 3367) :=
  ElevenRUP.step75614 (p 2417) (p 2608) (p 3201) (p 3367) (p 3585) (p 3876) (p 3954) (p 4278) (derived73546 p h) (derived73498 p h) (derived73486 p h) (derived73428 p h) (derived43518 p h)

theorem derived75617 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2992) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (p 2850) ∨ (¬ p 4717) ∨ (p 2946) ∨ (p 3367) :=
  ElevenRUP.step75617 (p 2608) (p 2651) (p 2850) (p 2946) (p 2952) (p 2992) (p 3016) (p 3367) (p 3585) (p 3684) (p 3954) (p 4717) (derived73498 p h) (derived73442 p h) (derived73330 p h) (derived73428 p h) (derived58499 p h)

theorem derived75620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3654) ∨ (p 3367) ∨ (¬ p 3363) ∨ (p 2553) ∨ (¬ p 2577) :=
  ElevenRUP.step75620 (p 2553) (p 2577) (p 2588) (p 3363) (p 3367) (p 3564) (p 3585) (p 3654) (p 3946) (derived73492 p h) (derived73428 p h) (derived73282 p h) (derived62292 p h)

theorem derived75621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2122) ∨ (p 3367) ∨ (p 2553) :=
  ElevenRUP.step75621 (p 2122) (p 2553) (p 2588) (p 2829) (p 3367) (p 3585) (derived73428 p h) (derived73282 p h) (derived53318 p h)

theorem derived75622 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3680) ∨ (¬ p 3363) ∨ (p 3367) ∨ (¬ p 3346) :=
  ElevenRUP.step75622 (p 3276) (p 3346) (p 3363) (p 3367) (p 3585) (p 3680) (p 4425) (derived73578 p h) (derived73428 p h) (derived59848 p h)

theorem derived75624 (p : Nat → Prop) (h : Inputs p) :
    (p 3873) ∨ (p 2608) :=
  ElevenRUP.step75624 (p 2608) (p 3873) (p 4732) (derived73732 p h) (h 7679)

theorem derived75626 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 4733) :=
  ElevenRUP.step75626 (p 2608) (p 4732) (p 4733) (derived73732 p h) (h 7682)

theorem derived75627 (p : Nat → Prop) (h : Inputs p) :
    (p 2744) ∨ (p 2608) :=
  ElevenRUP.step75627 (p 2608) (p 2744) (p 3954) (derived73498 p h) (derived42705 p h)

theorem derived75628 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 4376) :=
  ElevenRUP.step75628 (p 2608) (p 3954) (p 4376) (derived73498 p h) (derived46679 p h)

theorem derived75629 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 4866) :=
  ElevenRUP.step75629 (p 2608) (p 3954) (p 4866) (derived73498 p h) (derived47133 p h)

theorem derived75630 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 4377) :=
  ElevenRUP.step75630 (p 2608) (p 3954) (p 4377) (derived73498 p h) (derived47394 p h)

theorem derived75631 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 4736) :=
  ElevenRUP.step75631 (p 2608) (p 3954) (p 4736) (derived73498 p h) (derived48285 p h)

theorem derived75632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2741) ∨ (p 2608) ∨ (¬ p 2241) :=
  ElevenRUP.step75632 (p 2241) (p 2608) (p 2741) (p 3954) (derived73498 p h) (h 6267)

theorem derived75633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2741) ∨ (p 2608) ∨ (¬ p 2241) :=
  ElevenRUP.step75633 (p 2241) (p 2608) (p 2741) (p 3954) (derived73498 p h) (h 19767)

theorem derived75634 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 2241) ∨ (p 2608) :=
  ElevenRUP.step75634 (p 2241) (p 2608) (p 3189) (p 3256) (p 3954) (derived73498 p h) (derived44482 p h)

theorem derived75635 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (¬ p 2449) ∨ (¬ p 2241) ∨ (p 2608) :=
  ElevenRUP.step75635 (p 2241) (p 2449) (p 2608) (p 2996) (p 3027) (p 3954) (derived73340 p h) (derived73498 p h) (derived44485 p h)

theorem derived75636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (p 2608) ∨ (¬ p 2166) ∨ (p 2210) ∨ (¬ p 2750) ∨ (¬ p 2241) :=
  ElevenRUP.step75636 (p 2166) (p 2191) (p 2210) (p 2241) (p 2608) (p 2750) (p 3166) (p 3172) (p 3954) (derived73355 p h) (derived73498 p h) (derived73221 p h) (derived66830 p h)

theorem derived75637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 2608) ∨ (¬ p 2727) ∨ (p 2440) :=
  ElevenRUP.step75637 (p 2241) (p 2440) (p 2542) (p 2608) (p 2727) (p 3954) (derived73498 p h) (derived73270 p h) (derived46473 p h)

theorem derived75639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2241) ∨ (¬ p 3156) ∨ (p 2608) :=
  ElevenRUP.step75639 (p 2241) (p 2608) (p 2992) (p 3156) (p 3954) (derived73498 p h) (derived44234 p h)

theorem derived75640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2241) ∨ (p 2608) ∨ (¬ p 2284) :=
  ElevenRUP.step75640 (p 2241) (p 2284) (p 2608) (p 2992) (p 3954) (derived73498 p h) (derived44600 p h)

theorem derived75641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2241) ∨ (p 2608) ∨ (¬ p 2901) :=
  ElevenRUP.step75641 (p 2241) (p 2608) (p 2901) (p 2992) (p 3954) (derived73498 p h) (derived45062 p h)

theorem derived75642 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2608) ∨ (¬ p 2241) ∨ (p 3136) :=
  ElevenRUP.step75642 (p 2241) (p 2608) (p 2992) (p 3136) (p 3954) (p 4315) (derived73498 p h) (derived73550 p h) (derived53580 p h)

theorem derived75647 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2295) :=
  ElevenRUP.step75647 (p 2241) (p 2295) (p 2608) (p 2641) (p 3954) (derived73498 p h) (derived46052 p h)

theorem derived75650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (p 2331) ∨ (¬ p 2750) ∨ (p 2668) ∨ (¬ p 2972) ∨ (¬ p 4450) ∨ (p 2608) ∨ (¬ p 2210) ∨ (p 2363) :=
  ElevenRUP.step75650 (p 2210) (p 2252) (p 2331) (p 2363) (p 2608) (p 2668) (p 2750) (p 2963) (p 2972) (p 3324) (p 3954) (p 4347) (p 4450) (derived73338 p h) (derived73386 p h) (derived73498 p h) (derived73560 p h) (derived64816 p h)

theorem derived75651 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3319) ∨ (¬ p 3093) ∨ (¬ p 2750) ∨ (¬ p 4330) ∨ (p 3083) ∨ (¬ p 2252) ∨ (p 2528) ∨ (p 2651) :=
  ElevenRUP.step75651 (p 2252) (p 2528) (p 2534) (p 2608) (p 2651) (p 2657) (p 2750) (p 3083) (p 3093) (p 3319) (p 3954) (p 4256) (p 4330) (derived73498 p h) (derived73542 p h) (derived73268 p h) (derived73288 p h) (derived52093 p h)

theorem derived75652 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (p 2608) ∨ (¬ p 3379) ∨ (¬ p 2528) :=
  ElevenRUP.step75652 (p 2518) (p 2528) (p 2608) (p 3379) (p 3954) (derived73498 p h) (derived45616 p h)

theorem derived75656 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3246) ∨ (¬ p 2210) ∨ (¬ p 2891) :=
  ElevenRUP.step75656 (p 2210) (p 2608) (p 2891) (p 3246) (p 3954) (derived73498 p h) (derived44464 p h)

theorem derived75660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2608) ∨ (p 2860) ∨ (p 2839) :=
  ElevenRUP.step75660 (p 2284) (p 2608) (p 2839) (p 2860) (p 3583) (p 3758) (p 3954) (derived73498 p h) (derived73456 p h) (derived73424 p h) (derived45953 p h)

theorem derived75661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2608) ∨ (¬ p 4877) ∨ (¬ p 4172) ∨ (p 2166) :=
  ElevenRUP.step75661 (p 2166) (p 2191) (p 2220) (p 2608) (p 3954) (p 4172) (p 4877) (derived73498 p h) (derived73222 p h) (derived51581 p h)

theorem derived75663 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2737) ∨ (p 2608) ∨ (p 2295) :=
  ElevenRUP.step75663 (p 2295) (p 2608) (p 2737) (p 2743) (p 2797) (p 3568) (p 3954) (p 4195) (derived73532 p h) (derived73298 p h) (derived73498 p h) (derived73416 p h) (derived46257 p h)

theorem derived75665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 5152) ∨ (¬ p 2819) ∨ (¬ p 3830) ∨ (p 2608) ∨ (¬ p 3955) :=
  ElevenRUP.step75665 (p 2608) (p 2819) (p 3830) (p 3917) (p 3954) (p 3955) (p 5152) (derived73498 p h) (derived46446 p h)

theorem derived75667 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 2608) ∨ (p 3005) ∨ (p 2737) :=
  ElevenRUP.step75667 (p 2608) (p 2737) (p 2743) (p 3005) (p 3256) (p 3877) (p 3954) (p 4118) (derived73520 p h) (derived73498 p h) (derived73488 p h) (derived73298 p h) (derived46182 p h)

theorem derived75670 (p : Nat → Prop) (h : Inputs p) :
    (p 3631) ∨ (p 2608) ∨ (¬ p 4796) ∨ (¬ p 3516) ∨ (¬ p 3545) :=
  ElevenRUP.step75670 (p 2608) (p 3516) (p 3545) (p 3631) (p 3817) (p 3954) (p 4796) (derived73468 p h) (derived73498 p h) (derived50590 p h)

theorem derived75672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (p 2608) ∨ (p 2761) ∨ (¬ p 3707) :=
  ElevenRUP.step75672 (p 2608) (p 2761) (p 3707) (p 3830) (p 3954) (p 4381) (derived73498 p h) (derived73574 p h) (derived44569 p h)

theorem derived75674 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 3379) :=
  ElevenRUP.step75674 (p 2417) (p 2608) (p 2922) (p 3379) (p 3954) (derived73498 p h) (derived44581 p h)

theorem derived75678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4024) ∨ (p 2608) ∨ (¬ p 3093) ∨ (¬ p 2252) ∨ (¬ p 4133) ∨ (p 2901) ∨ (p 2946) ∨ (p 2881) ∨ (¬ p 2819) ∨ (¬ p 2750) :=
  ElevenRUP.step75678 (p 2252) (p 2608) (p 2750) (p 2819) (p 2881) (p 2901) (p 2946) (p 2952) (p 3093) (p 3570) (p 3954) (p 4024) (p 4133) (p 4320) (derived73498 p h) (derived73552 p h) (derived73330 p h) (derived73418 p h) (derived55177 p h)

theorem derived75683 (p : Nat → Prop) (h : Inputs p) :
    (p 2901) ∨ (¬ p 3156) ∨ (p 2608) ∨ (¬ p 4042) ∨ (p 2819) ∨ (p 2829) ∨ (¬ p 3051) ∨ (¬ p 4521) ∨ (¬ p 4503) :=
  ElevenRUP.step75683 (p 2608) (p 2819) (p 2829) (p 2901) (p 3051) (p 3156) (p 3688) (p 3954) (p 4042) (p 4320) (p 4358) (p 4503) (p 4521) (derived73552 p h) (derived73498 p h) (derived73564 p h) (derived73444 p h) (derived54342 p h)

theorem derived75684 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2737) ∨ (p 2630) ∨ (¬ p 2440) :=
  ElevenRUP.step75684 (p 2440) (p 2608) (p 2630) (p 2737) (p 2743) (p 2810) (p 3954) (derived73498 p h) (derived73298 p h) (derived73316 p h) (derived44829 p h)

theorem derived75686 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2210) ∨ (p 2563) ∨ (¬ p 2192) :=
  ElevenRUP.step75686 (p 2192) (p 2210) (p 2563) (p 2608) (p 3954) (p 4110) (derived73498 p h) (derived73516 p h) (derived44605 p h)

theorem derived75698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4777) ∨ (p 2608) ∨ (p 2707) ∨ (¬ p 2156) ∨ (¬ p 4521) ∨ (¬ p 2177) ∨ (p 2449) ∨ (¬ p 2274) ∨ (¬ p 4666) :=
  ElevenRUP.step75698 (p 2156) (p 2177) (p 2274) (p 2449) (p 2608) (p 2707) (p 3588) (p 3947) (p 3954) (p 4521) (p 4666) (p 4777) (derived73498 p h) (derived73430 p h) (derived73494 p h) (derived62578 p h)

theorem derived75699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 2284) ∨ (¬ p 5045) ∨ (¬ p 2156) ∨ (p 2417) ∨ (p 2608) ∨ (¬ p 4521) ∨ (p 2707) ∨ (¬ p 4106) ∨ (¬ p 4621) :=
  ElevenRUP.step75699 (p 2156) (p 2284) (p 2417) (p 2608) (p 2707) (p 3115) (p 3588) (p 3952) (p 3954) (p 4106) (p 4278) (p 4521) (p 4621) (p 5045) (derived73496 p h) (derived73546 p h) (derived73498 p h) (derived73430 p h) (derived54704 p h)

theorem derived75701 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3125) ∨ (¬ p 2241) ∨ (p 3564) ∨ (¬ p 2641) ∨ (¬ p 4564) ∨ (p 2573) ∨ (¬ p 3347) :=
  ElevenRUP.step75701 (p 2241) (p 2573) (p 2579) (p 2608) (p 2641) (p 3125) (p 3347) (p 3564) (p 3954) (p 4137) (p 4564) (derived73498 p h) (derived73524 p h) (derived73274 p h) (derived71289 p h)

theorem derived75702 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2608) ∨ (¬ p 3125) ∨ (p 3434) ∨ (¬ p 2248) ∨ (¬ p 4621) ∨ (¬ p 2284) ∨ (¬ p 2946) :=
  ElevenRUP.step75702 (p 2248) (p 2284) (p 2608) (p 2707) (p 2946) (p 3125) (p 3434) (p 3588) (p 3954) (p 4324) (p 4621) (derived73430 p h) (derived73498 p h) (derived73556 p h) (derived58934 p h)

theorem derived75704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 3309) ∨ (p 2608) ∨ (¬ p 4870) ∨ (¬ p 5020) :=
  ElevenRUP.step75704 (p 2307) (p 2608) (p 3309) (p 3549) (p 3954) (p 4870) (p 5020) (derived73406 p h) (derived73498 p h) (derived65153 p h)

theorem derived75706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 5017) ∨ (¬ p 2396) ∨ (¬ p 5740) ∨ (¬ p 5405) ∨ (¬ p 4316) ∨ (¬ p 2307) ∨ (p 2608) ∨ (p 2839) :=
  ElevenRUP.step75706 (p 2307) (p 2396) (p 2608) (p 2761) (p 2839) (p 3583) (p 3954) (p 4316) (p 5017) (p 5405) (p 5740) (derived73498 p h) (derived73424 p h) (derived55855 p h)

theorem derived75708 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2573) ∨ (p 2608) ∨ (¬ p 4079) :=
  ElevenRUP.step75708 (p 2493) (p 2499) (p 2573) (p 2608) (p 3954) (p 4079) (derived73260 p h) (derived73498 p h) (derived71290 p h)

theorem derived75710 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 2352) ∨ (¬ p 5190) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (p 2737) ∨ (¬ p 5113) ∨ (p 2608) :=
  ElevenRUP.step75710 (p 2352) (p 2363) (p 2573) (p 2608) (p 2737) (p 2743) (p 3755) (p 3954) (p 4035) (p 5113) (p 5190) (derived73506 p h) (derived73298 p h) (derived73498 p h) (derived62635 p h)

theorem derived75711 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2470) ∨ (¬ p 4079) ∨ (¬ p 2509) :=
  ElevenRUP.step75711 (p 2470) (p 2509) (p 2608) (p 3954) (p 4079) (derived73498 p h) (derived71292 p h)

theorem derived75712 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 3389) ∨ (¬ p 5190) ∨ (¬ p 4361) ∨ (p 2608) ∨ (¬ p 2911) ∨ (p 2737) ∨ (p 2177) :=
  ElevenRUP.step75712 (p 2177) (p 2299) (p 2608) (p 2685) (p 2737) (p 2743) (p 2911) (p 3389) (p 3572) (p 3954) (p 4361) (p 5190) (derived73420 p h) (derived73498 p h) (derived73298 p h) (derived73234 p h) (derived62481 p h)

theorem derived75713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3389) ∨ (p 3537) ∨ (p 3609) ∨ (¬ p 4332) ∨ (p 2437) ∨ (¬ p 5190) ∨ (p 2608) :=
  ElevenRUP.step75713 (p 2437) (p 2608) (p 3343) (p 3389) (p 3537) (p 3609) (p 3742) (p 3954) (p 4242) (p 4332) (p 4340) (p 5190) (derived73538 p h) (derived73558 p h) (derived73452 p h) (derived73498 p h) (derived42490 p h)

theorem derived75714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2230) ∨ (¬ p 3146) ∨ (¬ p 3917) ∨ (¬ p 4604) ∨ (p 2608) ∨ (¬ p 5190) ∨ (p 2829) :=
  ElevenRUP.step75714 (p 2230) (p 2373) (p 2608) (p 2829) (p 3146) (p 3688) (p 3917) (p 3954) (p 4604) (p 5190) (derived73498 p h) (derived73444 p h) (derived42472 p h)

theorem derived75716 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 2608) ∨ (p 2563) ∨ (¬ p 4362) ∨ (p 2685) ∨ (¬ p 4521) ∨ (¬ p 2156) ∨ (p 2737) :=
  ElevenRUP.step75716 (p 2156) (p 2427) (p 2563) (p 2608) (p 2685) (p 2737) (p 2743) (p 3572) (p 3954) (p 4110) (p 4362) (p 4521) (derived73498 p h) (derived73516 p h) (derived73420 p h) (derived73298 p h) (derived62624 p h)

theorem derived75717 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (p 2608) ∨ (p 2972) ∨ (¬ p 4877) ∨ (¬ p 4172) :=
  ElevenRUP.step75717 (p 2608) (p 2972) (p 3212) (p 3954) (p 4172) (p 4363) (p 4877) (derived73498 p h) (derived73568 p h) (derived49728 p h)

theorem derived75720 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 2651) ∨ (¬ p 2248) ∨ (¬ p 2417) ∨ (¬ p 4625) ∨ (¬ p 3917) ∨ (¬ p 2437) :=
  ElevenRUP.step75720 (p 2248) (p 2417) (p 2437) (p 2608) (p 2651) (p 2829) (p 3688) (p 3917) (p 3954) (p 4625) (derived73444 p h) (derived73498 p h) (derived61575 p h)

theorem derived75721 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2307) ∨ (¬ p 3645) ∨ (p 2177) ∨ (¬ p 4332) ∨ (p 2459) ∨ (¬ p 3333) ∨ (¬ p 4198) ∨ (¬ p 3379) ∨ (¬ p 4030) ∨ (¬ p 4877) :=
  ElevenRUP.step75721 (p 2177) (p 2299) (p 2307) (p 2313) (p 2459) (p 2608) (p 3333) (p 3379) (p 3645) (p 3954) (p 4030) (p 4198) (p 4332) (p 4348) (p 4877) (derived73498 p h) (derived73238 p h) (derived73234 p h) (derived73562 p h) (derived63045 p h)

theorem derived75725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 2363) ∨ (¬ p 3645) ∨ (¬ p 3399) ∨ (¬ p 4877) ∨ (p 2187) ∨ (p 2156) ∨ (p 2608) ∨ (¬ p 3950) :=
  ElevenRUP.step75725 (p 2156) (p 2187) (p 2363) (p 2608) (p 3399) (p 3631) (p 3645) (p 3646) (p 3950) (p 3954) (p 3989) (p 4347) (p 4877) (derived73560 p h) (derived73502 p h) (derived73436 p h) (derived73498 p h) (derived51812 p h)

theorem derived75734 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3146) ∨ (p 3005) ∨ (¬ p 2220) ∨ (p 2737) ∨ (¬ p 4521) ∨ (¬ p 4041) ∨ (p 2459) :=
  ElevenRUP.step75734 (p 2220) (p 2459) (p 2608) (p 2737) (p 2743) (p 3005) (p 3146) (p 3877) (p 3954) (p 4041) (p 4348) (p 4521) (derived73498 p h) (derived73488 p h) (derived73298 p h) (derived73562 p h) (derived42064 p h)

theorem derived75736 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3830) ∨ (p 2230) ∨ (¬ p 5123) ∨ (¬ p 3707) ∨ (p 2373) ∨ (p 2608) ∨ (¬ p 3347) :=
  ElevenRUP.step75736 (p 2230) (p 2373) (p 2589) (p 2608) (p 3347) (p 3707) (p 3830) (p 3880) (p 3954) (p 5123) (p 5568) (derived73284 p h) (derived73490 p h) (derived73498 p h) (derived71293 p h)

theorem derived75737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2972) ∨ (p 2608) ∨ (p 2982) ∨ (¬ p 2210) :=
  ElevenRUP.step75737 (p 2210) (p 2608) (p 2972) (p 2982) (p 3954) (p 4948) (derived73498 p h) (derived73846 p h) (derived44578 p h)

theorem derived75743 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5283) ∨ (¬ p 3707) ∨ (¬ p 2295) ∨ (¬ p 3830) ∨ (p 2608) ∨ (¬ p 5282) ∨ (¬ p 5274) :=
  ElevenRUP.step75743 (p 2295) (p 2608) (p 3707) (p 3830) (p 3954) (p 5274) (p 5282) (p 5283) (derived73498 p h) (derived56402 p h)

theorem derived75747 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (p 3051) ∨ (¬ p 2427) ∨ (p 2373) ∨ (¬ p 5063) ∨ (p 2608) ∨ (¬ p 3904) ∨ (¬ p 3347) ∨ (¬ p 2241) :=
  ElevenRUP.step75747 (p 2241) (p 2373) (p 2427) (p 2608) (p 3051) (p 3189) (p 3347) (p 3556) (p 3880) (p 3904) (p 3954) (p 5063) (derived73414 p h) (derived73490 p h) (derived73498 p h) (derived71297 p h)

theorem derived75754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5580) ∨ (¬ p 3707) ∨ (p 2608) ∨ (¬ p 3347) ∨ (¬ p 5123) ∨ (p 2352) ∨ (p 2573) ∨ (¬ p 3830) :=
  ElevenRUP.step75754 (p 2352) (p 2573) (p 2579) (p 2608) (p 3347) (p 3707) (p 3830) (p 3954) (p 3956) (p 5123) (p 5580) (derived73498 p h) (derived73500 p h) (derived73274 p h) (derived71299 p h)

theorem derived75756 (p : Nat → Prop) (h : Inputs p) :
    (p 3670) ∨ (p 2608) ∨ (¬ p 4826) ∨ (p 3599) ∨ (¬ p 2901) ∨ (¬ p 2248) ∨ (¬ p 4129) ∨ (¬ p 2946) :=
  ElevenRUP.step75756 (p 2248) (p 2608) (p 2901) (p 2946) (p 3599) (p 3670) (p 3954) (p 4129) (p 4379) (p 4826) (p 5387) (derived74026 p h) (derived73498 p h) (derived73572 p h) (derived51320 p h)

theorem derived75758 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2850) ∨ (p 2563) ∨ (p 3367) :=
  ElevenRUP.step75758 (p 2563) (p 2608) (p 2850) (p 3367) (p 3585) (p 3684) (p 3954) (p 4110) (derived73498 p h) (derived73442 p h) (derived73516 p h) (derived73428 p h) (derived43541 p h)

theorem derived75759 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 2608) ∨ (p 3422) ∨ (p 2553) :=
  ElevenRUP.step75759 (p 2553) (p 2588) (p 2608) (p 3367) (p 3422) (p 3584) (p 3585) (p 3954) (derived73428 p h) (derived73498 p h) (derived73426 p h) (derived73282 p h) (derived44197 p h)

theorem derived75760 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 2608) ∨ (p 3422) ∨ (p 2352) :=
  ElevenRUP.step75760 (p 2352) (p 2608) (p 3367) (p 3422) (p 3584) (p 3585) (p 3954) (p 3956) (derived73428 p h) (derived73498 p h) (derived73426 p h) (derived73500 p h) (derived44808 p h)

theorem derived75761 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 3367) ∨ (¬ p 5214) ∨ (¬ p 3379) :=
  ElevenRUP.step75761 (p 2608) (p 3367) (p 3379) (p 3585) (p 3954) (p 5214) (derived73498 p h) (derived73428 p h) (derived42710 p h)

theorem derived75762 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 5160) ∨ (p 2608) ∨ (p 3367) :=
  ElevenRUP.step75762 (p 2608) (p 3276) (p 3367) (p 3585) (p 3954) (p 4425) (p 5160) (derived73578 p h) (derived73498 p h) (derived73428 p h) (derived44660 p h)

theorem derived75763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 2608) ∨ (¬ p 2396) ∨ (¬ p 5160) ∨ (¬ p 4521) ∨ (p 3367) ∨ (¬ p 4641) ∨ (¬ p 2156) :=
  ElevenRUP.step75763 (p 2156) (p 2274) (p 2396) (p 2608) (p 3367) (p 3585) (p 3954) (p 4521) (p 4641) (p 5160) (derived73498 p h) (derived73428 p h) (derived62059 p h)

theorem derived75764 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 5160) ∨ (p 3367) ∨ (¬ p 2668) ∨ (¬ p 4697) ∨ (¬ p 2363) ∨ (¬ p 2248) ∨ (¬ p 2331) :=
  ElevenRUP.step75764 (p 2248) (p 2331) (p 2363) (p 2608) (p 2668) (p 3367) (p 3585) (p 3954) (p 4697) (p 5160) (derived73498 p h) (derived73428 p h) (derived57234 p h)

theorem derived75765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4641) ∨ (¬ p 2248) ∨ (¬ p 2331) ∨ (p 2608) ∨ (¬ p 2396) ∨ (¬ p 5160) ∨ (¬ p 2295) ∨ (p 3367) :=
  ElevenRUP.step75765 (p 2248) (p 2295) (p 2331) (p 2396) (p 2608) (p 3367) (p 3585) (p 3954) (p 4641) (p 5160) (derived73498 p h) (derived73428 p h) (derived49198 p h)

theorem derived75768 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 5160) ∨ (¬ p 2459) ∨ (p 3367) ∨ (¬ p 2881) ∨ (¬ p 4697) ∨ (¬ p 3051) ∨ (¬ p 4521) :=
  ElevenRUP.step75768 (p 2459) (p 2608) (p 2881) (p 3051) (p 3367) (p 3585) (p 3954) (p 4521) (p 4697) (p 5160) (derived73498 p h) (derived73428 p h) (derived42013 p h)

theorem derived75770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5325) ∨ (p 2608) ∨ (p 3367) ∨ (p 2187) ∨ (¬ p 3125) ∨ (¬ p 5160) ∨ (¬ p 2383) ∨ (¬ p 5017) :=
  ElevenRUP.step75770 (p 2187) (p 2383) (p 2608) (p 3125) (p 3367) (p 3585) (p 3954) (p 3989) (p 5017) (p 5160) (p 5325) (derived73498 p h) (derived73428 p h) (derived73502 p h) (derived63690 p h)

theorem derived75776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (p 2608) ∨ (p 2850) ∨ (p 3367) :=
  ElevenRUP.step75776 (p 2608) (p 2850) (p 3367) (p 3449) (p 3585) (p 3684) (p 3954) (derived73498 p h) (derived73442 p h) (derived73428 p h) (derived47757 p h)

theorem derived75778 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 2850) ∨ (p 3367) ∨ (p 2373) :=
  ElevenRUP.step75778 (p 2373) (p 2608) (p 2850) (p 3367) (p 3585) (p 3684) (p 3880) (p 3954) (derived73498 p h) (derived73442 p h) (derived73428 p h) (derived73490 p h) (derived44021 p h)

theorem derived75779 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (p 3367) ∨ (p 2440) ∨ (p 2850) :=
  ElevenRUP.step75779 (p 2440) (p 2542) (p 2608) (p 2850) (p 3367) (p 3585) (p 3684) (p 3954) (derived73498 p h) (derived73428 p h) (derived73270 p h) (derived73442 p h) (derived45046 p h)

theorem derived75782 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5160) ∨ (¬ p 3641) ∨ (¬ p 3358) :=
  ElevenRUP.step75782 (p 3358) (p 3641) (p 3874) (p 5160) (derived73483 p h) (h 34765)

theorem derived75783 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 2470) ∨ (¬ p 3363) :=
  ElevenRUP.step75783 (p 2470) (p 2476) (p 3363) (p 3641) (p 3874) (derived73483 p h) (derived73250 p h) (h 6429)

theorem derived75785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 2509) ∨ (¬ p 4030) :=
  ElevenRUP.step75785 (p 2509) (p 3641) (p 3874) (p 4030) (derived73483 p h) (h 6368)

theorem derived75786 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 3641) ∨ (¬ p 3573) :=
  ElevenRUP.step75786 (p 3422) (p 3573) (p 3584) (p 3641) (p 3874) (derived73426 p h) (derived73483 p h) (h 37610)

theorem derived75790 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (p 3040) :=
  ElevenRUP.step75790 (p 2996) (p 3036) (p 3040) (derived73346 p h) (h 4201)

theorem derived75792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3246) ∨ (¬ p 2440) ∨ (¬ p 2437) :=
  ElevenRUP.step75792 (p 2417) (p 2437) (p 2440) (p 3246) (p 3690) (derived73446 p h) (derived46654 p h)

theorem derived75793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3246) ∨ (¬ p 2437) ∨ (¬ p 2651) :=
  ElevenRUP.step75793 (p 2417) (p 2437) (p 2651) (p 3246) (p 3690) (derived73446 p h) (derived61541 p h)

theorem derived75797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2396) ∨ (¬ p 2598) ∨ (¬ p 3201) :=
  ElevenRUP.step75797 (p 2396) (p 2417) (p 2598) (p 3201) (p 4107) (derived73514 p h) (derived46804 p h)

theorem derived75799 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2396) ∨ (¬ p 4718) ∨ (p 2274) :=
  ElevenRUP.step75799 (p 2274) (p 2396) (p 2417) (p 3097) (p 4107) (p 4718) (derived73514 p h) (derived73352 p h) (derived69100 p h)

theorem derived75803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3657) ∨ (p 2911) :=
  ElevenRUP.step75803 (p 2417) (p 2911) (p 3644) (p 3657) (derived73434 p h) (h 20364)

theorem derived75813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 4001) ∨ (p 3246) :=
  ElevenRUP.step75813 (p 2417) (p 3246) (p 3690) (p 4001) (derived73446 p h) (h 20738)

theorem derived75819 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 4640) :=
  ElevenRUP.step75819 (p 2417) (p 4639) (p 4640) (derived73682 p h) (h 7419)

theorem derived75821 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 3201) ∨ (¬ p 3363) :=
  ElevenRUP.step75821 (p 3201) (p 3363) (p 3389) (p 3540) (p 3876) (derived73402 p h) (derived73485 p h) (h 6701)

theorem derived75823 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3201) ∨ (¬ p 4343) :=
  ElevenRUP.step75823 (p 2437) (p 3201) (p 3742) (p 3876) (p 4343) (derived73452 p h) (derived73485 p h) (h 32588)

theorem derived75824 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3875) ∨ (p 3641) ∨ (¬ p 3201) :=
  ElevenRUP.step75824 (p 3201) (p 3641) (p 3874) (p 3875) (p 3876) (derived73484 p h) (derived73485 p h) (h 5734)

theorem derived75825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 4030) ∨ (p 2922) :=
  ElevenRUP.step75825 (p 2922) (p 2928) (p 3201) (p 3876) (p 4030) (derived73485 p h) (derived73320 p h) (h 33602)

theorem derived75827 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 3201) ∨ (p 2850) :=
  ElevenRUP.step75827 (p 2441) (p 2850) (p 3201) (p 3684) (p 3876) (derived73485 p h) (derived73442 p h) (h 23799)

theorem derived75829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3921) ∨ (¬ p 2331) ∨ (p 2807) ∨ (¬ p 3740) ∨ (¬ p 4564) ∨ (¬ p 2274) :=
  ElevenRUP.step75829 (p 2274) (p 2331) (p 2807) (p 3414) (p 3740) (p 3921) (p 4564) (derived73392 p h) (derived41454 p h)

theorem derived75830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 2881) ∨ (p 2406) ∨ (¬ p 3519) ∨ (¬ p 3389) ∨ (¬ p 3740) :=
  ElevenRUP.step75830 (p 2264) (p 2406) (p 2881) (p 3238) (p 3389) (p 3519) (p 3570) (p 3740) (derived73418 p h) (derived73374 p h) (derived64448 p h)

theorem derived75831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3740) ∨ (¬ p 3389) ∨ (p 2807) ∨ (¬ p 2663) :=
  ElevenRUP.step75831 (p 2663) (p 2807) (p 3389) (p 3414) (p 3740) (derived73392 p h) (h 29333)

theorem derived75834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 3878) ∨ (¬ p 4753) ∨ (¬ p 3422) ∨ (p 3256) :=
  ElevenRUP.step75834 (p 2510) (p 2528) (p 3256) (p 3422) (p 3878) (p 4118) (p 4753) (derived73520 p h) (derived42333 p h)

theorem derived75835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3266) ∨ (¬ p 3389) ∨ (¬ p 3362) ∨ (¬ p 2145) ∨ (¬ p 4332) ∨ (p 2220) ∨ (¬ p 3343) ∨ (¬ p 4335) ∨ (p 2437) :=
  ElevenRUP.step75835 (p 2145) (p 2220) (p 2437) (p 3266) (p 3343) (p 3362) (p 3389) (p 3742) (p 4120) (p 4322) (p 4332) (p 4335) (derived73522 p h) (derived73452 p h) (derived54892 p h)

theorem derived75836 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2761) ∨ (¬ p 4402) ∨ (p 2427) ∨ (p 2230) :=
  ElevenRUP.step75836 (p 2230) (p 2427) (p 2589) (p 2761) (p 4235) (p 4322) (p 4402) (derived73536 p h) (derived73284 p h) (derived44001 p h)

theorem derived75837 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2761) ∨ (¬ p 2396) ∨ (p 2177) :=
  ElevenRUP.step75837 (p 2177) (p 2299) (p 2396) (p 2761) (p 4322) (derived73234 p h) (derived61452 p h)

theorem derived75838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 2440) ∨ (p 2982) ∨ (p 2651) :=
  ElevenRUP.step75838 (p 2440) (p 2651) (p 2657) (p 2982) (p 4322) (p 4948) (derived73846 p h) (derived73288 p h) (derived53220 p h)

theorem derived75840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 2946) ∨ (p 2982) ∨ (¬ p 3879) ∨ (¬ p 2651) :=
  ElevenRUP.step75840 (p 2651) (p 2946) (p 2952) (p 2982) (p 3879) (p 4322) (p 4948) (derived73330 p h) (derived73846 p h) (derived54213 p h)

theorem derived75845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3266) ∨ (p 2132) ∨ (p 3105) :=
  ElevenRUP.step75845 (p 2132) (p 2138) (p 3105) (p 3266) (p 4322) (p 4385) (derived73214 p h) (derived73576 p h) (derived43117 p h)

theorem derived75846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3266) ∨ (p 2839) ∨ (¬ p 2143) ∨ (¬ p 4032) :=
  ElevenRUP.step75846 (p 2143) (p 2839) (p 3266) (p 3583) (p 4032) (p 4322) (derived73424 p h) (derived55473 p h)

theorem derived75848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 4322) ∨ (¬ p 4032) ∨ (p 2992) ∨ (¬ p 2957) :=
  ElevenRUP.step75848 (p 2957) (p 2992) (p 3266) (p 3662) (p 4032) (p 4322) (derived73440 p h) (derived57313 p h)

theorem derived75850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3266) ∨ (¬ p 2241) ∨ (¬ p 4332) ∨ (¬ p 4335) ∨ (¬ p 3343) ∨ (¬ p 2727) ∨ (p 2220) :=
  ElevenRUP.step75850 (p 2220) (p 2241) (p 2727) (p 3266) (p 3343) (p 4120) (p 4322) (p 4332) (p 4335) (p 4524) (derived72962 p h) (derived73522 p h) (derived58122 p h)

theorem derived75852 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 2284) ∨ (p 2982) ∨ (¬ p 2563) :=
  ElevenRUP.step75852 (p 2284) (p 2563) (p 2982) (p 3952) (p 4322) (p 4948) (derived73496 p h) (derived73846 p h) (derived57656 p h)

theorem derived75853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 4032) ∨ (¬ p 3051) ∨ (p 2901) :=
  ElevenRUP.step75853 (p 2901) (p 3051) (p 4032) (p 4320) (p 4322) (derived73552 p h) (derived60353 p h)

theorem derived75856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 3276) ∨ (p 3093) ∨ (p 3309) ∨ (p 2396) ∨ (¬ p 5190) ∨ (¬ p 3355) ∨ (¬ p 4395) :=
  ElevenRUP.step75856 (p 2396) (p 3093) (p 3276) (p 3309) (p 3355) (p 3549) (p 3591) (p 4107) (p 4322) (p 4395) (p 5190) (derived73432 p h) (derived73406 p h) (derived73514 p h) (derived42491 p h)

theorem derived75859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3166) ∨ (p 2946) ∨ (¬ p 3256) :=
  ElevenRUP.step75859 (p 2946) (p 2952) (p 2992) (p 3166) (p 3256) (derived73330 p h) (derived45158 p h)

theorem derived75862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3166) ∨ (¬ p 3146) ∨ (p 2946) ∨ (¬ p 4311) :=
  ElevenRUP.step75862 (p 2946) (p 2952) (p 2992) (p 3146) (p 3166) (p 4311) (derived73330 p h) (derived55410 p h)

theorem derived75866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4311) ∨ (¬ p 3166) ∨ (p 2166) ∨ (p 2946) ∨ (¬ p 4957) :=
  ElevenRUP.step75866 (p 2166) (p 2191) (p 2946) (p 2952) (p 3166) (p 4311) (p 4957) (derived73222 p h) (derived73330 p h) (derived41303 p h)

theorem derived75867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4311) ∨ (¬ p 3166) ∨ (¬ p 3136) ∨ (p 2946) ∨ (¬ p 3146) :=
  ElevenRUP.step75867 (p 2946) (p 2952) (p 3136) (p 3146) (p 3166) (p 4311) (derived73330 p h) (derived48611 p h)

theorem derived75874 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4417) ∨ (p 2331) ∨ (¬ p 3166) ∨ (p 2187) :=
  ElevenRUP.step75874 (p 2187) (p 2331) (p 2963) (p 3166) (p 3989) (p 4417) (p 4560) (derived73338 p h) (derived72955 p h) (derived73502 p h) (derived50459 p h)

theorem derived75878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 5113) :=
  ElevenRUP.step75878 (p 3256) (p 5110) (p 5113) (derived73924 p h) (h 8636)

theorem derived75879 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 3256) ∨ (¬ p 5008) ∨ (¬ p 2651) ∨ (p 2088) :=
  ElevenRUP.step75879 (p 2088) (p 2651) (p 3256) (p 3286) (p 3292) (p 3857) (p 5008) (p 5110) (derived73378 p h) (derived73924 p h) (derived73480 p h) (derived66884 p h)

theorem derived75882 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 4518) ∨ (p 3246) ∨ (¬ p 4204) :=
  ElevenRUP.step75882 (p 2396) (p 3246) (p 3309) (p 3690) (p 4204) (p 4518) (derived73446 p h) (derived52194 p h)

theorem derived75884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2396) ∨ (p 3246) ∨ (¬ p 4204) ∨ (¬ p 4718) :=
  ElevenRUP.step75884 (p 2396) (p 2553) (p 3246) (p 3690) (p 4204) (p 4718) (derived73446 p h) (derived41321 p h)

theorem derived75885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2396) ∨ (¬ p 2573) ∨ (p 3246) :=
  ElevenRUP.step75885 (p 2396) (p 2553) (p 2573) (p 3246) (p 3690) (derived73446 p h) (derived45426 p h)

theorem derived75886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3051) ∨ (¬ p 2881) ∨ (p 2177) :=
  ElevenRUP.step75886 (p 2177) (p 2299) (p 2396) (p 2881) (p 3051) (derived73234 p h) (derived43509 p h)

theorem derived75887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3657) ∨ (p 2177) :=
  ElevenRUP.step75887 (p 2177) (p 2299) (p 2396) (p 3657) (derived73234 p h) (h 19992)

theorem derived75892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3146) ∨ (¬ p 4443) ∨ (¬ p 4902) ∨ (p 2177) :=
  ElevenRUP.step75892 (p 2177) (p 2299) (p 2396) (p 3146) (p 3692) (p 4443) (p 4902) (derived73448 p h) (derived73234 p h) (derived41717 p h)

theorem derived75893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3146) ∨ (p 2177) ∨ (¬ p 4443) ∨ (¬ p 4902) :=
  ElevenRUP.step75893 (p 2177) (p 2299) (p 2396) (p 3146) (p 3692) (p 4443) (p 4902) (derived73448 p h) (derived73234 p h) (derived50156 p h)

theorem derived75896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3516) ∨ (p 2707) ∨ (¬ p 3959) ∨ (p 2177) :=
  ElevenRUP.step75896 (p 2177) (p 2299) (p 2396) (p 2707) (p 3516) (p 3588) (p 3821) (p 3959) (derived73470 p h) (derived73430 p h) (derived73234 p h) (derived43305 p h)

theorem derived75898 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2396) ∨ (p 3425) ∨ (p 2177) :=
  ElevenRUP.step75898 (p 2177) (p 2299) (p 2396) (p 2717) (p 3425) (p 3471) (derived73396 p h) (derived73234 p h) (derived45956 p h)

theorem derived75900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2911) ∨ (p 3246) ∨ (¬ p 4647) ∨ (p 2177) :=
  ElevenRUP.step75900 (p 2177) (p 2299) (p 2396) (p 2911) (p 3246) (p 3690) (p 4647) (derived73446 p h) (derived73234 p h) (derived51022 p h)

theorem derived75901 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2911) ∨ (p 2177) ∨ (¬ p 3201) :=
  ElevenRUP.step75901 (p 2177) (p 2299) (p 2396) (p 2911) (p 3201) (derived73234 p h) (derived42922 p h)

theorem derived75902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2528) ∨ (¬ p 4443) ∨ (p 2177) ∨ (¬ p 4420) :=
  ElevenRUP.step75902 (p 2177) (p 2299) (p 2396) (p 2528) (p 2534) (p 4420) (p 4443) (derived73268 p h) (derived73234 p h) (derived61279 p h)

theorem derived75903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2177) :=
  ElevenRUP.step75903 (p 2177) (p 2299) (p 2396) (p 3399) (p 3527) (derived73234 p h) (derived43065 p h)

theorem derived75904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (p 2177) :=
  ElevenRUP.step75904 (p 2177) (p 2264) (p 2299) (p 2396) (p 2807) (derived73234 p h) (derived47019 p h)

theorem derived75906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 2449) ∨ (¬ p 2996) ∨ (p 2177) :=
  ElevenRUP.step75906 (p 2177) (p 2299) (p 2396) (p 2449) (p 2996) (p 3947) (derived73494 p h) (derived73234 p h) (derived48482 p h)

theorem derived75911 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 2509) ∨ (¬ p 3950) ∨ (¬ p 2331) ∨ (p 3379) ∨ (¬ p 2248) :=
  ElevenRUP.step75911 (p 2248) (p 2295) (p 2331) (p 2396) (p 2509) (p 2528) (p 2534) (p 3379) (p 3452) (p 3950) (derived73268 p h) (derived73394 p h) (derived48878 p h)

theorem derived75916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 4140) ∨ (p 3246) :=
  ElevenRUP.step75916 (p 2396) (p 3246) (p 3690) (p 4140) (derived73446 p h) (h 20664)

theorem derived75920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2396) ∨ (¬ p 4338) ∨ (p 3246) ∨ (¬ p 2881) :=
  ElevenRUP.step75920 (p 2396) (p 2881) (p 3246) (p 3309) (p 3690) (p 4338) (derived73446 p h) (derived54307 p h)

theorem derived75926 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2396) ∨ (¬ p 2563) ∨ (p 2427) :=
  ElevenRUP.step75926 (p 2396) (p 2427) (p 2563) (p 3246) (p 3690) (p 4235) (derived73446 p h) (derived73536 p h) (derived62841 p h)

theorem derived75928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 4257) ∨ (p 3246) ∨ (p 2427) ∨ (p 2406) :=
  ElevenRUP.step75928 (p 2396) (p 2406) (p 2427) (p 3238) (p 3246) (p 3690) (p 4235) (p 4257) (derived73446 p h) (derived73536 p h) (derived73374 p h) (derived49552 p h)

theorem derived75929 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3246) ∨ (¬ p 2156) ∨ (¬ p 2274) :=
  ElevenRUP.step75929 (p 2156) (p 2274) (p 2396) (p 3246) (p 3690) (derived73446 p h) (derived44876 p h)

theorem derived75930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2274) ∨ (¬ p 4138) ∨ (¬ p 4668) ∨ (p 2187) :=
  ElevenRUP.step75930 (p 2187) (p 2274) (p 2396) (p 3989) (p 4138) (p 4668) (derived73502 p h) (derived61417 p h)

theorem derived75931 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2911) ∨ (¬ p 2396) ∨ (¬ p 2274) :=
  ElevenRUP.step75931 (p 2274) (p 2396) (p 2417) (p 2911) (p 4278) (derived73546 p h) (derived58635 p h)

theorem derived75935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (p 2484) :=
  ElevenRUP.step75935 (p 2470) (p 2480) (p 2484) (derived73254 p h) (h 3095)

theorem derived75936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2210) ∨ (p 2166) ∨ (p 2563) :=
  ElevenRUP.step75936 (p 2166) (p 2191) (p 2210) (p 2373) (p 2563) (p 3555) (p 4110) (derived73412 p h) (derived73222 p h) (derived73516 p h) (derived47684 p h)

theorem derived75938 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2166) ∨ (¬ p 4506) ∨ (¬ p 4489) ∨ (¬ p 2192) :=
  ElevenRUP.step75938 (p 2166) (p 2191) (p 2192) (p 2383) (p 4489) (p 4506) (derived73222 p h) (derived49607 p h)

theorem derived75940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3979) ∨ (¬ p 4733) ∨ (p 3146) ∨ (p 2166) ∨ (¬ p 5122) ∨ (¬ p 2774) ∨ (p 2210) :=
  ElevenRUP.step75940 (p 2166) (p 2191) (p 2210) (p 2774) (p 2819) (p 3146) (p 3555) (p 3692) (p 3979) (p 4733) (p 5122) (derived73448 p h) (derived73222 p h) (derived73412 p h) (derived54692 p h)

theorem derived75941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 5122) ∨ (¬ p 2248) ∨ (p 2166) ∨ (¬ p 2331) ∨ (p 3146) ∨ (¬ p 3979) ∨ (p 2210) :=
  ElevenRUP.step75941 (p 2166) (p 2191) (p 2210) (p 2248) (p 2331) (p 2668) (p 3146) (p 3555) (p 3692) (p 3979) (p 5122) (derived73222 p h) (derived73448 p h) (derived73412 p h) (derived49196 p h)

theorem derived75942 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2210) ∨ (p 2166) ∨ (¬ p 2363) :=
  ElevenRUP.step75942 (p 2166) (p 2191) (p 2210) (p 2363) (p 3146) (p 3555) (p 3692) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived44995 p h)

theorem derived75943 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2241) ∨ (p 3146) ∨ (p 2166) :=
  ElevenRUP.step75943 (p 2166) (p 2191) (p 2210) (p 2241) (p 3146) (p 3555) (p 3692) (derived73412 p h) (derived73448 p h) (derived73222 p h) (derived54941 p h)

theorem derived75946 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2210) ∨ (p 2166) ∨ (¬ p 2608) :=
  ElevenRUP.step75946 (p 2166) (p 2191) (p 2210) (p 2608) (p 3146) (p 3555) (p 3692) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived46286 p h)

theorem derived75947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 3950) ∨ (¬ p 4733) ∨ (p 2166) ∨ (¬ p 2696) ∨ (p 2210) ∨ (p 3146) ∨ (¬ p 2685) :=
  ElevenRUP.step75947 (p 2166) (p 2191) (p 2210) (p 2449) (p 2685) (p 2696) (p 3146) (p 3555) (p 3692) (p 3950) (p 4733) (derived73222 p h) (derived73412 p h) (derived73448 p h) (derived50757 p h)

theorem derived75949 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (p 3146) ∨ (p 2210) ∨ (p 2166) :=
  ElevenRUP.step75949 (p 2166) (p 2191) (p 2210) (p 3146) (p 3266) (p 3555) (p 3692) (p 4444) (derived73580 p h) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived45469 p h)

theorem derived75950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 3146) ∨ (¬ p 2363) ∨ (p 2166) :=
  ElevenRUP.step75950 (p 2166) (p 2191) (p 2192) (p 2363) (p 3146) (p 3692) (derived73448 p h) (derived73222 p h) (derived47584 p h)

theorem derived75952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 2192) ∨ (p 2166) :=
  ElevenRUP.step75952 (p 2166) (p 2190) (p 2191) (p 2192) (derived73222 p h) (h 2518)

theorem derived75958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2220) ∨ (p 2166) ∨ (p 2156) :=
  ElevenRUP.step75958 (p 2156) (p 2166) (p 2191) (p 2220) (p 2891) (p 3646) (derived73222 p h) (derived73436 p h) (derived47208 p h)

theorem derived75959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2220) ∨ (p 2166) ∨ (p 2156) ∨ (¬ p 4558) :=
  ElevenRUP.step75959 (p 2156) (p 2166) (p 2191) (p 2220) (p 2891) (p 3646) (p 4558) (derived73222 p h) (derived73436 p h) (derived54419 p h)

theorem derived75962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2166) ∨ (¬ p 2274) ∨ (¬ p 4506) :=
  ElevenRUP.step75962 (p 2166) (p 2191) (p 2192) (p 2274) (p 4506) (derived73222 p h) (derived71303 p h)

theorem derived75963 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 3156) ∨ (¬ p 3136) ∨ (p 2210) :=
  ElevenRUP.step75963 (p 2166) (p 2191) (p 2210) (p 3136) (p 3156) (p 3555) (derived73222 p h) (derived73412 p h) (derived44036 p h)

theorem derived75965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2619) ∨ (p 2427) ∨ (¬ p 4885) ∨ (p 2166) :=
  ElevenRUP.step75965 (p 2166) (p 2191) (p 2427) (p 2619) (p 2891) (p 4235) (p 4885) (derived73536 p h) (derived73222 p h) (derived62587 p h)

theorem derived75967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2341) ∨ (¬ p 4132) ∨ (p 2166) :=
  ElevenRUP.step75967 (p 2166) (p 2191) (p 2341) (p 2891) (p 4132) (derived73222 p h) (derived68260 p h)

theorem derived75970 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2166) ∨ (¬ p 2264) ∨ (¬ p 2685) ∨ (p 2156) ∨ (¬ p 2696) ∨ (¬ p 4905) ∨ (¬ p 2145) :=
  ElevenRUP.step75970 (p 2145) (p 2156) (p 2166) (p 2191) (p 2192) (p 2264) (p 2685) (p 2696) (p 3646) (p 4905) (derived73222 p h) (derived73436 p h) (derived62652 p h)

theorem derived75971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2264) ∨ (¬ p 4362) ∨ (p 2166) ∨ (¬ p 4132) :=
  ElevenRUP.step75971 (p 2166) (p 2191) (p 2264) (p 2891) (p 4132) (p 4362) (derived73222 p h) (derived42424 p h)

theorem derived75976 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2210) ∨ (p 2166) ∨ (¬ p 2459) :=
  ElevenRUP.step75976 (p 2166) (p 2191) (p 2210) (p 2459) (p 3146) (p 3555) (p 3692) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived64768 p h)

theorem derived75981 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3422) ∨ (p 3051) ∨ (¬ p 4733) ∨ (¬ p 4134) ∨ (¬ p 2352) ∨ (¬ p 3369) ∨ (p 2166) ∨ (¬ p 2598) :=
  ElevenRUP.step75981 (p 2166) (p 2191) (p 2352) (p 2598) (p 2891) (p 3051) (p 3369) (p 3422) (p 3556) (p 4134) (p 4733) (derived73414 p h) (derived73222 p h) (derived64744 p h)

theorem derived75982 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 4556) ∨ (¬ p 2177) ∨ (¬ p 4132) ∨ (p 2166) :=
  ElevenRUP.step75982 (p 2166) (p 2177) (p 2191) (p 2891) (p 4132) (p 4556) (derived73222 p h) (derived50093 p h)

theorem derived75985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 4132) ∨ (p 2166) ∨ (¬ p 4668) :=
  ElevenRUP.step75985 (p 2166) (p 2191) (p 2891) (p 3246) (p 4132) (p 4668) (derived73222 p h) (derived50107 p h)

theorem derived75988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2210) ∨ (p 2166) ∨ (¬ p 2241) :=
  ElevenRUP.step75988 (p 2166) (p 2191) (p 2210) (p 2241) (p 2373) (p 3555) (derived73412 p h) (derived73222 p h) (derived46860 p h)

theorem derived75989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4132) ∨ (¬ p 2891) ∨ (p 2427) ∨ (p 2459) ∨ (p 2166) :=
  ElevenRUP.step75989 (p 2166) (p 2191) (p 2427) (p 2459) (p 2891) (p 4132) (p 4235) (p 4348) (derived73536 p h) (derived73562 p h) (derived73222 p h) (derived48868 p h)

theorem derived75995 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 2210) ∨ (¬ p 2373) ∨ (p 2166) :=
  ElevenRUP.step75995 (p 2166) (p 2191) (p 2210) (p 2373) (p 3399) (p 3555) (derived73412 p h) (derived73222 p h) (derived60947 p h)

theorem derived75999 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2210) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3950) ∨ (¬ p 2396) ∨ (¬ p 4733) ∨ (p 2166) :=
  ElevenRUP.step75999 (p 2122) (p 2166) (p 2191) (p 2210) (p 2396) (p 2774) (p 3146) (p 3555) (p 3692) (p 3950) (p 4733) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived50689 p h)

theorem derived76000 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2166) ∨ (¬ p 2192) ∨ (¬ p 4506) ∨ (¬ p 4718) :=
  ElevenRUP.step76000 (p 2166) (p 2191) (p 2192) (p 2352) (p 4506) (p 4718) (derived73222 p h) (derived41320 p h)

theorem derived76001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4338) ∨ (p 2166) ∨ (p 2274) :=
  ElevenRUP.step76001 (p 2166) (p 2191) (p 2274) (p 3097) (p 3309) (p 4338) (derived73222 p h) (derived73352 p h) (derived69475 p h)

theorem derived76005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 4210) ∨ (¬ p 4506) ∨ (p 2166) ∨ (¬ p 2563) :=
  ElevenRUP.step76005 (p 2166) (p 2191) (p 2563) (p 2668) (p 4210) (p 4506) (p 4560) (derived73222 p h) (derived72955 p h) (derived41224 p h)

theorem derived76010 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2210) ∨ (¬ p 5190) ∨ (p 3146) ∨ (¬ p 2396) ∨ (p 2166) ∨ (¬ p 2573) ∨ (¬ p 3950) :=
  ElevenRUP.step76010 (p 2166) (p 2191) (p 2210) (p 2396) (p 2553) (p 2573) (p 3146) (p 3555) (p 3692) (p 3950) (p 5190) (derived73412 p h) (derived73448 p h) (derived73222 p h) (derived42115 p h)

theorem derived76011 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2166) ∨ (¬ p 5194) ∨ (¬ p 2230) ∨ (¬ p 4202) :=
  ElevenRUP.step76011 (p 2166) (p 2191) (p 2230) (p 2373) (p 4202) (p 5194) (derived73222 p h) (derived49358 p h)

theorem derived76012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3370) ∨ (p 2563) ∨ (p 2166) ∨ (p 3146) :=
  ElevenRUP.step76012 (p 2156) (p 2166) (p 2191) (p 2563) (p 3146) (p 3370) (p 3692) (p 4110) (derived73516 p h) (derived73222 p h) (derived73448 p h) (derived53188 p h)

theorem derived76015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3146) ∨ (¬ p 2459) ∨ (p 2230) ∨ (¬ p 4629) ∨ (p 2166) :=
  ElevenRUP.step76015 (p 2166) (p 2191) (p 2230) (p 2459) (p 2528) (p 2589) (p 3146) (p 3692) (p 4629) (derived73448 p h) (derived73284 p h) (derived73222 p h) (derived66646 p h)

theorem derived76016 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3146) ∨ (¬ p 4355) ∨ (¬ p 4629) ∨ (p 2166) :=
  ElevenRUP.step76016 (p 2166) (p 2191) (p 2528) (p 3146) (p 3692) (p 4355) (p 4629) (derived73448 p h) (derived73222 p h) (derived54486 p h)

theorem derived76023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3950) ∨ (p 3146) ∨ (p 2210) ∨ (¬ p 4733) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 2417) ∨ (p 2166) :=
  ElevenRUP.step76023 (p 2166) (p 2191) (p 2210) (p 2417) (p 2598) (p 3146) (p 3201) (p 3555) (p 3692) (p 3950) (p 4733) (derived73448 p h) (derived73412 p h) (derived73222 p h) (derived50121 p h)

theorem derived76025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 2255) ∨ (p 2166) ∨ (¬ p 3156) ∨ (¬ p 2946) :=
  ElevenRUP.step76025 (p 2166) (p 2191) (p 2255) (p 2946) (p 3156) (p 3368) (derived73222 p h) (derived60401 p h)

theorem derived76040 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2166) ∨ (¬ p 4811) ∨ (¬ p 4109) ∨ (¬ p 4202) ∨ (p 2440) :=
  ElevenRUP.step76040 (p 2166) (p 2191) (p 2220) (p 2440) (p 2542) (p 4109) (p 4202) (p 4811) (derived73222 p h) (derived73270 p h) (derived41923 p h)

theorem derived76044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2220) ∨ (p 2166) ∨ (¬ p 2137) ∨ (¬ p 4874) :=
  ElevenRUP.step76044 (p 2137) (p 2166) (p 2191) (p 2220) (p 2737) (p 4874) (derived73222 p h) (derived67282 p h)

theorem derived76050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 2972) ∨ (¬ p 3369) ∨ (¬ p 4032) ∨ (p 2166) :=
  ElevenRUP.step76050 (p 2166) (p 2191) (p 2972) (p 3369) (p 4032) (p 5568) (derived73222 p h) (derived54111 p h)

theorem derived76054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (p 3115) ∨ (¬ p 3156) ∨ (p 2166) :=
  ElevenRUP.step76054 (p 2166) (p 2191) (p 3115) (p 3156) (p 4208) (p 4322) (derived73534 p h) (derived73222 p h) (derived59207 p h)

theorem derived76055 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 3156) ∨ (p 2166) ∨ (¬ p 4975) ∨ (¬ p 3368) ∨ (¬ p 3413) :=
  ElevenRUP.step76055 (p 2166) (p 2191) (p 2641) (p 3156) (p 3368) (p 3413) (p 4975) (derived73222 p h) (derived50233 p h)

theorem derived76057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 3156) ∨ (¬ p 2641) ∨ (p 2166) ∨ (¬ p 4566) :=
  ElevenRUP.step76057 (p 2166) (p 2191) (p 2641) (p 3156) (p 3368) (p 4566) (derived73222 p h) (derived60438 p h)

theorem derived76058 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (¬ p 3368) ∨ (¬ p 2946) ∨ (¬ p 3579) ∨ (¬ p 2253) ∨ (¬ p 3156) ∨ (p 2166) :=
  ElevenRUP.step76058 (p 2166) (p 2191) (p 2253) (p 2946) (p 2996) (p 3027) (p 3156) (p 3368) (p 3579) (derived73340 p h) (derived73222 p h) (derived43380 p h)

theorem derived76059 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2166) ∨ (¬ p 4717) ∨ (¬ p 2493) ∨ (¬ p 4202) :=
  ElevenRUP.step76059 (p 2166) (p 2191) (p 2373) (p 2493) (p 4202) (p 4717) (derived73222 p h) (derived41372 p h)

theorem derived76060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2166) ∨ (p 2860) ∨ (p 2132) :=
  ElevenRUP.step76060 (p 2132) (p 2138) (p 2166) (p 2191) (p 2192) (p 2860) (p 3758) (derived73222 p h) (derived73456 p h) (derived73214 p h) (derived56365 p h)

theorem derived76063 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 2220) ∨ (p 2166) ∨ (¬ p 3136) ∨ (¬ p 2745) ∨ (¬ p 2951) :=
  ElevenRUP.step76063 (p 2166) (p 2191) (p 2220) (p 2745) (p 2951) (p 3136) (p 3368) (derived73222 p h) (derived41232 p h)

theorem derived76064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 2406) ∨ (p 2166) ∨ (¬ p 3379) ∨ (¬ p 4335) :=
  ElevenRUP.step76064 (p 2166) (p 2191) (p 2406) (p 2982) (p 3379) (p 4335) (derived73222 p h) (derived43343 p h)

theorem derived76066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4341) ∨ (¬ p 3256) ∨ (¬ p 2331) ∨ (p 2363) ∨ (¬ p 3379) ∨ (¬ p 2246) ∨ (p 2210) ∨ (¬ p 4134) ∨ (¬ p 2749) ∨ (p 2166) :=
  ElevenRUP.step76066 (p 2166) (p 2191) (p 2210) (p 2246) (p 2331) (p 2363) (p 2749) (p 3256) (p 3379) (p 3555) (p 4134) (p 4341) (p 4347) (derived73560 p h) (derived73412 p h) (derived73222 p h) (derived71307 p h)

theorem derived76067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4282) ∨ (¬ p 3950) ∨ (p 3146) ∨ (¬ p 2656) ∨ (¬ p 2417) ∨ (¬ p 2727) ∨ (p 2166) ∨ (p 2946) ∨ (¬ p 2249) ∨ (¬ p 3389) :=
  ElevenRUP.step76067 (p 2166) (p 2191) (p 2249) (p 2417) (p 2656) (p 2727) (p 2946) (p 2952) (p 3146) (p 3389) (p 3692) (p 3950) (p 4282) (derived73448 p h) (derived73222 p h) (derived73330 p h) (derived51865 p h)

theorem derived76070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3461) ∨ (¬ p 4282) ∨ (¬ p 5123) ∨ (p 2946) ∨ (¬ p 2249) ∨ (p 2166) ∨ (¬ p 3323) ∨ (¬ p 2641) :=
  ElevenRUP.step76070 (p 2166) (p 2191) (p 2249) (p 2641) (p 2946) (p 2952) (p 3323) (p 3461) (p 4282) (p 5123) (p 5568) (derived73330 p h) (derived73222 p h) (derived52273 p h)

theorem derived76072 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 3156) ∨ (¬ p 2727) ∨ (p 2166) :=
  ElevenRUP.step76072 (p 2166) (p 2191) (p 2727) (p 3156) (p 3368) (derived73222 p h) (derived69603 p h)

theorem derived76073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 4335) ∨ (p 2166) ∨ (¬ p 4282) :=
  ElevenRUP.step76073 (p 2166) (p 2191) (p 3115) (p 4282) (p 4335) (derived73222 p h) (h 28969)

end ElevenLogic
