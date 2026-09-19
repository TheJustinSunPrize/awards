import SunPrize.Certificate.Derived048
import SunPrize.Certificate.Logic049
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived95883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5142) ∨ (¬ p 3550) ∨ (p 2274) ∨ (¬ p 2187) ∨ (p 3527) :=
  ElevenRUP.step95883 (p 2187) (p 2274) (p 3097) (p 3527) (p 3548) (p 3550) (p 5142) (derived73352 p h) (derived73404 p h) (derived40977 p h)

theorem derived95884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2295) ∨ (¬ p 3550) ∨ (p 3527) ∨ (¬ p 5142) :=
  ElevenRUP.step95884 (p 2295) (p 2668) (p 3527) (p 3548) (p 3550) (p 3568) (p 5142) (derived73416 p h) (derived73404 p h) (derived40974 p h)

theorem derived95885 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (¬ p 4209) ∨ (¬ p 2417) ∨ (¬ p 5295) ∨ (¬ p 4647) ∨ (¬ p 2901) :=
  ElevenRUP.step95885 (p 2417) (p 2901) (p 3115) (p 4208) (p 4209) (p 4647) (p 5295) (derived73534 p h) (derived57771 p h)

theorem derived95887 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (¬ p 2951) ∨ (¬ p 4207) ∨ (¬ p 4209) :=
  ElevenRUP.step95887 (p 2951) (p 3115) (p 4207) (p 4208) (p 4209) (derived73534 p h) (h 6304)

theorem derived95895 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 3146) ∨ (¬ p 3440) ∨ (p 2608) ∨ (p 3156) ∨ (¬ p 2750) ∨ (¬ p 5122) ∨ (p 2946) ∨ (¬ p 2252) ∨ (¬ p 3830) :=
  ElevenRUP.step95895 (p 2252) (p 2608) (p 2750) (p 2946) (p 2952) (p 3146) (p 3156) (p 3440) (p 3497) (p 3692) (p 3830) (p 3954) (p 4181) (p 5122) (derived73448 p h) (derived73498 p h) (derived73400 p h) (derived73330 p h) (derived55202 p h)

theorem derived95896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3987) ∨ (¬ p 2307) ∨ (¬ p 4975) ∨ (p 2295) ∨ (p 2651) :=
  ElevenRUP.step95896 (p 2295) (p 2307) (p 2651) (p 2657) (p 3568) (p 3987) (p 4975) (derived73416 p h) (derived73288 p h) (derived49439 p h)

theorem derived95897 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (p 2440) ∨ (¬ p 2655) ∨ (¬ p 4975) ∨ (p 2230) :=
  ElevenRUP.step95897 (p 2230) (p 2331) (p 2440) (p 2542) (p 2589) (p 2655) (p 4975) (derived73270 p h) (derived73284 p h) (derived41379 p h)

theorem derived95899 (p : Nat → Prop) (h : Inputs p) :
    (p 4281) ∨ (¬ p 2727) :=
  ElevenRUP.step95899 (p 2727) (p 4281) (p 5912) (derived74223 p h) (h 12454)

theorem derived95900 (p : Nat → Prop) (h : Inputs p) :
    (p 3487) ∨ (¬ p 2727) :=
  ElevenRUP.step95900 (p 2727) (p 3487) (p 5912) (derived74223 p h) (h 12455)

theorem derived95901 (p : Nat → Prop) (h : Inputs p) :
    (p 4813) ∨ (¬ p 2727) :=
  ElevenRUP.step95901 (p 2727) (p 4813) (p 5912) (derived74223 p h) (h 12457)

theorem derived95903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 3516) ∨ (p 2437) ∨ (¬ p 4279) ∨ (p 2177) :=
  ElevenRUP.step95903 (p 2177) (p 2299) (p 2396) (p 2437) (p 3516) (p 3742) (p 3821) (p 4279) (derived73470 p h) (derived73452 p h) (derived73234 p h) (derived45139 p h)

theorem derived95904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (¬ p 3083) ∨ (p 2396) ∨ (p 2437) ∨ (¬ p 3543) ∨ (¬ p 4666) ∨ (¬ p 4427) ∨ (¬ p 4404) :=
  ElevenRUP.step95904 (p 2396) (p 2437) (p 3083) (p 3543) (p 3742) (p 4107) (p 4279) (p 4404) (p 4427) (p 4666) (derived73514 p h) (derived73452 p h) (derived42537 p h)

theorem derived95905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3516) ∨ (¬ p 4279) :=
  ElevenRUP.step95905 (p 2417) (p 3516) (p 3821) (p 4278) (p 4279) (derived73545 p h) (derived73470 p h) (h 36433)

theorem derived95906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (p 2341) ∨ (¬ p 2911) :=
  ElevenRUP.step95906 (p 2341) (p 2911) (p 3551) (p 3644) (p 4279) (derived73408 p h) (derived73433 p h) (h 15109)

theorem derived95914 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 2449) ∨ (¬ p 3580) ∨ (¬ p 4279) ∨ (¬ p 4811) ∨ (p 2922) :=
  ElevenRUP.step95914 (p 2449) (p 2922) (p 2928) (p 3516) (p 3580) (p 3821) (p 4279) (p 4811) (derived73470 p h) (derived73320 p h) (derived41135 p h)

theorem derived95923 (p : Nat → Prop) (h : Inputs p) :
    (p 5206) ∨ (p 3399) :=
  ElevenRUP.step95923 (p 3399) (p 5206) (p 6043) (derived74381 p h) (h 13253)

theorem derived95924 (p : Nat → Prop) (h : Inputs p) :
    (p 3543) ∨ (p 3399) :=
  ElevenRUP.step95924 (p 3399) (p 3543) (p 6043) (derived74381 p h) (h 13254)

theorem derived95927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4114) ∨ (¬ p 5315) ∨ (¬ p 2088) ∨ (¬ p 2578) ∨ (p 3073) ∨ (¬ p 4558) ∨ (¬ p 2870) ∨ (¬ p 3096) ∨ (¬ p 4359) :=
  ElevenRUP.step95927 (p 2088) (p 2578) (p 2870) (p 3073) (p 3096) (p 4114) (p 4261) (p 4359) (p 4558) (p 5315) (derived73544 p h) (derived50995 p h)

theorem derived95928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5315) ∨ (¬ p 3609) ∨ (p 2608) ∨ (¬ p 3449) ∨ (p 2528) :=
  ElevenRUP.step95928 (p 2528) (p 2534) (p 2608) (p 3449) (p 3609) (p 3954) (p 5315) (derived73498 p h) (derived73268 p h) (derived65262 p h)

theorem derived95932 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3670) ∨ (p 3125) ∨ (¬ p 4117) ∨ (¬ p 2787) ∨ (¬ p 5454) ∨ (¬ p 2274) ∨ (p 2307) ∨ (¬ p 3286) ∨ (¬ p 5322) :=
  ElevenRUP.step95932 (p 2274) (p 2307) (p 2313) (p 2787) (p 3125) (p 3276) (p 3286) (p 3670) (p 3744) (p 4117) (p 4425) (p 5322) (p 5454) (derived73578 p h) (derived73454 p h) (derived73238 p h) (derived48980 p h)

theorem derived95934 (p : Nat → Prop) (h : Inputs p) :
    (p 4416) ∨ (p 3449) :=
  ElevenRUP.step95934 (p 3449) (p 4416) (p 6055) (derived74397 p h) (h 13333)

theorem derived95935 (p : Nat → Prop) (h : Inputs p) :
    (p 5239) ∨ (p 3449) :=
  ElevenRUP.step95935 (p 3449) (p 5239) (p 6055) (derived74397 p h) (h 13334)

theorem derived95936 (p : Nat → Prop) (h : Inputs p) :
    (p 3439) ∨ (p 3449) :=
  ElevenRUP.step95936 (p 3439) (p 3449) (p 6055) (derived74397 p h) (h 13336)

theorem derived95937 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 3631) ∨ (¬ p 2936) ∨ (¬ p 2341) ∨ (p 2911) :=
  ElevenRUP.step95937 (p 2341) (p 2911) (p 2936) (p 3516) (p 3631) (p 3644) (p 3821) (derived73470 p h) (derived73434 p h) (derived48785 p h)

theorem derived95942 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 5038) ∨ (p 2284) ∨ (¬ p 5046) ∨ (¬ p 3506) ∨ (¬ p 4952) :=
  ElevenRUP.step95942 (p 2284) (p 3276) (p 3506) (p 3952) (p 4425) (p 4952) (p 5038) (p 5046) (derived73578 p h) (derived73496 p h) (derived50576 p h)

theorem derived95943 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4322) ∨ (¬ p 5038) ∨ (¬ p 3506) ∨ (¬ p 4705) ∨ (p 2982) :=
  ElevenRUP.step95943 (p 2982) (p 3506) (p 4322) (p 4705) (p 4948) (p 5038) (derived73846 p h) (derived41828 p h)

theorem derived95944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2954) ∨ (¬ p 4984) ∨ (p 2341) ∨ (¬ p 2901) ∨ (¬ p 2881) :=
  ElevenRUP.step95944 (p 2341) (p 2881) (p 2901) (p 2954) (p 3551) (p 4984) (derived73408 p h) (derived41823 p h)

theorem derived95947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 2383) ∨ (¬ p 4198) ∨ (¬ p 2954) ∨ (¬ p 2284) :=
  ElevenRUP.step95947 (p 2187) (p 2284) (p 2383) (p 2387) (p 2954) (p 4198) (derived73246 p h) (derived52291 p h)

theorem derived95954 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5233) ∨ (p 2707) ∨ (p 2396) ∨ (¬ p 4477) :=
  ElevenRUP.step95954 (p 2396) (p 2707) (p 3588) (p 3599) (p 4107) (p 4477) (p 5233) (derived73430 p h) (derived73514 p h) (derived41286 p h)

theorem derived95958 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2427) ∨ (¬ p 2829) ∨ (¬ p 3483) ∨ (p 2982) ∨ (¬ p 3366) ∨ (¬ p 2143) ∨ (¬ p 5052) ∨ (p 2696) ∨ (¬ p 4368) :=
  ElevenRUP.step95958 (p 2143) (p 2427) (p 2696) (p 2829) (p 2982) (p 3051) (p 3365) (p 3366) (p 3483) (p 3556) (p 4368) (p 4948) (p 5052) (derived73414 p h) (derived73846 p h) (derived73390 p h) (derived51294 p h)

theorem derived95959 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2341) ∨ (¬ p 2437) ∨ (¬ p 4383) ∨ (¬ p 5203) :=
  ElevenRUP.step95959 (p 2341) (p 2437) (p 3083) (p 4256) (p 4383) (p 5203) (derived73542 p h) (derived41713 p h)

theorem derived95961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2307) ∨ (¬ p 4031) ∨ (¬ p 5217) ∨ (¬ p 2505) ∨ (¬ p 4198) ∨ (p 2850) :=
  ElevenRUP.step95961 (p 2307) (p 2313) (p 2505) (p 2850) (p 3309) (p 3684) (p 4031) (p 4198) (p 5217) (derived73238 p h) (derived73442 p h) (derived50764 p h)

theorem derived95963 (p : Nat → Prop) (h : Inputs p) :
    (p 4140) ∨ (¬ p 2274) :=
  ElevenRUP.step95963 (p 2274) (p 4140) (p 5819) (derived74103 p h) (h 11911)

theorem derived95964 (p : Nat → Prop) (h : Inputs p) :
    (p 3872) ∨ (¬ p 2274) :=
  ElevenRUP.step95964 (p 2274) (p 3872) (p 5819) (derived74103 p h) (h 11912)

theorem derived95967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5087) ∨ (¬ p 2717) ∨ (¬ p 4383) ∨ (¬ p 3389) ∨ (p 2470) :=
  ElevenRUP.step95967 (p 2470) (p 2476) (p 2717) (p 3389) (p 4383) (p 5087) (derived73250 p h) (derived63663 p h)

theorem derived95968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 3960) ∨ (¬ p 2437) ∨ (p 3083) ∨ (¬ p 2717) ∨ (¬ p 5087) :=
  ElevenRUP.step95968 (p 2437) (p 2481) (p 2717) (p 3083) (p 3960) (p 4256) (p 5087) (derived73542 p h) (derived49132 p h)

theorem derived95970 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 4661) ∨ (¬ p 2807) :=
  ElevenRUP.step95970 (p 2807) (p 3286) (p 3292) (p 4661) (derived73378 p h) (h 19994)

theorem derived95973 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 3005) ∨ (¬ p 2573) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (¬ p 2553) ∨ (p 2696) ∨ (¬ p 4419) :=
  ElevenRUP.step95973 (p 2396) (p 2553) (p 2573) (p 2696) (p 3005) (p 3256) (p 3365) (p 3877) (p 3950) (p 4118) (p 4419) (derived73520 p h) (derived73488 p h) (derived73390 p h) (derived64683 p h)

theorem derived95974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5600) ∨ (p 3005) ∨ (¬ p 4419) ∨ (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 3389) ∨ (¬ p 5123) ∨ (p 2696) :=
  ElevenRUP.step95974 (p 2417) (p 2696) (p 2761) (p 3005) (p 3365) (p 3389) (p 3877) (p 4419) (p 5123) (p 5600) (derived73488 p h) (derived73390 p h) (derived64902 p h)

theorem derived95975 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (p 3256) ∨ (¬ p 4826) ∨ (p 3266) ∨ (¬ p 2573) ∨ (¬ p 4236) ∨ (¬ p 3791) ∨ (¬ p 4419) ∨ (¬ p 2553) :=
  ElevenRUP.step95975 (p 2553) (p 2573) (p 3166) (p 3172) (p 3256) (p 3266) (p 3791) (p 4118) (p 4236) (p 4419) (p 4444) (p 4826) (derived73356 p h) (derived73520 p h) (derived73580 p h) (derived62627 p h)

theorem derived95976 (p : Nat → Prop) (h : Inputs p) :
    (p 4967) ∨ (¬ p 3005) :=
  ElevenRUP.step95976 (p 3005) (p 4967) (p 5963) (derived74291 p h) (h 12765)

theorem derived95977 (p : Nat → Prop) (h : Inputs p) :
    (p 4373) ∨ (¬ p 3005) :=
  ElevenRUP.step95977 (p 3005) (p 4373) (p 5963) (derived74291 p h) (h 12766)

theorem derived95978 (p : Nat → Prop) (h : Inputs p) :
    (p 4968) ∨ (¬ p 3005) :=
  ElevenRUP.step95978 (p 3005) (p 4968) (p 5963) (derived74291 p h) (h 12768)

theorem derived95979 (p : Nat → Prop) (h : Inputs p) :
    (p 4969) ∨ (¬ p 3005) :=
  ElevenRUP.step95979 (p 3005) (p 4969) (p 5963) (derived74291 p h) (h 12769)

theorem derived95980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4637) ∨ (¬ p 2341) ∨ (¬ p 5201) ∨ (¬ p 3346) ∨ (p 2911) :=
  ElevenRUP.step95980 (p 2341) (p 2911) (p 3346) (p 3644) (p 4637) (p 5201) (derived73434 p h) (derived52653 p h)

theorem derived95981 (p : Nat → Prop) (h : Inputs p) :
    (p 3905) ∨ (p 2598) :=
  ElevenRUP.step95981 (p 2598) (p 3905) (p 5881) (derived74181 p h) (h 12274)

theorem derived95982 (p : Nat → Prop) (h : Inputs p) :
    (p 4419) ∨ (p 2598) :=
  ElevenRUP.step95982 (p 2598) (p 4419) (p 5881) (derived74181 p h) (h 12275)

theorem derived95983 (p : Nat → Prop) (h : Inputs p) :
    (p 3759) ∨ (p 2598) :=
  ElevenRUP.step95983 (p 2598) (p 3759) (p 5881) (derived74181 p h) (h 12278)

theorem derived95984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5017) ∨ (¬ p 2383) ∨ (¬ p 2363) ∨ (p 2459) ∨ (p 2727) ∨ (p 3083) ∨ (p 2241) ∨ (¬ p 4438) :=
  ElevenRUP.step95984 (p 2241) (p 2247) (p 2363) (p 2383) (p 2459) (p 2727) (p 3083) (p 4111) (p 4256) (p 4348) (p 4438) (p 5017) (derived73562 p h) (derived73518 p h) (derived73542 p h) (derived73226 p h) (derived55495 p h)

theorem derived95985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2881) ∨ (¬ p 2459) ∨ (p 2727) ∨ (¬ p 4275) ∨ (p 2241) ∨ (¬ p 5017) ∨ (¬ p 4697) ∨ (p 3343) :=
  ElevenRUP.step95985 (p 2241) (p 2247) (p 2307) (p 2459) (p 2727) (p 2881) (p 3343) (p 3359) (p 4111) (p 4275) (p 4697) (p 5017) (derived73518 p h) (derived73226 p h) (derived73388 p h) (derived41994 p h)

theorem derived95986 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 2241) ∨ (¬ p 4356) ∨ (¬ p 5017) ∨ (p 2284) :=
  ElevenRUP.step95986 (p 2241) (p 2247) (p 2284) (p 2992) (p 3662) (p 3952) (p 4356) (p 5017) (derived73440 p h) (derived73226 p h) (derived73496 p h) (derived41957 p h)

theorem derived95989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5017) ∨ (¬ p 2187) ∨ (p 3083) ∨ (¬ p 2307) ∨ (p 2274) ∨ (p 2241) ∨ (p 2727) ∨ (¬ p 4384) :=
  ElevenRUP.step95989 (p 2187) (p 2241) (p 2247) (p 2274) (p 2307) (p 2727) (p 3083) (p 3097) (p 4111) (p 4256) (p 4384) (p 5017) (derived73542 p h) (derived73352 p h) (derived73226 p h) (derived73518 p h) (derived41993 p h)

theorem derived95992 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4695) ∨ (p 3156) ∨ (¬ p 4947) ∨ (¬ p 4134) ∨ (¬ p 3115) :=
  ElevenRUP.step95992 (p 2363) (p 3115) (p 3156) (p 3497) (p 4134) (p 4347) (p 4695) (p 4947) (derived73560 p h) (derived73400 p h) (derived56466 p h)

theorem derived95997 (p : Nat → Prop) (h : Inputs p) :
    (p 4449) ∨ (¬ p 2982) :=
  ElevenRUP.step95997 (p 2982) (p 4449) (p 5957) (derived74283 p h) (h 12726)

theorem derived95998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3286) ∨ (¬ p 5170) ∨ (p 2651) :=
  ElevenRUP.step95998 (p 2651) (p 2657) (p 3286) (p 3292) (p 5170) (derived73377 p h) (derived73288 p h) (h 27055)

theorem derived96001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4421) ∨ (¬ p 2331) ∨ (p 2651) ∨ (¬ p 5170) :=
  ElevenRUP.step96001 (p 2331) (p 2651) (p 2657) (p 4421) (p 5170) (derived73288 p h) (h 19880)

theorem derived96004 (p : Nat → Prop) (h : Inputs p) :
    (p 4695) ∨ (¬ p 2528) :=
  ElevenRUP.step96004 (p 2528) (p 4695) (p 5870) (derived74167 p h) (h 12211)

theorem derived96005 (p : Nat → Prop) (h : Inputs p) :
    (p 3358) ∨ (¬ p 2528) :=
  ElevenRUP.step96005 (p 2528) (p 3358) (p 5870) (derived74167 p h) (h 12212)

theorem derived96007 (p : Nat → Prop) (h : Inputs p) :
    (p 4697) ∨ (¬ p 2528) :=
  ElevenRUP.step96007 (p 2528) (p 4697) (p 5870) (derived74167 p h) (h 12215)

theorem derived96012 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 4427) ∨ (¬ p 2501) ∨ (¬ p 2553) ∨ (¬ p 3093) :=
  ElevenRUP.step96012 (p 2501) (p 2553) (p 3093) (p 3399) (p 4366) (p 4427) (derived73570 p h) (derived41399 p h)

theorem derived96016 (p : Nat → Prop) (h : Inputs p) :
    (p 4031) ∨ (¬ p 2230) :=
  ElevenRUP.step96016 (p 2230) (p 4031) (p 5813) (derived74095 p h) (h 11878)

theorem derived96017 (p : Nat → Prop) (h : Inputs p) :
    (p 4399) ∨ (¬ p 2230) :=
  ElevenRUP.step96017 (p 2230) (p 4399) (p 5813) (derived74095 p h) (h 11880)

theorem derived96019 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2319) ∨ (¬ p 2396) ∨ (¬ p 2341) ∨ (¬ p 4866) ∨ (p 2972) ∨ (p 2210) ∨ (p 2177) ∨ (¬ p 5016) ∨ (¬ p 3951) :=
  ElevenRUP.step96019 (p 2177) (p 2210) (p 2299) (p 2319) (p 2341) (p 2396) (p 2608) (p 2972) (p 3555) (p 3951) (p 4363) (p 4866) (p 5016) (derived73568 p h) (derived73412 p h) (derived73234 p h) (derived58696 p h)

theorem derived96020 (p : Nat → Prop) (h : Inputs p) :
    (p 4760) ∨ (¬ p 2641) :=
  ElevenRUP.step96020 (p 2641) (p 4760) (p 5894) (derived74199 p h) (h 12350)

theorem derived96021 (p : Nat → Prop) (h : Inputs p) :
    (p 3922) ∨ (¬ p 2641) :=
  ElevenRUP.step96021 (p 2641) (p 3922) (p 5894) (derived74199 p h) (h 12351)

theorem derived96022 (p : Nat → Prop) (h : Inputs p) :
    (p 4759) ∨ (¬ p 2641) :=
  ElevenRUP.step96022 (p 2641) (p 4759) (p 5894) (derived74199 p h) (h 12352)

theorem derived96024 (p : Nat → Prop) (h : Inputs p) :
    (p 4389) ∨ (p 3016) :=
  ElevenRUP.step96024 (p 3016) (p 4389) (p 5965) (derived74293 p h) (h 12779)

theorem derived96025 (p : Nat → Prop) (h : Inputs p) :
    (p 4194) ∨ (p 3016) :=
  ElevenRUP.step96025 (p 3016) (p 4194) (p 5965) (derived74293 p h) (h 12781)

theorem derived96026 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3016) :=
  ElevenRUP.step96026 (p 3016) (p 4972) (p 5965) (derived74293 p h) (h 12782)

theorem derived96028 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3204) ∨ (¬ p 2553) ∨ (¬ p 4870) ∨ (p 2352) ∨ (¬ p 3156) ∨ (¬ p 3136) ∨ (p 2307) ∨ (¬ p 4433) ∨ (¬ p 2696) :=
  ElevenRUP.step96028 (p 2307) (p 2313) (p 2352) (p 2553) (p 2696) (p 2753) (p 3136) (p 3156) (p 3204) (p 3956) (p 4433) (p 4870) (derived73500 p h) (derived73238 p h) (derived64179 p h)

theorem derived96029 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (¬ p 3093) ∨ (¬ p 4870) ∨ (¬ p 3873) ∨ (¬ p 2737) :=
  ElevenRUP.step96029 (p 2696) (p 2737) (p 3093) (p 3365) (p 3873) (p 4870) (derived73390 p h) (derived42483 p h)

theorem derived96032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 2761) ∨ (¬ p 4636) :=
  ElevenRUP.step96032 (p 2761) (p 3276) (p 4381) (p 4425) (p 4636) (derived73577 p h) (derived73574 p h) (h 23986)

theorem derived96033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3402) ∨ (p 2761) ∨ (¬ p 2437) ∨ (p 3343) ∨ (p 2922) ∨ (¬ p 4636) :=
  ElevenRUP.step96033 (p 2437) (p 2761) (p 2922) (p 2928) (p 3343) (p 3359) (p 3402) (p 4381) (p 4636) (derived73574 p h) (derived73388 p h) (derived73320 p h) (derived63105 p h)

theorem derived96034 (p : Nat → Prop) (h : Inputs p) :
    (p 3343) ∨ (¬ p 4636) ∨ (¬ p 2437) ∨ (¬ p 2396) ∨ (¬ p 4276) :=
  ElevenRUP.step96034 (p 2396) (p 2437) (p 3343) (p 3359) (p 4276) (p 4636) (derived73388 p h) (derived59676 p h)

theorem derived96042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 4695) ∨ (¬ p 4133) ∨ (p 3527) ∨ (¬ p 4636) ∨ (p 2363) :=
  ElevenRUP.step96042 (p 2363) (p 3527) (p 3548) (p 3631) (p 4133) (p 4347) (p 4636) (p 4695) (derived73404 p h) (derived73560 p h) (derived53981 p h)

theorem derived96044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3543) ∨ (p 3266) ∨ (¬ p 3516) ∨ (¬ p 3032) ∨ (¬ p 2685) ∨ (¬ p 3276) ∨ (¬ p 4636) :=
  ElevenRUP.step96044 (p 2685) (p 3032) (p 3266) (p 3276) (p 3516) (p 3543) (p 4444) (p 4636) (derived73580 p h) (derived61211 p h)

theorem derived96045 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 4388) ∨ (¬ p 2982) ∨ (¬ p 4629) ∨ (¬ p 2210) :=
  ElevenRUP.step96045 (p 2210) (p 2982) (p 3830) (p 3834) (p 4388) (p 4629) (derived73474 p h) (derived55633 p h)

theorem derived96047 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 3115) ∨ (¬ p 4388) ∨ (¬ p 2210) ∨ (¬ p 4957) :=
  ElevenRUP.step96047 (p 2210) (p 3115) (p 3830) (p 3834) (p 4388) (p 4957) (derived73474 p h) (derived42633 p h)

theorem derived96055 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3680) ∨ (¬ p 3105) ∨ (¬ p 4938) ∨ (¬ p 4875) :=
  ElevenRUP.step96055 (p 3105) (p 3680) (p 3707) (p 4321) (p 4875) (p 4938) (derived73554 p h) (derived48913 p h)

theorem derived96056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 3707) ∨ (¬ p 4957) ∨ (¬ p 3680) ∨ (¬ p 4938) :=
  ElevenRUP.step96056 (p 3115) (p 3680) (p 3707) (p 4321) (p 4938) (p 4957) (derived73554 p h) (derived41619 p h)

theorem derived96057 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 4282) ∨ (¬ p 4702) ∨ (¬ p 3680) ∨ (¬ p 2982) ∨ (¬ p 4938) :=
  ElevenRUP.step96057 (p 2982) (p 3680) (p 3707) (p 4282) (p 4321) (p 4702) (p 4938) (derived73554 p h) (derived48101 p h)

theorem derived96058 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 2608) ∨ (¬ p 3545) ∨ (¬ p 4796) ∨ (¬ p 2341) :=
  ElevenRUP.step96058 (p 2341) (p 2608) (p 3527) (p 3545) (p 3548) (p 3954) (p 4796) (derived73404 p h) (derived73498 p h) (derived49272 p h)

theorem derived96060 (p : Nat → Prop) (h : Inputs p) :
    (p 5152) ∨ (¬ p 3319) :=
  ElevenRUP.step96060 (p 3319) (p 5152) (p 6026) (derived74367 p h) (h 13150)

theorem derived96061 (p : Nat → Prop) (h : Inputs p) :
    (p 5153) ∨ (¬ p 3319) :=
  ElevenRUP.step96061 (p 3319) (p 5153) (p 6026) (derived74367 p h) (h 13151)

theorem derived96066 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2992) ∨ (¬ p 4901) ∨ (p 2996) ∨ (¬ p 4333) :=
  ElevenRUP.step96066 (p 2992) (p 2996) (p 3027) (p 3156) (p 3497) (p 3662) (p 4333) (p 4901) (derived73400 p h) (derived73440 p h) (derived73340 p h) (derived60393 p h)

theorem derived96071 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (p 2459) ∨ (p 3005) ∨ (¬ p 4041) ∨ (¬ p 3136) :=
  ElevenRUP.step96071 (p 2459) (p 2470) (p 2528) (p 2946) (p 2952) (p 3005) (p 3136) (p 3877) (p 4041) (p 4236) (p 4348) (p 4419) (derived73330 p h) (derived73562 p h) (derived73488 p h) (derived64944 p h)

theorem derived96073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 3379) ∨ (¬ p 3590) ∨ (¬ p 2608) ∨ (¬ p 5086) :=
  ElevenRUP.step96073 (p 2608) (p 2707) (p 3379) (p 3452) (p 3590) (p 5086) (derived73394 p h) (derived48954 p h)

theorem derived96076 (p : Nat → Prop) (h : Inputs p) :
    (p 3740) ∨ (p 2437) :=
  ElevenRUP.step96076 (p 2437) (p 3740) (p 5857) (derived74153 p h) (h 12134)

theorem derived96077 (p : Nat → Prop) (h : Inputs p) :
    (p 4112) ∨ (p 2437) :=
  ElevenRUP.step96077 (p 2437) (p 4112) (p 5857) (derived74153 p h) (h 12136)

theorem derived96078 (p : Nat → Prop) (h : Inputs p) :
    (p 4650) ∨ (p 2437) :=
  ElevenRUP.step96078 (p 2437) (p 4650) (p 5857) (derived74153 p h) (h 12137)

theorem derived96081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5740) ∨ (¬ p 2761) ∨ (p 2210) ∨ (¬ p 2396) ∨ (¬ p 2241) ∨ (¬ p 5016) ∨ (¬ p 5405) ∨ (¬ p 4756) ∨ (¬ p 3412) ∨ (¬ p 2307) :=
  ElevenRUP.step96081 (p 2210) (p 2241) (p 2307) (p 2396) (p 2761) (p 3412) (p 3555) (p 4756) (p 5016) (p 5405) (p 5740) (derived73412 p h) (derived48257 p h)

theorem derived96085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5016) ∨ (¬ p 3266) ∨ (¬ p 2383) ∨ (¬ p 5405) ∨ (¬ p 2363) ∨ (¬ p 3366) ∨ (¬ p 5740) ∨ (¬ p 4866) ∨ (p 3136) ∨ (p 2696) :=
  ElevenRUP.step96085 (p 2363) (p 2383) (p 2696) (p 3136) (p 3266) (p 3365) (p 3366) (p 4315) (p 4866) (p 5016) (p 5405) (p 5740) (derived73550 p h) (derived73390 p h) (derived48222 p h)

theorem derived96086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3717) ∨ (¬ p 5449) ∨ (p 2122) ∨ (¬ p 2307) ∨ (¬ p 3743) ∨ (¬ p 4193) :=
  ElevenRUP.step96086 (p 2122) (p 2307) (p 3717) (p 3743) (p 3822) (p 4193) (p 5449) (derived73472 p h) (derived53512 p h)

theorem derived96087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4272) ∨ (¬ p 5449) ∨ (¬ p 3136) ∨ (¬ p 3745) ∨ (p 2797) :=
  ElevenRUP.step96087 (p 2797) (p 3136) (p 3745) (p 4195) (p 4272) (p 5449) (derived73532 p h) (derived41931 p h)

theorem derived96090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5433) ∨ (¬ p 5405) ∨ (¬ p 2383) ∨ (p 2850) ∨ (p 2598) ∨ (¬ p 3266) ∨ (¬ p 2781) ∨ (¬ p 2363) :=
  ElevenRUP.step96090 (p 2363) (p 2383) (p 2598) (p 2781) (p 2850) (p 3055) (p 3266) (p 3684) (p 5405) (p 5433) (derived73442 p h) (derived73350 p h) (derived41932 p h)

theorem derived96092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4272) ∨ (¬ p 5433) ∨ (p 3016) ∨ (¬ p 4715) ∨ (¬ p 3413) :=
  ElevenRUP.step96092 (p 3016) (p 3413) (p 3574) (p 4272) (p 4715) (p 5433) (derived73422 p h) (derived50740 p h)

theorem derived96093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5433) ∨ (¬ p 2307) ∨ (¬ p 2781) ∨ (p 2598) ∨ (¬ p 5405) ∨ (¬ p 2396) ∨ (¬ p 2761) ∨ (p 2850) :=
  ElevenRUP.step96093 (p 2307) (p 2396) (p 2598) (p 2761) (p 2781) (p 2850) (p 3055) (p 3684) (p 5405) (p 5433) (derived73350 p h) (derived73442 p h) (derived55681 p h)

theorem derived96096 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4394) ∨ (¬ p 3125) :=
  ElevenRUP.step96096 (p 3125) (p 3744) (p 4393) (p 4394) (derived73453 p h) (h 6732)

theorem derived96097 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (p 2850) ∨ (p 2598) ∨ (p 2563) :=
  ElevenRUP.step96097 (p 2563) (p 2598) (p 2850) (p 3055) (p 3684) (p 4110) (p 4393) (derived73442 p h) (derived73350 p h) (derived73516 p h) (derived45659 p h)

theorem derived96101 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (p 2132) ∨ (¬ p 5254) ∨ (¬ p 2417) ∨ (¬ p 4419) ∨ (¬ p 2761) ∨ (¬ p 3389) ∨ (p 2860) :=
  ElevenRUP.step96101 (p 2132) (p 2138) (p 2417) (p 2761) (p 2860) (p 3389) (p 3758) (p 4393) (p 4419) (p 5254) (derived73214 p h) (derived73456 p h) (derived64913 p h)

theorem derived96103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3914) ∨ (¬ p 4393) ∨ (¬ p 4337) ∨ (p 2563) ∨ (p 3323) :=
  ElevenRUP.step96103 (p 2563) (p 3323) (p 3914) (p 4037) (p 4110) (p 4337) (p 4393) (derived73516 p h) (derived73508 p h) (derived46735 p h)

theorem derived96107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 4393) ∨ (p 2651) ∨ (¬ p 3125) ∨ (¬ p 2249) ∨ (p 3276) ∨ (¬ p 3487) ∨ (¬ p 2641) ∨ (¬ p 3193) :=
  ElevenRUP.step96107 (p 2249) (p 2641) (p 2651) (p 2657) (p 3125) (p 3193) (p 3276) (p 3487) (p 4228) (p 4393) (p 4425) (derived73288 p h) (derived73578 p h) (derived52264 p h)

theorem derived96109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 4393) ∨ (¬ p 3747) ∨ (p 2192) ∨ (p 3156) ∨ (¬ p 4336) :=
  ElevenRUP.step96109 (p 2192) (p 3156) (p 3497) (p 3747) (p 4173) (p 4228) (p 4336) (p 4393) (derived73528 p h) (derived73400 p h) (derived57625 p h)

theorem derived96111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4140) ∨ (p 2156) ∨ (¬ p 3051) ∨ (¬ p 5472) :=
  ElevenRUP.step96111 (p 2156) (p 3051) (p 3646) (p 4140) (p 4393) (p 5472) (derived73436 p h) (derived42309 p h)

theorem derived96112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 3434) ∨ (p 2192) ∨ (p 2210) ∨ (p 3425) ∨ (¬ p 4733) ∨ (¬ p 2761) ∨ (¬ p 5254) :=
  ElevenRUP.step96112 (p 2192) (p 2210) (p 2761) (p 3425) (p 3434) (p 3471) (p 3555) (p 4173) (p 4393) (p 4733) (p 5254) (derived73528 p h) (derived73412 p h) (derived73396 p h) (derived55627 p h)

theorem derived96113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 3830) ∨ (¬ p 5254) ∨ (¬ p 3707) ∨ (¬ p 2252) ∨ (p 2284) ∨ (p 2946) ∨ (p 2608) ∨ (¬ p 2750) :=
  ElevenRUP.step96113 (p 2252) (p 2284) (p 2608) (p 2750) (p 2946) (p 2952) (p 3707) (p 3830) (p 3952) (p 3954) (p 4393) (p 5254) (derived73496 p h) (derived73330 p h) (derived73498 p h) (derived52034 p h)

theorem derived96114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4441) ∨ (¬ p 5472) ∨ (¬ p 2957) ∨ (p 2156) ∨ (¬ p 3156) ∨ (¬ p 3955) :=
  ElevenRUP.step96114 (p 2156) (p 2957) (p 3156) (p 3646) (p 3955) (p 4393) (p 4441) (p 5472) (derived73436 p h) (derived59897 p h)

theorem derived96116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 4393) ∨ (p 2156) ∨ (p 3156) ∨ (¬ p 4336) ∨ (¬ p 3747) :=
  ElevenRUP.step96116 (p 2156) (p 3156) (p 3497) (p 3646) (p 3747) (p 4228) (p 4336) (p 4393) (derived73436 p h) (derived73400 p h) (derived46667 p h)

theorem derived96117 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4140) ∨ (¬ p 5472) ∨ (p 2284) ∨ (¬ p 2901) :=
  ElevenRUP.step96117 (p 2284) (p 2901) (p 3952) (p 4140) (p 4393) (p 5472) (derived73496 p h) (derived42427 p h)

theorem derived96120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (p 3136) ∨ (p 2284) ∨ (p 2696) :=
  ElevenRUP.step96120 (p 2284) (p 2696) (p 3136) (p 3365) (p 3952) (p 4315) (p 4393) (derived73550 p h) (derived73496 p h) (derived73390 p h) (derived61986 p h)

theorem derived96122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (p 2132) ∨ (p 2860) ∨ (¬ p 4786) ∨ (¬ p 2807) ∨ (¬ p 2761) ∨ (¬ p 2449) ∨ (¬ p 5254) :=
  ElevenRUP.step96122 (p 2132) (p 2138) (p 2449) (p 2761) (p 2807) (p 2860) (p 3758) (p 4393) (p 4786) (p 5254) (derived73214 p h) (derived73456 p h) (derived57482 p h)

theorem derived96125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 3166) ∨ (p 2860) ∨ (¬ p 5254) ∨ (¬ p 3266) ∨ (¬ p 3256) ∨ (¬ p 4786) ∨ (p 2132) :=
  ElevenRUP.step96125 (p 2132) (p 2138) (p 2860) (p 3166) (p 3256) (p 3266) (p 3758) (p 4393) (p 4786) (p 5254) (derived73456 p h) (derived73214 p h) (derived52119 p h)

theorem derived96127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4053) ∨ (¬ p 4338) ∨ (p 2860) ∨ (¬ p 4878) :=
  ElevenRUP.step96127 (p 2860) (p 3758) (p 4053) (p 4338) (p 4393) (p 4878) (derived73456 p h) (derived50761 p h)

theorem derived96128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4393) ∨ (¬ p 4850) ∨ (¬ p 5248) ∨ (p 2946) ∨ (¬ p 2341) ∨ (p 2284) ∨ (¬ p 3266) ∨ (¬ p 2459) :=
  ElevenRUP.step96128 (p 2284) (p 2341) (p 2459) (p 2946) (p 2952) (p 3266) (p 3952) (p 4393) (p 4850) (p 5248) (derived73330 p h) (derived73496 p h) (derived48028 p h)

theorem derived96136 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 5400) ∨ (¬ p 2598) ∨ (¬ p 3204) ∨ (p 2396) ∨ (¬ p 2850) ∨ (¬ p 3727) ∨ (p 2307) ∨ (¬ p 4870) ∨ (¬ p 2753) :=
  ElevenRUP.step96136 (p 2307) (p 2313) (p 2396) (p 2598) (p 2753) (p 2761) (p 2850) (p 3204) (p 3727) (p 4107) (p 4381) (p 4870) (p 5400) (derived73574 p h) (derived73514 p h) (derived73238 p h) (derived53944 p h)

theorem derived96141 (p : Nat → Prop) (h : Inputs p) :
    (p 4331) ∨ (¬ p 3564) :=
  ElevenRUP.step96141 (p 3564) (p 4331) (p 6083) (derived74427 p h) (h 13549)

theorem derived96142 (p : Nat → Prop) (h : Inputs p) :
    (p 4422) ∨ (¬ p 3564) :=
  ElevenRUP.step96142 (p 3564) (p 4422) (p 6083) (derived74427 p h) (h 13550)

theorem derived96143 (p : Nat → Prop) (h : Inputs p) :
    (p 5324) ∨ (¬ p 3564) :=
  ElevenRUP.step96143 (p 3564) (p 5324) (p 6083) (derived74427 p h) (h 13552)

theorem derived96144 (p : Nat → Prop) (h : Inputs p) :
    (p 5325) ∨ (¬ p 3564) :=
  ElevenRUP.step96144 (p 3564) (p 5325) (p 6083) (derived74427 p h) (h 13553)

theorem derived96148 (p : Nat → Prop) (h : Inputs p) :
    (p 3801) ∨ (¬ p 3811) :=
  ElevenRUP.step96148 (p 3801) (p 3811) (p 3816) (derived73465 p h) (h 5625)

theorem derived96149 (p : Nat → Prop) (h : Inputs p) :
    (p 4740) ∨ (p 2619) :=
  ElevenRUP.step96149 (p 2619) (p 4740) (p 5887) (derived74189 p h) (h 12308)

theorem derived96150 (p : Nat → Prop) (h : Inputs p) :
    (p 4359) ∨ (p 2619) :=
  ElevenRUP.step96150 (p 2619) (p 4359) (p 5887) (derived74189 p h) (h 12310)

theorem derived96151 (p : Nat → Prop) (h : Inputs p) :
    (p 4741) ∨ (p 2619) :=
  ElevenRUP.step96151 (p 2619) (p 4741) (p 5887) (derived74189 p h) (h 12311)

theorem derived96152 (p : Nat → Prop) (h : Inputs p) :
    (p 4742) ∨ (p 2619) :=
  ElevenRUP.step96152 (p 2619) (p 4742) (p 5887) (derived74189 p h) (h 12312)

theorem derived96153 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 4322) ∨ (¬ p 4952) :=
  ElevenRUP.step96153 (p 3276) (p 4322) (p 4425) (p 4952) (derived73578 p h) (h 34954)

theorem derived96154 (p : Nat → Prop) (h : Inputs p) :
    (p 3193) ∨ (¬ p 4952) ∨ (p 2230) ∨ (¬ p 3347) ∨ (p 2427) ∨ (¬ p 5104) :=
  ElevenRUP.step96154 (p 2230) (p 2427) (p 2589) (p 3193) (p 3222) (p 3347) (p 4235) (p 4952) (p 5104) (derived73364 p h) (derived73284 p h) (derived73536 p h) (derived51266 p h)

theorem derived96156 (p : Nat → Prop) (h : Inputs p) :
    (p 5670) ∨ (p 4149) :=
  ElevenRUP.step96156 (p 4149) (p 5670) (p 6175) (derived74465 p h) (h 15080)

theorem derived96163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4114) ∨ (p 2363) ∨ (¬ p 5022) ∨ (¬ p 2088) ∨ (¬ p 3923) :=
  ElevenRUP.step96163 (p 2088) (p 2363) (p 3923) (p 4114) (p 4347) (p 5022) (derived73560 p h) (derived49413 p h)

theorem derived96165 (p : Nat → Prop) (h : Inputs p) :
    (p 3820) ∨ (¬ p 3425) :=
  ElevenRUP.step96165 (p 3425) (p 3820) (p 6061) (derived74405 p h) (h 13373)

theorem derived96166 (p : Nat → Prop) (h : Inputs p) :
    (p 3577) ∨ (¬ p 3425) :=
  ElevenRUP.step96166 (p 3425) (p 3577) (p 6061) (derived74405 p h) (h 13374)

theorem derived96168 (p : Nat → Prop) (h : Inputs p) :
    (p 5258) ∨ (¬ p 3425) :=
  ElevenRUP.step96168 (p 3425) (p 5258) (p 6061) (derived74405 p h) (h 13377)

theorem derived96169 (p : Nat → Prop) (h : Inputs p) :
    (p 4135) ∨ (¬ p 3246) :=
  ElevenRUP.step96169 (p 3246) (p 4135) (p 6011) (derived74347 p h) (h 13059)

theorem derived96170 (p : Nat → Prop) (h : Inputs p) :
    (p 4192) ∨ (¬ p 3246) :=
  ElevenRUP.step96170 (p 3246) (p 4192) (p 6011) (derived74347 p h) (h 13060)

theorem derived96171 (p : Nat → Prop) (h : Inputs p) :
    (p 5104) ∨ (¬ p 3246) :=
  ElevenRUP.step96171 (p 3246) (p 5104) (p 6011) (derived74347 p h) (h 13062)

theorem derived96173 (p : Nat → Prop) (h : Inputs p) :
    (p 5233) ∨ (¬ p 3434) :=
  ElevenRUP.step96173 (p 3434) (p 5233) (p 6053) (derived74395 p h) (h 13316)

theorem derived96174 (p : Nat → Prop) (h : Inputs p) :
    (p 5234) ∨ (¬ p 3434) :=
  ElevenRUP.step96174 (p 3434) (p 5234) (p 6053) (derived74395 p h) (h 13317)

theorem derived96176 (p : Nat → Prop) (h : Inputs p) :
    (p 5236) ∨ (¬ p 3434) :=
  ElevenRUP.step96176 (p 3434) (p 5236) (p 6053) (derived74395 p h) (h 13320)

theorem derived96177 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 2396) ∨ (¬ p 5260) ∨ (¬ p 4275) ∨ (¬ p 2881) ∨ (¬ p 4638) ∨ (¬ p 3670) ∨ (¬ p 3286) ∨ (¬ p 4117) ∨ (¬ p 5454) ∨ (p 2341) :=
  ElevenRUP.step96177 (p 2341) (p 2396) (p 2881) (p 3276) (p 3286) (p 3551) (p 3670) (p 4107) (p 4117) (p 4275) (p 4425) (p 4638) (p 5260) (p 5454) (derived73578 p h) (derived73514 p h) (derived73408 p h) (derived56151 p h)

theorem derived96180 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (¬ p 3286) ∨ (¬ p 2737) ∨ (¬ p 5454) ∨ (p 2946) :=
  ElevenRUP.step96180 (p 2737) (p 2946) (p 2952) (p 3286) (p 3599) (p 4379) (p 5454) (derived73572 p h) (derived73330 p h) (derived54998 p h)

theorem derived96183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 5284) ∨ (¬ p 5454) :=
  ElevenRUP.step96183 (p 3670) (p 5284) (p 5387) (p 5454) (derived74025 p h) (h 37734)

theorem derived96196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (p 3461) ∨ (¬ p 5454) ∨ (¬ p 4976) ∨ (p 3564) ∨ (¬ p 4421) :=
  ElevenRUP.step96196 (p 3461) (p 3564) (p 3670) (p 4137) (p 4191) (p 4421) (p 4976) (p 5454) (derived73530 p h) (derived73524 p h) (derived64326 p h)

theorem derived96197 (p : Nat → Prop) (h : Inputs p) :
    (p 4312) ∨ (p 3156) :=
  ElevenRUP.step96197 (p 3156) (p 4312) (p 5998) (derived74333 p h) (h 12974)

theorem derived96198 (p : Nat → Prop) (h : Inputs p) :
    (p 3661) ∨ (p 3156) :=
  ElevenRUP.step96198 (p 3156) (p 3661) (p 5998) (derived74333 p h) (h 12976)

theorem derived96199 (p : Nat → Prop) (h : Inputs p) :
    (p 5062) ∨ (p 3156) :=
  ElevenRUP.step96199 (p 3156) (p 5062) (p 5998) (derived74333 p h) (h 12977)

theorem derived96209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2088) ∨ (¬ p 4416) ∨ (¬ p 2608) ∨ (¬ p 5312) :=
  ElevenRUP.step96209 (p 2088) (p 2608) (p 3073) (p 3857) (p 4416) (p 5312) (derived73480 p h) (derived42229 p h)

theorem derived96214 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4353) ∨ (p 3609) ∨ (¬ p 4352) ∨ (¬ p 4351) :=
  ElevenRUP.step96214 (p 3609) (p 4340) (p 4351) (p 4352) (p 4353) (derived73558 p h) (h 6614)

theorem derived96219 (p : Nat → Prop) (h : Inputs p) :
    (p 4027) ∨ (p 3670) :=
  ElevenRUP.step96219 (p 3670) (p 4027) (p 6103) (derived74449 p h) (h 13764)

theorem derived96220 (p : Nat → Prop) (h : Inputs p) :
    (p 4028) ∨ (p 3670) :=
  ElevenRUP.step96220 (p 3670) (p 4028) (p 6103) (derived74449 p h) (h 13766)

theorem derived96223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5338) ∨ (p 2098) ∨ (¬ p 3366) ∨ (¬ p 3599) :=
  ElevenRUP.step96223 (p 2098) (p 2104) (p 3366) (p 3599) (p 4379) (p 5338) (derived73204 p h) (derived73571 p h) (h 21819)

theorem derived96225 (p : Nat → Prop) (h : Inputs p) :
    (p 3670) ∨ (¬ p 2518) ∨ (¬ p 4604) ∨ (¬ p 5228) ∨ (¬ p 4736) ∨ (¬ p 2528) ∨ (¬ p 3379) ∨ (¬ p 3461) ∨ (¬ p 3425) :=
  ElevenRUP.step96225 (p 2518) (p 2528) (p 3379) (p 3425) (p 3461) (p 3670) (p 4604) (p 4736) (p 5228) (p 5387) (derived74026 p h) (derived59322 p h)

theorem derived96228 (p : Nat → Prop) (h : Inputs p) :
    (p 3670) ∨ (¬ p 2761) ∨ (¬ p 3366) ∨ (¬ p 4395) ∨ (¬ p 5228) ∨ (¬ p 3115) ∨ (p 3156) ∨ (¬ p 4377) ∨ (¬ p 3425) ∨ (¬ p 2220) ∨ (¬ p 3370) :=
  ElevenRUP.step96228 (p 2220) (p 2761) (p 3115) (p 3156) (p 3366) (p 3370) (p 3425) (p 3497) (p 3670) (p 4377) (p 4395) (p 5228) (p 5387) (derived74026 p h) (derived73400 p h) (derived55926 p h)

theorem derived96231 (p : Nat → Prop) (h : Inputs p) :
    (p 5486) ∨ (p 3830) :=
  ElevenRUP.step96231 (p 3830) (p 5486) (p 6127) (derived74461 p h) (h 14006)

theorem derived96232 (p : Nat → Prop) (h : Inputs p) :
    (p 5487) ∨ (p 3830) :=
  ElevenRUP.step96232 (p 3830) (p 5487) (p 6127) (derived74461 p h) (h 14007)

theorem derived96234 (p : Nat → Prop) (h : Inputs p) :
    (p 5458) ∨ (¬ p 3755) :=
  ElevenRUP.step96234 (p 3755) (p 5458) (p 6122) (derived74459 p h) (h 13919)

theorem derived96235 (p : Nat → Prop) (h : Inputs p) :
    (p 5459) ∨ (¬ p 3755) :=
  ElevenRUP.step96235 (p 3755) (p 5459) (p 6122) (derived74459 p h) (h 13920)

theorem derived96236 (p : Nat → Prop) (h : Inputs p) :
    (p 5460) ∨ (¬ p 3755) :=
  ElevenRUP.step96236 (p 3755) (p 5460) (p 6122) (derived74459 p h) (h 13922)

theorem derived96243 (p : Nat → Prop) (h : Inputs p) :
    (p 4038) ∨ (¬ p 3654) :=
  ElevenRUP.step96243 (p 3654) (p 4038) (p 6101) (derived74447 p h) (h 13735)

theorem derived96244 (p : Nat → Prop) (h : Inputs p) :
    (p 4036) ∨ (¬ p 3654) :=
  ElevenRUP.step96244 (p 3654) (p 4036) (p 6101) (derived74447 p h) (h 13736)

theorem derived96246 (p : Nat → Prop) (h : Inputs p) :
    (p 5373) ∨ (¬ p 3641) :=
  ElevenRUP.step96246 (p 3641) (p 5373) (p 6098) (derived74443 p h) (h 13703)

theorem derived96247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 4354) :=
  ElevenRUP.step96247 (p 3641) (p 4354) (p 6098) (derived74443 p h) (h 13704)

theorem derived96249 (p : Nat → Prop) (h : Inputs p) :
    (p 5375) ∨ (¬ p 3641) :=
  ElevenRUP.step96249 (p 3641) (p 5375) (p 6098) (derived74443 p h) (h 13707)

theorem derived96250 (p : Nat → Prop) (h : Inputs p) :
    (p 5362) ∨ (¬ p 3631) :=
  ElevenRUP.step96250 (p 3631) (p 5362) (p 6095) (derived74439 p h) (h 13673)

theorem derived96251 (p : Nat → Prop) (h : Inputs p) :
    (p 5363) ∨ (¬ p 3631) :=
  ElevenRUP.step96251 (p 3631) (p 5363) (p 6095) (derived74439 p h) (h 13674)

theorem derived96254 (p : Nat → Prop) (h : Inputs p) :
    (p 5343) ∨ (¬ p 3609) :=
  ElevenRUP.step96254 (p 3609) (p 5343) (p 6089) (derived74435 p h) (h 13638)

theorem derived96255 (p : Nat → Prop) (h : Inputs p) :
    (p 5344) ∨ (¬ p 3609) :=
  ElevenRUP.step96255 (p 3609) (p 5344) (p 6089) (derived74435 p h) (h 13639)

theorem derived96260 (p : Nat → Prop) (h : Inputs p) :
    (p 5332) ∨ (¬ p 3599) :=
  ElevenRUP.step96260 (p 3599) (p 5332) (p 6086) (derived74431 p h) (h 13623)

theorem derived96261 (p : Nat → Prop) (h : Inputs p) :
    (p 5333) ∨ (¬ p 3599) :=
  ElevenRUP.step96261 (p 3599) (p 5333) (p 6086) (derived74431 p h) (h 13625)

theorem derived96262 (p : Nat → Prop) (h : Inputs p) :
    (p 5317) ∨ (¬ p 3537) :=
  ElevenRUP.step96262 (p 3537) (p 5317) (p 6080) (derived74423 p h) (h 13509)

theorem derived96264 (p : Nat → Prop) (h : Inputs p) :
    (p 5315) ∨ (¬ p 3537) :=
  ElevenRUP.step96264 (p 3537) (p 5315) (p 6080) (derived74423 p h) (h 13511)

theorem derived96265 (p : Nat → Prop) (h : Inputs p) :
    (p 5316) ∨ (¬ p 3537) :=
  ElevenRUP.step96265 (p 3537) (p 5316) (p 6080) (derived74423 p h) (h 13512)

theorem derived96266 (p : Nat → Prop) (h : Inputs p) :
    (p 5307) ∨ (¬ p 3527) :=
  ElevenRUP.step96266 (p 3527) (p 5307) (p 6077) (derived74419 p h) (h 13490)

theorem derived96267 (p : Nat → Prop) (h : Inputs p) :
    (p 4189) ∨ (¬ p 3527) :=
  ElevenRUP.step96267 (p 3527) (p 4189) (p 6077) (derived74419 p h) (h 13491)

theorem derived96270 (p : Nat → Prop) (h : Inputs p) :
    (p 5299) ∨ (¬ p 3516) :=
  ElevenRUP.step96270 (p 3516) (p 5299) (p 6074) (derived74415 p h) (h 13472)

theorem derived96273 (p : Nat → Prop) (h : Inputs p) :
    (p 5300) ∨ (¬ p 3516) :=
  ElevenRUP.step96273 (p 3516) (p 5300) (p 6074) (derived74415 p h) (h 13475)

theorem derived96274 (p : Nat → Prop) (h : Inputs p) :
    (p 4390) ∨ (¬ p 3422) :=
  ElevenRUP.step96274 (p 3422) (p 4390) (p 6050) (derived74391 p h) (h 13296)

theorem derived96275 (p : Nat → Prop) (h : Inputs p) :
    (p 4375) ∨ (¬ p 3422) :=
  ElevenRUP.step96275 (p 3422) (p 4375) (p 6050) (derived74391 p h) (h 13297)

theorem derived96279 (p : Nat → Prop) (h : Inputs p) :
    (p 5201) ∨ (¬ p 3389) :=
  ElevenRUP.step96279 (p 3389) (p 5201) (p 6041) (derived74379 p h) (h 13243)

theorem derived96281 (p : Nat → Prop) (h : Inputs p) :
    (p 4279) ∨ (¬ p 3389) :=
  ElevenRUP.step96281 (p 3389) (p 4279) (p 6041) (derived74379 p h) (h 13246)

theorem derived96282 (p : Nat → Prop) (h : Inputs p) :
    (p 5171) ∨ (p 3343) :=
  ElevenRUP.step96282 (p 3343) (p 5171) (p 6031) (derived74369 p h) (h 13179)

theorem derived96283 (p : Nat → Prop) (h : Inputs p) :
    (p 5170) ∨ (p 3343) :=
  ElevenRUP.step96283 (p 3343) (p 5170) (p 6031) (derived74369 p h) (h 13181)

theorem derived96284 (p : Nat → Prop) (h : Inputs p) :
    (p 5172) ∨ (p 3343) :=
  ElevenRUP.step96284 (p 3343) (p 5172) (p 6031) (derived74369 p h) (h 13182)

theorem derived96286 (p : Nat → Prop) (h : Inputs p) :
    (p 3547) ∨ (¬ p 3309) :=
  ElevenRUP.step96286 (p 3309) (p 3547) (p 6023) (derived74363 p h) (h 13133)

theorem derived96287 (p : Nat → Prop) (h : Inputs p) :
    (p 4452) ∨ (¬ p 3309) :=
  ElevenRUP.step96287 (p 3309) (p 4452) (p 6023) (derived74363 p h) (h 13134)

theorem derived96289 (p : Nat → Prop) (h : Inputs p) :
    (p 5145) ∨ (¬ p 3309) :=
  ElevenRUP.step96289 (p 3309) (p 5145) (p 6023) (derived74363 p h) (h 13137)

theorem derived96290 (p : Nat → Prop) (h : Inputs p) :
    (p 5127) ∨ (p 3276) :=
  ElevenRUP.step96290 (p 3276) (p 5127) (p 6019) (derived74357 p h) (h 13108)

theorem derived96291 (p : Nat → Prop) (h : Inputs p) :
    (p 5126) ∨ (p 3276) :=
  ElevenRUP.step96291 (p 3276) (p 5126) (p 6019) (derived74357 p h) (h 13110)

theorem derived96293 (p : Nat → Prop) (h : Inputs p) :
    (p 5129) ∨ (p 3276) :=
  ElevenRUP.step96293 (p 3276) (p 5129) (p 6019) (derived74357 p h) (h 13112)

theorem derived96294 (p : Nat → Prop) (h : Inputs p) :
    (p 5117) ∨ (p 3266) :=
  ElevenRUP.step96294 (p 3266) (p 5117) (p 6016) (derived74353 p h) (h 13091)

theorem derived96295 (p : Nat → Prop) (h : Inputs p) :
    (p 5116) ∨ (p 3266) :=
  ElevenRUP.step96295 (p 3266) (p 5116) (p 6016) (derived74353 p h) (h 13093)

theorem derived96297 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (p 3266) :=
  ElevenRUP.step96297 (p 3266) (p 5119) (p 6016) (derived74353 p h) (h 13095)

theorem derived96298 (p : Nat → Prop) (h : Inputs p) :
    (p 4350) ∨ (¬ p 3256) :=
  ElevenRUP.step96298 (p 3256) (p 4350) (p 6014) (derived74351 p h) (h 13079)

theorem derived96299 (p : Nat → Prop) (h : Inputs p) :
    (p 5111) ∨ (¬ p 3256) :=
  ElevenRUP.step96299 (p 3256) (p 5111) (p 6014) (derived74351 p h) (h 13080)

theorem derived96302 (p : Nat → Prop) (h : Inputs p) :
    (p 3658) ∨ (¬ p 3201) :=
  ElevenRUP.step96302 (p 3201) (p 3658) (p 6005) (derived74343 p h) (h 13020)

theorem derived96303 (p : Nat → Prop) (h : Inputs p) :
    (p 5085) ∨ (¬ p 3201) :=
  ElevenRUP.step96303 (p 3201) (p 5085) (p 6005) (derived74343 p h) (h 13021)

theorem derived96304 (p : Nat → Prop) (h : Inputs p) :
    (p 5086) ∨ (¬ p 3201) :=
  ElevenRUP.step96304 (p 3201) (p 5086) (p 6005) (derived74343 p h) (h 13023)

theorem derived96305 (p : Nat → Prop) (h : Inputs p) :
    (p 5087) ∨ (¬ p 3201) :=
  ElevenRUP.step96305 (p 3201) (p 5087) (p 6005) (derived74343 p h) (h 13024)

theorem derived96306 (p : Nat → Prop) (h : Inputs p) :
    (p 4288) ∨ (¬ p 3189) :=
  ElevenRUP.step96306 (p 3189) (p 4288) (p 6002) (derived74339 p h) (h 13000)

theorem derived96307 (p : Nat → Prop) (h : Inputs p) :
    (p 3859) ∨ (¬ p 3189) :=
  ElevenRUP.step96307 (p 3189) (p 3859) (p 6002) (derived74339 p h) (h 13001)

theorem derived96308 (p : Nat → Prop) (h : Inputs p) :
    (p 5078) ∨ (¬ p 3189) :=
  ElevenRUP.step96308 (p 3189) (p 5078) (p 6002) (derived74339 p h) (h 13003)

theorem derived96310 (p : Nat → Prop) (h : Inputs p) :
    (p 2532) ∨ (¬ p 3146) :=
  ElevenRUP.step96310 (p 2532) (p 3146) (p 5996) (derived74331 p h) (h 12963)

theorem derived96311 (p : Nat → Prop) (h : Inputs p) :
    (p 2533) ∨ (¬ p 3146) :=
  ElevenRUP.step96311 (p 2533) (p 3146) (p 5996) (derived74331 p h) (h 12964)

theorem derived96313 (p : Nat → Prop) (h : Inputs p) :
    (p 5059) ∨ (¬ p 3146) :=
  ElevenRUP.step96313 (p 3146) (p 5059) (p 5996) (derived74331 p h) (h 12967)

theorem derived96314 (p : Nat → Prop) (h : Inputs p) :
    (p 5051) ∨ (¬ p 3136) :=
  ElevenRUP.step96314 (p 3136) (p 5051) (p 5993) (derived74327 p h) (h 12946)

theorem derived96315 (p : Nat → Prop) (h : Inputs p) :
    (p 4313) ∨ (¬ p 3136) :=
  ElevenRUP.step96315 (p 3136) (p 4313) (p 5993) (derived74327 p h) (h 12947)

theorem derived96317 (p : Nat → Prop) (h : Inputs p) :
    (p 5053) ∨ (¬ p 3136) :=
  ElevenRUP.step96317 (p 3136) (p 5053) (p 5993) (derived74327 p h) (h 12950)

theorem derived96318 (p : Nat → Prop) (h : Inputs p) :
    (p 5045) ∨ (¬ p 3125) :=
  ElevenRUP.step96318 (p 3125) (p 5045) (p 5990) (derived74323 p h) (h 12928)

theorem derived96319 (p : Nat → Prop) (h : Inputs p) :
    (p 4334) ∨ (¬ p 3125) :=
  ElevenRUP.step96319 (p 3125) (p 4334) (p 5990) (derived74323 p h) (h 12929)

theorem derived96321 (p : Nat → Prop) (h : Inputs p) :
    (p 4368) ∨ (¬ p 3125) :=
  ElevenRUP.step96321 (p 3125) (p 4368) (p 5990) (derived74323 p h) (h 12932)

theorem derived96322 (p : Nat → Prop) (h : Inputs p) :
    (p 4040) ∨ (p 3115) :=
  ElevenRUP.step96322 (p 3115) (p 4040) (p 5986) (derived74317 p h) (h 12905)

theorem derived96323 (p : Nat → Prop) (h : Inputs p) :
    (p 4314) ∨ (p 3115) :=
  ElevenRUP.step96323 (p 3115) (p 4314) (p 5986) (derived74317 p h) (h 12907)

theorem derived96326 (p : Nat → Prop) (h : Inputs p) :
    (p 5026) ∨ (p 3105) :=
  ElevenRUP.step96326 (p 3105) (p 5026) (p 5983) (derived74313 p h) (h 12887)

theorem derived96327 (p : Nat → Prop) (h : Inputs p) :
    (p 5025) ∨ (p 3105) :=
  ElevenRUP.step96327 (p 3105) (p 5025) (p 5983) (derived74313 p h) (h 12889)

theorem derived96330 (p : Nat → Prop) (h : Inputs p) :
    (p 4352) ∨ (¬ p 3073) :=
  ElevenRUP.step96330 (p 3073) (p 4352) (p 5975) (derived74303 p h) (h 12840)

theorem derived96331 (p : Nat → Prop) (h : Inputs p) :
    (p 4351) ∨ (¬ p 3073) :=
  ElevenRUP.step96331 (p 3073) (p 4351) (p 5975) (derived74303 p h) (h 12841)

theorem derived96334 (p : Nat → Prop) (h : Inputs p) :
    (p 4985) ∨ (p 3051) :=
  ElevenRUP.step96334 (p 3051) (p 4985) (p 5968) (derived74297 p h) (h 12800)

theorem derived96335 (p : Nat → Prop) (h : Inputs p) :
    (p 4984) ∨ (p 3051) :=
  ElevenRUP.step96335 (p 3051) (p 4984) (p 5968) (derived74297 p h) (h 12801)

theorem derived96336 (p : Nat → Prop) (h : Inputs p) :
    (p 4986) ∨ (p 3051) :=
  ElevenRUP.step96336 (p 3051) (p 4986) (p 5968) (derived74297 p h) (h 12802)

theorem derived96337 (p : Nat → Prop) (h : Inputs p) :
    (p 3691) ∨ (p 3051) :=
  ElevenRUP.step96337 (p 3051) (p 3691) (p 5968) (derived74297 p h) (h 12804)

theorem derived96338 (p : Nat → Prop) (h : Inputs p) :
    (p 4959) ∨ (¬ p 2992) :=
  ElevenRUP.step96338 (p 2992) (p 4959) (p 5960) (derived74287 p h) (h 12744)

theorem derived96339 (p : Nat → Prop) (h : Inputs p) :
    (p 4282) ∨ (¬ p 2992) :=
  ElevenRUP.step96339 (p 2992) (p 4282) (p 5960) (derived74287 p h) (h 12745)

theorem derived96340 (p : Nat → Prop) (h : Inputs p) :
    (p 4365) ∨ (¬ p 2992) :=
  ElevenRUP.step96340 (p 2992) (p 4365) (p 5960) (derived74287 p h) (h 12746)

theorem derived96342 (p : Nat → Prop) (h : Inputs p) :
    (p 4947) ∨ (p 2982) :=
  ElevenRUP.step96342 (p 2982) (p 4947) (p 5956) (derived74281 p h) (h 12719)

theorem derived96343 (p : Nat → Prop) (h : Inputs p) :
    (p 3237) ∨ (p 2982) :=
  ElevenRUP.step96343 (p 2982) (p 3237) (p 5956) (derived74281 p h) (h 12721)

theorem derived96345 (p : Nat → Prop) (h : Inputs p) :
    (p 4950) ∨ (p 2982) :=
  ElevenRUP.step96345 (p 2982) (p 4950) (p 5956) (derived74281 p h) (h 12723)

theorem derived96346 (p : Nat → Prop) (h : Inputs p) :
    (p 4388) ∨ (p 2972) :=
  ElevenRUP.step96346 (p 2972) (p 4388) (p 5953) (derived74277 p h) (h 12701)

theorem derived96347 (p : Nat → Prop) (h : Inputs p) :
    (p 4938) ∨ (p 2972) :=
  ElevenRUP.step96347 (p 2972) (p 4938) (p 5953) (derived74277 p h) (h 12703)

theorem derived96350 (p : Nat → Prop) (h : Inputs p) :
    (p 3699) ∨ (p 2901) :=
  ElevenRUP.step96350 (p 2901) (p 3699) (p 5947) (derived74269 p h) (h 12664)

theorem derived96351 (p : Nat → Prop) (h : Inputs p) :
    (p 4386) ∨ (p 2901) :=
  ElevenRUP.step96351 (p 2901) (p 4386) (p 5947) (derived74269 p h) (h 12666)

theorem derived96352 (p : Nat → Prop) (h : Inputs p) :
    (p 4917) ∨ (p 2901) :=
  ElevenRUP.step96352 (p 2901) (p 4917) (p 5947) (derived74269 p h) (h 12667)

theorem derived96354 (p : Nat → Prop) (h : Inputs p) :
    (p 4909) ∨ (p 2891) :=
  ElevenRUP.step96354 (p 2891) (p 4909) (p 5944) (derived74265 p h) (h 12647)

theorem derived96355 (p : Nat → Prop) (h : Inputs p) :
    (p 3554) ∨ (p 2891) :=
  ElevenRUP.step96355 (p 2891) (p 3554) (p 5944) (derived74265 p h) (h 12649)

theorem derived96357 (p : Nat → Prop) (h : Inputs p) :
    (p 4911) ∨ (p 2891) :=
  ElevenRUP.step96357 (p 2891) (p 4911) (p 5944) (derived74265 p h) (h 12651)

theorem derived96358 (p : Nat → Prop) (h : Inputs p) :
    (p 4042) ∨ (¬ p 2881) :=
  ElevenRUP.step96358 (p 2881) (p 4042) (p 5942) (derived74263 p h) (h 12636)

theorem derived96359 (p : Nat → Prop) (h : Inputs p) :
    (p 3747) ∨ (¬ p 2881) :=
  ElevenRUP.step96359 (p 2881) (p 3747) (p 5942) (derived74263 p h) (h 12637)

theorem derived96360 (p : Nat → Prop) (h : Inputs p) :
    (p 4904) ∨ (¬ p 2881) :=
  ElevenRUP.step96360 (p 2881) (p 4904) (p 5942) (derived74263 p h) (h 12639)

theorem derived96362 (p : Nat → Prop) (h : Inputs p) :
    (p 4169) ∨ (p 2870) :=
  ElevenRUP.step96362 (p 2870) (p 4169) (p 5938) (derived74257 p h) (h 12611)

theorem derived96363 (p : Nat → Prop) (h : Inputs p) :
    (p 4136) ∨ (p 2870) :=
  ElevenRUP.step96363 (p 2870) (p 4136) (p 5938) (derived74257 p h) (h 12613)

theorem derived96365 (p : Nat → Prop) (h : Inputs p) :
    (p 4895) ∨ (p 2870) :=
  ElevenRUP.step96365 (p 2870) (p 4895) (p 5938) (derived74257 p h) (h 12615)

theorem derived96366 (p : Nat → Prop) (h : Inputs p) :
    (p 3695) ∨ (¬ p 2850) :=
  ElevenRUP.step96366 (p 2850) (p 3695) (p 5933) (derived74251 p h) (h 12582)

theorem derived96367 (p : Nat → Prop) (h : Inputs p) :
    (p 3582) ∨ (¬ p 2850) :=
  ElevenRUP.step96367 (p 2850) (p 3582) (p 5933) (derived74251 p h) (h 12583)

theorem derived96372 (p : Nat → Prop) (h : Inputs p) :
    (p 3371) ∨ (¬ p 2839) :=
  ElevenRUP.step96372 (p 2839) (p 3371) (p 5930) (derived74247 p h) (h 12567)

theorem derived96373 (p : Nat → Prop) (h : Inputs p) :
    (p 4243) ∨ (¬ p 2839) :=
  ElevenRUP.step96373 (p 2839) (p 4243) (p 5930) (derived74247 p h) (h 12569)

theorem derived96374 (p : Nat → Prop) (h : Inputs p) :
    (p 3953) ∨ (p 2829) :=
  ElevenRUP.step96374 (p 2829) (p 3953) (p 5926) (derived74241 p h) (h 12543)

theorem derived96376 (p : Nat → Prop) (h : Inputs p) :
    (p 3918) ∨ (p 2829) :=
  ElevenRUP.step96376 (p 2829) (p 3918) (p 5926) (derived74241 p h) (h 12545)

theorem derived96378 (p : Nat → Prop) (h : Inputs p) :
    (p 4326) ∨ (¬ p 2819) :=
  ElevenRUP.step96378 (p 2819) (p 4326) (p 5924) (derived74239 p h) (h 12530)

theorem derived96379 (p : Nat → Prop) (h : Inputs p) :
    (p 4861) ∨ (¬ p 2819) :=
  ElevenRUP.step96379 (p 2819) (p 4861) (p 5924) (derived74239 p h) (h 12531)

theorem derived96381 (p : Nat → Prop) (h : Inputs p) :
    (p 4863) ∨ (¬ p 2819) :=
  ElevenRUP.step96381 (p 2819) (p 4863) (p 5924) (derived74239 p h) (h 12534)

theorem derived96382 (p : Nat → Prop) (h : Inputs p) :
    (p 4328) ∨ (¬ p 2797) :=
  ElevenRUP.step96382 (p 2797) (p 4328) (p 5918) (derived74231 p h) (h 12491)

theorem derived96383 (p : Nat → Prop) (h : Inputs p) :
    (p 4426) ∨ (¬ p 2797) :=
  ElevenRUP.step96383 (p 2797) (p 4426) (p 5918) (derived74231 p h) (h 12492)

theorem derived96384 (p : Nat → Prop) (h : Inputs p) :
    (p 4845) ∨ (¬ p 2797) :=
  ElevenRUP.step96384 (p 2797) (p 4845) (p 5918) (derived74231 p h) (h 12494)

theorem derived96385 (p : Nat → Prop) (h : Inputs p) :
    (p 4846) ∨ (¬ p 2797) :=
  ElevenRUP.step96385 (p 2797) (p 4846) (p 5918) (derived74231 p h) (h 12495)

theorem derived96386 (p : Nat → Prop) (h : Inputs p) :
    (p 4824) ∨ (p 2761) :=
  ElevenRUP.step96386 (p 2761) (p 4824) (p 5914) (derived74225 p h) (h 12465)

theorem derived96387 (p : Nat → Prop) (h : Inputs p) :
    (p 4823) ∨ (p 2761) :=
  ElevenRUP.step96387 (p 2761) (p 4823) (p 5914) (derived74225 p h) (h 12467)

theorem derived96390 (p : Nat → Prop) (h : Inputs p) :
    (p 4424) ∨ (p 2707) :=
  ElevenRUP.step96390 (p 2707) (p 4424) (p 5905) (derived74213 p h) (h 12412)

theorem derived96391 (p : Nat → Prop) (h : Inputs p) :
    (p 4794) ∨ (p 2707) :=
  ElevenRUP.step96391 (p 2707) (p 4794) (p 5905) (derived74213 p h) (h 12413)

theorem derived96392 (p : Nat → Prop) (h : Inputs p) :
    (p 4400) ∨ (p 2707) :=
  ElevenRUP.step96392 (p 2707) (p 4400) (p 5905) (derived74213 p h) (h 12414)

theorem derived96394 (p : Nat → Prop) (h : Inputs p) :
    (p 4325) ∨ (¬ p 2685) :=
  ElevenRUP.step96394 (p 2685) (p 4325) (p 5900) (derived74207 p h) (h 12383)

theorem derived96395 (p : Nat → Prop) (h : Inputs p) :
    (p 4781) ∨ (¬ p 2685) :=
  ElevenRUP.step96395 (p 2685) (p 4781) (p 5900) (derived74207 p h) (h 12384)

theorem derived96396 (p : Nat → Prop) (h : Inputs p) :
    (p 4782) ∨ (¬ p 2685) :=
  ElevenRUP.step96396 (p 2685) (p 4782) (p 5900) (derived74207 p h) (h 12386)

theorem derived96397 (p : Nat → Prop) (h : Inputs p) :
    (p 4783) ∨ (¬ p 2685) :=
  ElevenRUP.step96397 (p 2685) (p 4783) (p 5900) (derived74207 p h) (h 12387)

theorem derived96398 (p : Nat → Prop) (h : Inputs p) :
    (p 4417) ∨ (¬ p 2668) :=
  ElevenRUP.step96398 (p 2668) (p 4417) (p 5897) (derived74203 p h) (h 12366)

theorem derived96399 (p : Nat → Prop) (h : Inputs p) :
    (p 4341) ∨ (¬ p 2668) :=
  ElevenRUP.step96399 (p 2668) (p 4341) (p 5897) (derived74203 p h) (h 12367)

theorem derived96400 (p : Nat → Prop) (h : Inputs p) :
    (p 4773) ∨ (¬ p 2668) :=
  ElevenRUP.step96400 (p 2668) (p 4773) (p 5897) (derived74203 p h) (h 12369)

theorem derived96401 (p : Nat → Prop) (h : Inputs p) :
    (p 4774) ∨ (¬ p 2668) :=
  ElevenRUP.step96401 (p 2668) (p 4774) (p 5897) (derived74203 p h) (h 12370)

theorem derived96402 (p : Nat → Prop) (h : Inputs p) :
    (p 3683) ∨ (¬ p 2630) :=
  ElevenRUP.step96402 (p 2630) (p 3683) (p 5891) (derived74195 p h) (h 12331)

theorem derived96403 (p : Nat → Prop) (h : Inputs p) :
    (p 3475) ∨ (¬ p 2630) :=
  ElevenRUP.step96403 (p 2630) (p 3475) (p 5891) (derived74195 p h) (h 12332)

theorem derived96406 (p : Nat → Prop) (h : Inputs p) :
    (p 2753) ∨ (p 2608) :=
  ElevenRUP.step96406 (p 2608) (p 2753) (p 5884) (derived74185 p h) (h 12291)

theorem derived96408 (p : Nat → Prop) (h : Inputs p) :
    (p 3873) ∨ (p 2608) :=
  ElevenRUP.step96408 (p 2608) (p 3873) (p 5884) (derived74185 p h) (h 12294)

theorem derived96409 (p : Nat → Prop) (h : Inputs p) :
    (p 3096) ∨ (p 2563) :=
  ElevenRUP.step96409 (p 2563) (p 3096) (p 5878) (derived74177 p h) (h 12257)

theorem derived96410 (p : Nat → Prop) (h : Inputs p) :
    (p 2590) ∨ (p 2563) :=
  ElevenRUP.step96410 (p 2563) (p 2590) (p 5878) (derived74177 p h) (h 12259)

theorem derived96413 (p : Nat → Prop) (h : Inputs p) :
    (p 4241) ∨ (p 2440) :=
  ElevenRUP.step96413 (p 2440) (p 4241) (p 5873) (derived74171 p h) (h 12228)

theorem derived96414 (p : Nat → Prop) (h : Inputs p) :
    (p 3413) ∨ (p 2440) :=
  ElevenRUP.step96414 (p 2440) (p 3413) (p 5873) (derived74171 p h) (h 12229)

theorem derived96415 (p : Nat → Prop) (h : Inputs p) :
    (p 4705) ∨ (p 2440) :=
  ElevenRUP.step96415 (p 2440) (p 4705) (p 5873) (derived74171 p h) (h 12232)

theorem derived96416 (p : Nat → Prop) (h : Inputs p) :
    (p 4445) ∨ (p 2459) :=
  ElevenRUP.step96416 (p 2459) (p 4445) (p 5863) (derived74161 p h) (h 12168)

theorem derived96417 (p : Nat → Prop) (h : Inputs p) :
    (p 3657) ∨ (p 2459) :=
  ElevenRUP.step96417 (p 2459) (p 3657) (p 5863) (derived74161 p h) (h 12170)

theorem derived96419 (p : Nat → Prop) (h : Inputs p) :
    (p 3950) ∨ (p 2459) :=
  ElevenRUP.step96419 (p 2459) (p 3950) (p 5863) (derived74161 p h) (h 12172)

theorem derived96420 (p : Nat → Prop) (h : Inputs p) :
    (p 4660) ∨ (¬ p 2449) :=
  ElevenRUP.step96420 (p 2449) (p 4660) (p 5861) (derived74159 p h) (h 12157)

theorem derived96421 (p : Nat → Prop) (h : Inputs p) :
    (p 4661) ∨ (¬ p 2449) :=
  ElevenRUP.step96421 (p 2449) (p 4661) (p 5861) (derived74159 p h) (h 12158)

theorem derived96423 (p : Nat → Prop) (h : Inputs p) :
    (p 4663) ∨ (¬ p 2449) :=
  ElevenRUP.step96423 (p 2449) (p 4663) (p 5861) (derived74159 p h) (h 12161)

theorem derived96424 (p : Nat → Prop) (h : Inputs p) :
    (p 4451) ∨ (¬ p 2417) :=
  ElevenRUP.step96424 (p 2417) (p 4451) (p 5852) (derived74147 p h) (h 12106)

theorem derived96425 (p : Nat → Prop) (h : Inputs p) :
    (p 3192) ∨ (¬ p 2417) :=
  ElevenRUP.step96425 (p 2417) (p 3192) (p 5852) (derived74147 p h) (h 12107)

theorem derived96427 (p : Nat → Prop) (h : Inputs p) :
    (p 4641) ∨ (¬ p 2417) :=
  ElevenRUP.step96427 (p 2417) (p 4641) (p 5852) (derived74147 p h) (h 12110)

theorem derived96428 (p : Nat → Prop) (h : Inputs p) :
    (p 4210) ∨ (¬ p 2406) :=
  ElevenRUP.step96428 (p 2406) (p 4210) (p 5849) (derived74143 p h) (h 12088)

theorem derived96429 (p : Nat → Prop) (h : Inputs p) :
    (p 3948) ∨ (¬ p 2406) :=
  ElevenRUP.step96429 (p 2406) (p 3948) (p 5849) (derived74143 p h) (h 12089)

theorem derived96432 (p : Nat → Prop) (h : Inputs p) :
    (p 4617) ∨ (¬ p 2383) :=
  ElevenRUP.step96432 (p 2383) (p 4617) (p 5843) (derived74135 p h) (h 12052)

theorem derived96434 (p : Nat → Prop) (h : Inputs p) :
    (p 4114) ∨ (¬ p 2383) :=
  ElevenRUP.step96434 (p 2383) (p 4114) (p 5843) (derived74135 p h) (h 12055)

theorem derived96435 (p : Nat → Prop) (h : Inputs p) :
    (p 4113) ∨ (¬ p 2383) :=
  ElevenRUP.step96435 (p 2383) (p 4113) (p 5843) (derived74135 p h) (h 12056)

theorem derived96436 (p : Nat → Prop) (h : Inputs p) :
    (p 4171) ∨ (p 2363) :=
  ElevenRUP.step96436 (p 2363) (p 4171) (p 5836) (derived74125 p h) (h 12010)

theorem derived96437 (p : Nat → Prop) (h : Inputs p) :
    (p 3322) ∨ (p 2363) :=
  ElevenRUP.step96437 (p 2363) (p 3322) (p 5836) (derived74125 p h) (h 12012)

theorem derived96440 (p : Nat → Prop) (h : Inputs p) :
    (p 4157) ∨ (¬ p 2352) :=
  ElevenRUP.step96440 (p 2352) (p 4157) (p 5834) (derived74123 p h) (h 11997)

theorem derived96441 (p : Nat → Prop) (h : Inputs p) :
    (p 2510) ∨ (¬ p 2352) :=
  ElevenRUP.step96441 (p 2352) (p 2510) (p 5834) (derived74123 p h) (h 11998)

theorem derived96442 (p : Nat → Prop) (h : Inputs p) :
    (p 4598) ∨ (¬ p 2352) :=
  ElevenRUP.step96442 (p 2352) (p 4598) (p 5834) (derived74123 p h) (h 12000)

theorem derived96445 (p : Nat → Prop) (h : Inputs p) :
    (p 4592) ∨ (¬ p 2341) :=
  ElevenRUP.step96445 (p 2341) (p 4592) (p 5831) (derived74119 p h) (h 11981)

theorem derived96446 (p : Nat → Prop) (h : Inputs p) :
    (p 4403) ∨ (¬ p 2341) :=
  ElevenRUP.step96446 (p 2341) (p 4403) (p 5831) (derived74119 p h) (h 11982)

theorem derived96447 (p : Nat → Prop) (h : Inputs p) :
    (p 4590) ∨ (¬ p 2341) :=
  ElevenRUP.step96447 (p 2341) (p 4590) (p 5831) (derived74119 p h) (h 11983)

theorem derived96448 (p : Nat → Prop) (h : Inputs p) :
    (p 2667) ∨ (¬ p 2331) :=
  ElevenRUP.step96448 (p 2331) (p 2667) (p 5828) (derived74115 p h) (h 11963)

theorem derived96449 (p : Nat → Prop) (h : Inputs p) :
    (p 3987) ∨ (¬ p 2331) :=
  ElevenRUP.step96449 (p 2331) (p 3987) (p 5828) (derived74115 p h) (h 11965)

theorem derived96450 (p : Nat → Prop) (h : Inputs p) :
    (p 4583) ∨ (¬ p 2331) :=
  ElevenRUP.step96450 (p 2331) (p 4583) (p 5828) (derived74115 p h) (h 11966)

theorem derived96452 (p : Nat → Prop) (h : Inputs p) :
    (p 3552) ∨ (¬ p 2295) :=
  ElevenRUP.step96452 (p 2295) (p 3552) (p 5825) (derived74111 p h) (h 11946)

theorem derived96453 (p : Nat → Prop) (h : Inputs p) :
    (p 4156) ∨ (¬ p 2295) :=
  ElevenRUP.step96453 (p 2295) (p 4156) (p 5825) (derived74111 p h) (h 11947)

theorem derived96454 (p : Nat → Prop) (h : Inputs p) :
    (p 4572) ∨ (¬ p 2295) :=
  ElevenRUP.step96454 (p 2295) (p 4572) (p 5825) (derived74111 p h) (h 11949)

theorem derived96456 (p : Nat → Prop) (h : Inputs p) :
    (p 4378) ∨ (¬ p 2264) :=
  ElevenRUP.step96456 (p 2264) (p 4378) (p 5816) (derived74099 p h) (h 11894)

theorem derived96457 (p : Nat → Prop) (h : Inputs p) :
    (p 4044) ∨ (¬ p 2264) :=
  ElevenRUP.step96457 (p 2264) (p 4044) (p 5816) (derived74099 p h) (h 11895)

theorem derived96459 (p : Nat → Prop) (h : Inputs p) :
    (p 4041) ∨ (¬ p 2264) :=
  ElevenRUP.step96459 (p 2264) (p 4041) (p 5816) (derived74099 p h) (h 11898)

theorem derived96460 (p : Nat → Prop) (h : Inputs p) :
    (p 3697) ∨ (p 2220) :=
  ElevenRUP.step96460 (p 2220) (p 3697) (p 5809) (derived74089 p h) (h 11853)

theorem derived96461 (p : Nat → Prop) (h : Inputs p) :
    (p 3696) ∨ (p 2220) :=
  ElevenRUP.step96461 (p 2220) (p 3696) (p 5809) (derived74089 p h) (h 11854)

theorem derived96462 (p : Nat → Prop) (h : Inputs p) :
    (p 4529) ∨ (p 2220) :=
  ElevenRUP.step96462 (p 2220) (p 4529) (p 5809) (derived74089 p h) (h 11856)

theorem derived96464 (p : Nat → Prop) (h : Inputs p) :
    (p 3369) ∨ (p 2210) :=
  ElevenRUP.step96464 (p 2210) (p 3369) (p 5806) (derived74085 p h) (h 11835)

theorem derived96465 (p : Nat → Prop) (h : Inputs p) :
    (p 3370) ∨ (p 2210) :=
  ElevenRUP.step96465 (p 2210) (p 3370) (p 5806) (derived74085 p h) (h 11836)

theorem derived96466 (p : Nat → Prop) (h : Inputs p) :
    (p 4521) ∨ (p 2210) :=
  ElevenRUP.step96466 (p 2210) (p 4521) (p 5806) (derived74085 p h) (h 11838)

theorem derived96468 (p : Nat → Prop) (h : Inputs p) :
    (p 4512) ∨ (p 2192) :=
  ElevenRUP.step96468 (p 2192) (p 4512) (p 5803) (derived74081 p h) (h 11817)

theorem derived96469 (p : Nat → Prop) (h : Inputs p) :
    (p 3957) ∨ (p 2192) :=
  ElevenRUP.step96469 (p 2192) (p 3957) (p 5803) (derived74081 p h) (h 11818)

theorem derived96471 (p : Nat → Prop) (h : Inputs p) :
    (p 4514) ∨ (p 2192) :=
  ElevenRUP.step96471 (p 2192) (p 4514) (p 5803) (derived74081 p h) (h 11821)

theorem derived96472 (p : Nat → Prop) (h : Inputs p) :
    (p 3550) ∨ (¬ p 2177) :=
  ElevenRUP.step96472 (p 2177) (p 3550) (p 5798) (derived74075 p h) (h 11789)

theorem derived96473 (p : Nat → Prop) (h : Inputs p) :
    (p 3325) ∨ (¬ p 2177) :=
  ElevenRUP.step96473 (p 2177) (p 3325) (p 5798) (derived74075 p h) (h 11790)

theorem derived96475 (p : Nat → Prop) (h : Inputs p) :
    (p 4503) ∨ (¬ p 2177) :=
  ElevenRUP.step96475 (p 2177) (p 4503) (p 5798) (derived74075 p h) (h 11793)

theorem derived96476 (p : Nat → Prop) (h : Inputs p) :
    (p 3906) ∨ (p 2166) :=
  ElevenRUP.step96476 (p 2166) (p 3906) (p 5794) (derived74069 p h) (h 11766)

theorem derived96477 (p : Nat → Prop) (h : Inputs p) :
    (p 4492) ∨ (p 2166) :=
  ElevenRUP.step96477 (p 2166) (p 4492) (p 5794) (derived74069 p h) (h 11768)

theorem derived96481 (p : Nat → Prop) (h : Inputs p) :
    (p 4198) ∨ (p 2156) :=
  ElevenRUP.step96481 (p 2156) (p 4198) (p 5791) (derived74065 p h) (h 11752)

theorem derived96482 (p : Nat → Prop) (h : Inputs p) :
    (p 3743) ∨ (p 2156) :=
  ElevenRUP.step96482 (p 2156) (p 3743) (p 5791) (derived74065 p h) (h 11753)

theorem derived96483 (p : Nat → Prop) (h : Inputs p) :
    (p 4475) ∨ (¬ p 2122) :=
  ElevenRUP.step96483 (p 2122) (p 4475) (p 5789) (derived74063 p h) (h 11737)

theorem derived96484 (p : Nat → Prop) (h : Inputs p) :
    (p 3426) ∨ (¬ p 2122) :=
  ElevenRUP.step96484 (p 2122) (p 3426) (p 5789) (derived74063 p h) (h 11738)

theorem derived96485 (p : Nat → Prop) (h : Inputs p) :
    (p 4476) ∨ (¬ p 2122) :=
  ElevenRUP.step96485 (p 2122) (p 4476) (p 5789) (derived74063 p h) (h 11740)

theorem derived96486 (p : Nat → Prop) (h : Inputs p) :
    (p 4477) ∨ (¬ p 2122) :=
  ElevenRUP.step96486 (p 2122) (p 4477) (p 5789) (derived74063 p h) (h 11741)

theorem derived96487 (p : Nat → Prop) (h : Inputs p) :
    (p 4461) ∨ (¬ p 2088) :=
  ElevenRUP.step96487 (p 2088) (p 4461) (p 5786) (derived74059 p h) (h 11720)

theorem derived96490 (p : Nat → Prop) (h : Inputs p) :
    (p 4460) ∨ (¬ p 2088) :=
  ElevenRUP.step96490 (p 2088) (p 4460) (p 5786) (derived74059 p h) (h 11723)

theorem derived96509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5616) ∨ (p 4149) ∨ (p 2098) ∨ (¬ p 5369) ∨ (¬ p 2598) ∨ (¬ p 5682) :=
  ElevenRUP.step96509 (p 2098) (p 2104) (p 2598) (p 4149) (p 4286) (p 5369) (p 5616) (p 5682) (derived73548 p h) (derived73204 p h) (derived50430 p h)

theorem derived96513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5586) ∨ (p 2373) ∨ (¬ p 4506) ∨ (¬ p 2156) ∨ (¬ p 4109) :=
  ElevenRUP.step96513 (p 2156) (p 2373) (p 3737) (p 3880) (p 4109) (p 4506) (p 5586) (derived73490 p h) (derived60583 p h)

theorem derived96514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5586) ∨ (¬ p 4506) ∨ (p 2166) ∨ (¬ p 2192) :=
  ElevenRUP.step96514 (p 2166) (p 2191) (p 2192) (p 3737) (p 4506) (p 5586) (derived73222 p h) (derived64730 p h)

theorem derived96515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3914) ∨ (¬ p 5586) ∨ (¬ p 4197) ∨ (¬ p 2785) ∨ (¬ p 2363) ∨ (p 2088) :=
  ElevenRUP.step96515 (p 2088) (p 2363) (p 2785) (p 3857) (p 3914) (p 4197) (p 5586) (derived73480 p h) (derived56331 p h)

theorem derived96517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 5556) ∨ (p 2177) :=
  ElevenRUP.step96517 (p 2177) (p 2299) (p 3791) (p 5556) (derived73234 p h) (h 21839)

theorem derived96531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3801) ∨ (¬ p 4260) ∨ (¬ p 2177) ∨ (¬ p 5507) ∨ (p 2493) :=
  ElevenRUP.step96531 (p 2177) (p 2493) (p 2499) (p 3801) (p 4260) (p 5507) (derived73260 p h) (derived62060 p h)

theorem derived96537 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 5487) ∨ (¬ p 3767) :=
  ElevenRUP.step96537 (p 3707) (p 3767) (p 4321) (p 5487) (derived73554 p h) (h 39556)

theorem derived96543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5483) ∨ (p 3804) ∨ (p 3811) :=
  ElevenRUP.step96543 (p 3804) (p 3810) (p 3811) (p 3816) (p 5483) (derived73464 p h) (derived73466 p h) (h 9511)

theorem derived96544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5482) ∨ (p 5483) ∨ (¬ p 3794) :=
  ElevenRUP.step96544 (p 3794) (p 5479) (p 5482) (p 5483) (derived74042 p h) (h 9512)

theorem derived96547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 5477) ∨ (¬ p 4275) ∨ (¬ p 3246) ∨ (¬ p 4067) ∨ (p 2449) :=
  ElevenRUP.step96547 (p 2449) (p 3246) (p 3947) (p 4067) (p 4228) (p 4275) (p 5477) (derived73494 p h) (derived41538 p h)

theorem derived96548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4053) ∨ (p 3073) ∨ (¬ p 4371) ∨ (¬ p 5477) ∨ (¬ p 3325) ∨ (¬ p 2363) :=
  ElevenRUP.step96548 (p 2363) (p 3073) (p 3325) (p 4053) (p 4261) (p 4371) (p 5477) (derived73544 p h) (derived41676 p h)

theorem derived96550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3914) ∨ (¬ p 5477) ∨ (p 3527) ∨ (¬ p 2298) ∨ (¬ p 2264) ∨ (¬ p 4024) ∨ (¬ p 4105) :=
  ElevenRUP.step96550 (p 2264) (p 2298) (p 3527) (p 3548) (p 3914) (p 4024) (p 4105) (p 5477) (derived73404 p h) (derived58212 p h)

theorem derived96554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5475) ∨ (¬ p 5503) ∨ (¬ p 4276) ∨ (p 2274) :=
  ElevenRUP.step96554 (p 2274) (p 3097) (p 3737) (p 4276) (p 5475) (p 5503) (derived73352 p h) (derived41769 p h)

theorem derived96555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5514) ∨ (p 2573) ∨ (¬ p 5472) ∨ (¬ p 4710) ∨ (¬ p 3389) :=
  ElevenRUP.step96555 (p 2573) (p 2579) (p 3389) (p 4710) (p 5472) (p 5514) (derived73274 p h) (derived41904 p h)

theorem derived96568 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 5403) ∨ (¬ p 4952) ∨ (¬ p 5402) :=
  ElevenRUP.step96568 (p 3276) (p 4425) (p 4952) (p 5402) (p 5403) (derived73578 p h) (h 16281)

theorem derived96574 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (p 3276) ∨ (¬ p 5159) ∨ (¬ p 5682) ∨ (¬ p 5391) ∨ (¬ p 3367) :=
  ElevenRUP.step96574 (p 3276) (p 3367) (p 3599) (p 4379) (p 4425) (p 5159) (p 5391) (p 5682) (derived73572 p h) (derived73578 p h) (derived41967 p h)

theorem derived96576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3773) ∨ (¬ p 3461) ∨ (¬ p 2946) ∨ (¬ p 5378) ∨ (¬ p 2891) ∨ (¬ p 2255) ∨ (p 2641) ∨ (¬ p 3412) ∨ (¬ p 3246) ∨ (¬ p 2667) ∨ (¬ p 4625) :=
  ElevenRUP.step96576 (p 2255) (p 2641) (p 2667) (p 2891) (p 2946) (p 3246) (p 3412) (p 3461) (p 3773) (p 4154) (p 4625) (p 5378) (derived73526 p h) (derived48533 p h)

theorem derived96583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (p 3599) ∨ (¬ p 5352) ∨ (¬ p 4233) :=
  ElevenRUP.step96583 (p 2753) (p 3599) (p 4233) (p 4379) (p 5352) (derived73572 p h) (h 32776)

theorem derived96586 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 5332) ∨ (¬ p 3670) :=
  ElevenRUP.step96586 (p 3670) (p 3707) (p 4321) (p 5332) (p 5387) (derived73554 p h) (derived74025 p h) (h 26593)

theorem derived96592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3346) ∨ (p 2553) ∨ (¬ p 5321) ∨ (¬ p 2584) :=
  ElevenRUP.step96592 (p 2307) (p 2553) (p 2584) (p 2588) (p 3346) (p 5321) (derived73282 p h) (derived49495 p h)

theorem derived96597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3848) ∨ (¬ p 3297) ∨ (p 2996) ∨ (¬ p 2396) ∨ (¬ p 5295) :=
  ElevenRUP.step96597 (p 2396) (p 2996) (p 3027) (p 3297) (p 3848) (p 5295) (derived73340 p h) (derived72117 p h)

theorem derived96606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2797) ∨ (p 2696) ∨ (¬ p 3246) ∨ (¬ p 5257) ∨ (p 3323) ∨ (¬ p 4625) ∨ (p 2881) :=
  ElevenRUP.step96606 (p 2341) (p 2696) (p 2797) (p 2881) (p 3246) (p 3323) (p 3365) (p 3570) (p 4037) (p 4195) (p 4625) (p 5257) (derived73532 p h) (derived73390 p h) (derived73508 p h) (derived73418 p h) (derived53912 p h)

theorem derived96608 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (¬ p 2753) ∨ (p 3425) ∨ (¬ p 5234) :=
  ElevenRUP.step96608 (p 2753) (p 3425) (p 3471) (p 3599) (p 4379) (p 5234) (derived73572 p h) (derived73396 p h) (h 20394)

theorem derived96610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5233) ∨ (p 2707) ∨ (p 3246) ∨ (¬ p 4898) :=
  ElevenRUP.step96610 (p 2707) (p 3246) (p 3588) (p 3599) (p 3690) (p 4898) (p 5233) (derived73430 p h) (derived73446 p h) (derived50506 p h)

theorem derived96614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5229) ∨ (¬ p 2753) ∨ (¬ p 2717) ∨ (p 3599) ∨ (¬ p 4666) ∨ (p 3425) :=
  ElevenRUP.step96614 (p 2717) (p 2753) (p 3425) (p 3471) (p 3599) (p 4379) (p 4666) (p 5229) (derived73572 p h) (derived73396 p h) (derived48941 p h)

theorem derived96617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (p 2761) ∨ (¬ p 5229) :=
  ElevenRUP.step96617 (p 2761) (p 3670) (p 4381) (p 5229) (derived73574 p h) (h 20374)

theorem derived96622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5458) ∨ (p 2630) ∨ (¬ p 5177) ∨ (p 2737) :=
  ElevenRUP.step96622 (p 2630) (p 2737) (p 2743) (p 2810) (p 3599) (p 5177) (p 5458) (derived73316 p h) (derived73298 p h) (derived48435 p h)

theorem derived96625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (¬ p 3707) ∨ (¬ p 4953) ∨ (¬ p 3233) ∨ (p 2406) ∨ (¬ p 5175) :=
  ElevenRUP.step96625 (p 2406) (p 3233) (p 3238) (p 3707) (p 4953) (p 5175) (p 5284) (derived73374 p h) (derived41660 p h)

theorem derived96626 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5171) ∨ (¬ p 3355) ∨ (¬ p 2663) ∨ (p 3286) :=
  ElevenRUP.step96626 (p 2663) (p 3286) (p 3292) (p 3355) (p 5171) (derived73378 p h) (h 20255)

theorem derived96627 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 3286) ∨ (¬ p 2651) ∨ (¬ p 5171) ∨ (p 2727) :=
  ElevenRUP.step96627 (p 2651) (p 2727) (p 3276) (p 3286) (p 3292) (p 4111) (p 4425) (p 5171) (derived73578 p h) (derived73378 p h) (derived73518 p h) (derived43608 p h)

theorem derived96629 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3506) ∨ (¬ p 5171) :=
  ElevenRUP.step96629 (p 3276) (p 3506) (p 4425) (p 5171) (derived73578 p h) (h 20060)

theorem derived96634 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3670) ∨ (¬ p 5165) ∨ (¬ p 3193) ∨ (p 3422) :=
  ElevenRUP.step96634 (p 3193) (p 3276) (p 3422) (p 3584) (p 3670) (p 4425) (p 5165) (derived73578 p h) (derived73426 p h) (derived47021 p h)

theorem derived96635 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3670) ∨ (¬ p 3346) ∨ (¬ p 3905) ∨ (¬ p 3660) ∨ (p 3422) ∨ (¬ p 5165) :=
  ElevenRUP.step96635 (p 3276) (p 3346) (p 3422) (p 3584) (p 3660) (p 3670) (p 3905) (p 4425) (p 5165) (derived73578 p h) (derived73426 p h) (derived58816 p h)

theorem derived96640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3892) ∨ (¬ p 5133) ∨ (¬ p 2156) ∨ (p 2727) ∨ (p 2241) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 4521) :=
  ElevenRUP.step96640 (p 2156) (p 2241) (p 2247) (p 2727) (p 3125) (p 3461) (p 3892) (p 4111) (p 4521) (p 5133) (derived73518 p h) (derived73226 p h) (derived48161 p h)

theorem derived96647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5121) ∨ (p 3461) ∨ (¬ p 4330) ∨ (p 3146) :=
  ElevenRUP.step96647 (p 3146) (p 3461) (p 3692) (p 3969) (p 4191) (p 4330) (p 5121) (derived73530 p h) (derived73448 p h) (derived48255 p h)

theorem derived96648 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3670) ∨ (¬ p 5031) ∨ (¬ p 5357) ∨ (¬ p 4885) ∨ (p 2427) ∨ (¬ p 3571) :=
  ElevenRUP.step96648 (p 2427) (p 3571) (p 3670) (p 3707) (p 4235) (p 4321) (p 4885) (p 5031) (p 5357) (derived73554 p h) (derived73536 p h) (derived42522 p h)

theorem derived96651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 4322) ∨ (¬ p 4875) ∨ (¬ p 5031) ∨ (p 2972) :=
  ElevenRUP.step96651 (p 2972) (p 3670) (p 4322) (p 4363) (p 4875) (p 5031) (derived73568 p h) (derived54899 p h)

theorem derived96653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5030) ∨ (p 2982) ∨ (¬ p 4885) ∨ (p 2839) :=
  ElevenRUP.step96653 (p 2839) (p 2982) (p 3583) (p 3599) (p 4885) (p 4948) (p 5030) (derived73846 p h) (derived73424 p h) (derived42246 p h)

theorem derived96664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4590) ∨ (p 2264) ∨ (¬ p 4854) ∨ (¬ p 2088) ∨ (p 2459) :=
  ElevenRUP.step96664 (p 2088) (p 2264) (p 2459) (p 3553) (p 4348) (p 4590) (p 4854) (derived73410 p h) (derived73562 p h) (derived64379 p h)

theorem derived96665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4129) ∨ (¬ p 4830) ∨ (¬ p 4382) ∨ (p 2982) ∨ (¬ p 3698) ∨ (¬ p 2870) :=
  ElevenRUP.step96665 (p 2870) (p 2982) (p 3698) (p 4129) (p 4382) (p 4830) (p 4948) (derived73846 p h) (derived41429 p h)

theorem derived96667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4063) ∨ (p 3461) ∨ (¬ p 4621) ∨ (p 3516) ∨ (¬ p 4828) :=
  ElevenRUP.step96667 (p 3461) (p 3516) (p 3821) (p 4063) (p 4191) (p 4621) (p 4828) (derived73530 p h) (derived73470 p h) (derived49543 p h)

theorem derived96673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4793) ∨ (p 3399) ∨ (¬ p 3589) ∨ (¬ p 2598) ∨ (p 3367) :=
  ElevenRUP.step96673 (p 2598) (p 3367) (p 3399) (p 3585) (p 3589) (p 4366) (p 4793) (derived73570 p h) (derived73428 p h) (derived60037 p h)

theorem derived96675 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 4793) ∨ (¬ p 2741) ∨ (p 3399) :=
  ElevenRUP.step96675 (p 2253) (p 2651) (p 2727) (p 2741) (p 3399) (p 4111) (p 4366) (p 4793) (derived73518 p h) (derived73570 p h) (derived49575 p h)

theorem derived96676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (p 3266) ∨ (¬ p 4746) ∨ (¬ p 5344) ∨ (p 3146) :=
  ElevenRUP.step96676 (p 3146) (p 3266) (p 3670) (p 3692) (p 4444) (p 4746) (p 5344) (derived73580 p h) (derived73448 p h) (derived41210 p h)

theorem derived96679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (p 3073) ∨ (p 2470) ∨ (¬ p 4685) ∨ (¬ p 4695) :=
  ElevenRUP.step96679 (p 2470) (p 2476) (p 3073) (p 3355) (p 4261) (p 4685) (p 4695) (derived73544 p h) (derived73250 p h) (derived48031 p h)

theorem derived96680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4638) ∨ (¬ p 3343) ∨ (¬ p 2630) ∨ (¬ p 2696) ∨ (p 2396) ∨ (¬ p 4877) ∨ (¬ p 2753) ∨ (p 2156) ∨ (p 2274) ∨ (¬ p 3645) :=
  ElevenRUP.step96680 (p 2156) (p 2274) (p 2396) (p 2630) (p 2696) (p 2753) (p 3097) (p 3343) (p 3645) (p 3646) (p 4107) (p 4638) (p 4877) (derived73514 p h) (derived73436 p h) (derived73352 p h) (derived50794 p h)

theorem derived96681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3343) ∨ (p 3083) ∨ (¬ p 2663) ∨ (p 2774) ∨ (p 2122) ∨ (¬ p 4638) ∨ (¬ p 4786) ∨ (p 2396) :=
  ElevenRUP.step96681 (p 2122) (p 2396) (p 2470) (p 2663) (p 2774) (p 2780) (p 3083) (p 3343) (p 3822) (p 4107) (p 4256) (p 4638) (p 4786) (derived73542 p h) (derived73308 p h) (derived73472 p h) (derived73514 p h) (derived52170 p h)

theorem derived96682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 2088) ∨ (¬ p 4345) ∨ (¬ p 4614) ∨ (p 2352) :=
  ElevenRUP.step96682 (p 2088) (p 2352) (p 3564) (p 3857) (p 3956) (p 4345) (p 4614) (derived73480 p h) (derived73500 p h) (derived41421 p h)

theorem derived96683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 3256) ∨ (¬ p 4607) ∨ (¬ p 3146) ∨ (¬ p 4580) ∨ (¬ p 2655) ∨ (p 2230) ∨ (p 2122) ∨ (¬ p 4134) ∨ (¬ p 4346) ∨ (¬ p 2307) :=
  ElevenRUP.step96683 (p 2122) (p 2230) (p 2307) (p 2589) (p 2655) (p 2819) (p 3146) (p 3256) (p 3822) (p 4118) (p 4134) (p 4346) (p 4580) (p 4607) (derived73520 p h) (derived73284 p h) (derived73472 p h) (derived58480 p h)

theorem derived96685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2331) ∨ (¬ p 4104) ∨ (p 2264) ∨ (¬ p 4572) :=
  ElevenRUP.step96685 (p 2264) (p 2331) (p 2341) (p 2963) (p 3553) (p 4104) (p 4572) (derived73338 p h) (derived73410 p h) (derived53033 p h)

theorem derived96686 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 2088) ∨ (¬ p 4529) ∨ (¬ p 2532) ∨ (p 3156) :=
  ElevenRUP.step96686 (p 2088) (p 2532) (p 3115) (p 3156) (p 3497) (p 3857) (p 4529) (derived73480 p h) (derived73400 p h) (derived60831 p h)

theorem derived96687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3425) ∨ (¬ p 4472) ∨ (¬ p 2598) ∨ (p 3367) :=
  ElevenRUP.step96687 (p 2598) (p 2829) (p 3367) (p 3425) (p 3585) (p 4472) (derived73428 p h) (derived55696 p h)

theorem derived96688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3767) ∨ (¬ p 4456) ∨ (p 2761) ∨ (¬ p 3657) ∨ (¬ p 4905) ∨ (¬ p 3146) :=
  ElevenRUP.step96688 (p 2761) (p 3146) (p 3657) (p 3767) (p 4381) (p 4456) (p 4905) (derived73574 p h) (derived53279 p h)

theorem derived96689 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 4456) ∨ (¬ p 3297) ∨ (¬ p 3005) ∨ (¬ p 3146) ∨ (¬ p 5063) :=
  ElevenRUP.step96689 (p 3005) (p 3146) (p 3297) (p 3755) (p 4035) (p 4456) (p 5063) (derived73506 p h) (derived50550 p h)

theorem derived96691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3767) ∨ (¬ p 3322) ∨ (¬ p 3146) ∨ (¬ p 4134) ∨ (¬ p 4456) ∨ (p 3461) :=
  ElevenRUP.step96691 (p 3146) (p 3322) (p 3461) (p 3767) (p 4134) (p 4191) (p 4456) (derived73530 p h) (derived63025 p h)

theorem derived96693 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3767) ∨ (¬ p 3854) ∨ (¬ p 4439) ∨ (p 2241) :=
  ElevenRUP.step96693 (p 2241) (p 2247) (p 3707) (p 3767) (p 3854) (p 4321) (p 4439) (derived73554 p h) (derived73226 p h) (derived53841 p h)

theorem derived96696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (p 3093) ∨ (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 5254) ∨ (¬ p 2761) :=
  ElevenRUP.step96696 (p 2241) (p 2707) (p 2750) (p 2761) (p 3093) (p 3434) (p 3591) (p 4435) (p 5254) (derived73432 p h) (derived64558 p h)

theorem derived96697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 3914) ∨ (p 2819) ∨ (p 3093) :=
  ElevenRUP.step96697 (p 2819) (p 3093) (p 3591) (p 3914) (p 4358) (p 4435) (derived73564 p h) (derived73432 p h) (derived46726 p h)

theorem derived96699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 5472) ∨ (¬ p 4140) ∨ (¬ p 3569) ∨ (¬ p 2437) ∨ (¬ p 5016) ∨ (p 3016) ∨ (¬ p 2386) :=
  ElevenRUP.step96699 (p 2386) (p 2437) (p 3016) (p 3569) (p 3574) (p 4140) (p 4435) (p 5016) (p 5472) (derived73422 p h) (derived58001 p h)

theorem derived96700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 4228) ∨ (p 3093) ∨ (¬ p 3019) ∨ (¬ p 2440) :=
  ElevenRUP.step96700 (p 2440) (p 3019) (p 3093) (p 3591) (p 4228) (p 4435) (derived73432 p h) (derived65003 p h)

theorem derived96704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 4793) ∨ (¬ p 2608) ∨ (p 3093) ∨ (¬ p 5254) ∨ (¬ p 3146) ∨ (¬ p 4132) ∨ (¬ p 2341) ∨ (¬ p 3543) ∨ (¬ p 3266) :=
  ElevenRUP.step96704 (p 2341) (p 2608) (p 3093) (p 3146) (p 3266) (p 3543) (p 3591) (p 4132) (p 4435) (p 4793) (p 5254) (derived73432 p h) (derived63573 p h)

theorem derived96705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 2341) ∨ (p 3093) ∨ (¬ p 3519) ∨ (¬ p 5254) ∨ (¬ p 3266) ∨ (¬ p 4383) ∨ (¬ p 2608) ∨ (¬ p 4376) ∨ (¬ p 5201) ∨ (¬ p 2528) :=
  ElevenRUP.step96705 (p 2341) (p 2528) (p 2608) (p 3093) (p 3266) (p 3519) (p 3591) (p 4376) (p 4383) (p 4435) (p 5201) (p 5254) (derived73432 p h) (derived57349 p h)

theorem derived96708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4435) ∨ (¬ p 3914) ∨ (¬ p 4375) ∨ (¬ p 4644) ∨ (¬ p 4210) ∨ (¬ p 4512) ∨ (p 3201) :=
  ElevenRUP.step96708 (p 3201) (p 3876) (p 3914) (p 4210) (p 4375) (p 4435) (p 4512) (p 4644) (derived73486 p h) (derived63927 p h)

theorem derived96711 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (¬ p 4435) ∨ (p 3136) ∨ (¬ p 2957) ∨ (¬ p 3737) ∨ (¬ p 4512) ∨ (p 2274) :=
  ElevenRUP.step96711 (p 2274) (p 2957) (p 3097) (p 3136) (p 3370) (p 3737) (p 4315) (p 4435) (p 4512) (derived73550 p h) (derived73352 p h) (derived56756 p h)

theorem derived96712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4317) ∨ (¬ p 4435) ∨ (¬ p 5472) ∨ (¬ p 4140) ∨ (¬ p 4119) ∨ (¬ p 3073) ∨ (p 3146) :=
  ElevenRUP.step96712 (p 3073) (p 3146) (p 3692) (p 4119) (p 4140) (p 4317) (p 4435) (p 5472) (derived73448 p h) (derived41338 p h)

theorem derived96713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 4435) ∨ (¬ p 2249) ∨ (¬ p 3922) ∨ (p 2274) ∨ (¬ p 3276) ∨ (¬ p 3686) ∨ (¬ p 3333) ∨ (p 2996) ∨ (p 4325) ∨ (p 2331) :=
  ElevenRUP.step96713 (p 2249) (p 2274) (p 2331) (p 2963) (p 2996) (p 3027) (p 3097) (p 3276) (p 3333) (p 3686) (p 3737) (p 3922) (p 4325) (p 4435) (derived73352 p h) (derived73340 p h) (derived73338 p h) (derived52286 p h)

theorem derived96716 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3680) ∨ (¬ p 4387) :=
  ElevenRUP.step96716 (p 3680) (p 3707) (p 4321) (p 4387) (derived73554 p h) (h 20163)

theorem derived96718 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4387) ∨ (¬ p 3830) ∨ (¬ p 4632) ∨ (p 2210) ∨ (p 2982) :=
  ElevenRUP.step96718 (p 2210) (p 2982) (p 3555) (p 3830) (p 4387) (p 4632) (p 4948) (derived73412 p h) (derived73846 p h) (derived58766 p h)

theorem derived96721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4387) ∨ (¬ p 3830) ∨ (¬ p 4960) ∨ (p 3115) ∨ (p 2210) :=
  ElevenRUP.step96721 (p 2210) (p 3115) (p 3555) (p 3830) (p 4208) (p 4387) (p 4960) (derived73534 p h) (derived73412 p h) (derived62858 p h)

theorem derived96723 (p : Nat → Prop) (h : Inputs p) :
    (p 3105) ∨ (¬ p 5358) ∨ (¬ p 4387) ∨ (¬ p 2417) ∨ (¬ p 2870) ∨ (¬ p 4647) :=
  ElevenRUP.step96723 (p 2417) (p 2870) (p 3105) (p 4385) (p 4387) (p 4647) (p 5358) (derived73576 p h) (derived50619 p h)

theorem derived96724 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4116) ∨ (p 2992) ∨ (¬ p 2651) ∨ (¬ p 3680) ∨ (¬ p 2922) ∨ (¬ p 2255) ∨ (¬ p 3951) ∨ (¬ p 2417) ∨ (¬ p 3773) ∨ (¬ p 4380) ∨ (¬ p 2957) :=
  ElevenRUP.step96724 (p 2255) (p 2417) (p 2651) (p 2922) (p 2957) (p 2992) (p 3662) (p 3680) (p 3773) (p 3951) (p 4116) (p 4380) (derived73440 p h) (derived60190 p h)

theorem derived96730 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 4354) ∨ (¬ p 2598) :=
  ElevenRUP.step96730 (p 2098) (p 2104) (p 2598) (p 4354) (derived73204 p h) (h 6616)

theorem derived96732 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 4354) ∨ (¬ p 3367) :=
  ElevenRUP.step96732 (p 3367) (p 3537) (p 4242) (p 4354) (derived73538 p h) (h 33440)

theorem derived96739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (p 2774) ∨ (¬ p 4329) ∨ (p 3125) :=
  ElevenRUP.step96739 (p 2774) (p 2780) (p 3125) (p 3737) (p 3744) (p 4329) (derived73308 p h) (derived73454 p h) (derived46508 p h)

theorem derived96748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5299) ∨ (p 2417) ∨ (¬ p 3105) ∨ (¬ p 4323) ∨ (¬ p 4277) ∨ (p 2870) :=
  ElevenRUP.step96748 (p 2417) (p 2870) (p 3105) (p 4244) (p 4277) (p 4278) (p 4323) (p 5299) (derived73546 p h) (derived73540 p h) (derived41754 p h)

theorem derived96760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3773) ∨ (¬ p 4233) ∨ (¬ p 3670) :=
  ElevenRUP.step96760 (p 3670) (p 3773) (p 4233) (p 5387) (derived74025 p h) (h 32354)

theorem derived96763 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (¬ p 3670) ∨ (¬ p 4375) ∨ (¬ p 4231) ∨ (¬ p 3346) :=
  ElevenRUP.step96763 (p 3276) (p 3346) (p 3670) (p 4231) (p 4375) (p 4425) (derived73578 p h) (derived72121 p h)

theorem derived96772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4039) ∨ (¬ p 3755) ∨ (p 3136) ∨ (¬ p 2957) ∨ (¬ p 5046) ∨ (p 2156) :=
  ElevenRUP.step96772 (p 2156) (p 2957) (p 3136) (p 3646) (p 3755) (p 4039) (p 4315) (p 5046) (derived73550 p h) (derived73436 p h) (derived62079 p h)

theorem derived96781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3892) ∨ (¬ p 5127) ∨ (¬ p 4521) ∨ (¬ p 2156) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (p 2727) ∨ (p 2241) :=
  ElevenRUP.step96781 (p 2156) (p 2241) (p 2247) (p 2727) (p 3125) (p 3461) (p 3892) (p 4111) (p 4521) (p 5127) (derived73518 p h) (derived73226 p h) (derived48162 p h)

theorem derived96782 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2088) ∨ (¬ p 3858) :=
  ElevenRUP.step96782 (p 2088) (p 3073) (p 3857) (p 3858) (derived73480 p h) (h 5706)

theorem derived96785 (p : Nat → Prop) (h : Inputs p) :
    (p 3853) ∨ (¬ p 3852) :=
  ElevenRUP.step96785 (p 3852) (p 3853) (p 3856) (derived73477 p h) (h 5698)

theorem derived96786 (p : Nat → Prop) (h : Inputs p) :
    (p 3854) ∨ (¬ p 3852) :=
  ElevenRUP.step96786 (p 3852) (p 3854) (p 3856) (derived73477 p h) (h 5699)

theorem derived96788 (p : Nat → Prop) (h : Inputs p) :
    (p 3833) ∨ (¬ p 3852) :=
  ElevenRUP.step96788 (p 3833) (p 3852) (p 3856) (derived73477 p h) (h 5701)

theorem derived96789 (p : Nat → Prop) (h : Inputs p) :
    (p 3842) ∨ (¬ p 3852) :=
  ElevenRUP.step96789 (p 3842) (p 3852) (p 3856) (derived73477 p h) (h 5702)

theorem derived96793 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3853) ∨ (¬ p 3506) :=
  ElevenRUP.step96793 (p 3506) (p 3707) (p 3853) (p 4321) (derived73554 p h) (h 6542)

theorem derived96798 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (p 3707) ∨ (¬ p 3564) ∨ (¬ p 3853) ∨ (¬ p 2573) ∨ (¬ p 2249) ∨ (¬ p 3266) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 4330) :=
  ElevenRUP.step96798 (p 2249) (p 2573) (p 2656) (p 2727) (p 3266) (p 3286) (p 3292) (p 3564) (p 3707) (p 3853) (p 4321) (p 4330) (derived73378 p h) (derived73554 p h) (derived62914 p h)

theorem derived96803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3755) ∨ (p 3830) ∨ (¬ p 3847) ∨ (¬ p 2608) ∨ (p 3136) :=
  ElevenRUP.step96803 (p 2608) (p 3136) (p 3755) (p 3830) (p 3834) (p 3847) (p 4315) (derived73474 p h) (derived73550 p h) (derived59937 p h)

theorem derived96804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (p 2992) ∨ (¬ p 2957) ∨ (¬ p 3286) ∨ (p 3051) ∨ (p 3461) ∨ (¬ p 3847) ∨ (¬ p 2255) ∨ (p 3246) ∨ (¬ p 4621) :=
  ElevenRUP.step96804 (p 2255) (p 2957) (p 2992) (p 3051) (p 3246) (p 3286) (p 3461) (p 3556) (p 3662) (p 3690) (p 3707) (p 3847) (p 4191) (p 4621) (derived73440 p h) (derived73414 p h) (derived73530 p h) (derived73446 p h) (derived55721 p h)

theorem derived96805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (¬ p 3847) ∨ (¬ p 3707) :=
  ElevenRUP.step96805 (p 3707) (p 3847) (p 4321) (p 5284) (derived73553 p h) (h 29669)

theorem derived96806 (p : Nat → Prop) (h : Inputs p) :
    (p 3811) ∨ (p 5481) :=
  ElevenRUP.step96806 (p 3811) (p 3816) (p 5481) (derived73466 p h) (h 9507)

theorem derived96808 (p : Nat → Prop) (h : Inputs p) :
    (p 3804) ∨ (p 5480) :=
  ElevenRUP.step96808 (p 3804) (p 3810) (p 5480) (derived73464 p h) (h 9503)

theorem derived96809 (p : Nat → Prop) (h : Inputs p) :
    (p 3807) ∨ (¬ p 3804) :=
  ElevenRUP.step96809 (p 3804) (p 3807) (p 3810) (derived73463 p h) (h 5610)

theorem derived96819 (p : Nat → Prop) (h : Inputs p) :
    (p 3773) ∨ (¬ p 3770) :=
  ElevenRUP.step96819 (p 3770) (p 3773) (p 3776) (derived73457 p h) (h 5543)

theorem derived96826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (p 3399) ∨ (p 3527) ∨ (¬ p 2608) :=
  ElevenRUP.step96826 (p 2608) (p 3399) (p 3527) (p 3548) (p 3599) (p 4366) (derived73570 p h) (derived73404 p h) (derived47085 p h)

theorem derived96831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5453) ∨ (p 2737) :=
  ElevenRUP.step96831 (p 2737) (p 2743) (p 3599) (p 5453) (derived73298 p h) (h 19937)

theorem derived96834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (p 3146) ∨ (p 3537) ∨ (¬ p 5343) ∨ (¬ p 4746) :=
  ElevenRUP.step96834 (p 3146) (p 3537) (p 3599) (p 3692) (p 4242) (p 4746) (p 5343) (derived73448 p h) (derived73538 p h) (derived41212 p h)

theorem derived96835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 5343) ∨ (p 2459) ∨ (p 3537) ∨ (¬ p 4807) :=
  ElevenRUP.step96835 (p 2459) (p 3537) (p 3599) (p 4242) (p 4348) (p 4807) (p 5343) (derived73562 p h) (derived73538 p h) (derived42181 p h)

theorem derived96837 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 3853) ∨ (¬ p 3438) ∨ (¬ p 5063) ∨ (¬ p 3146) ∨ (¬ p 3166) :=
  ElevenRUP.step96837 (p 3146) (p 3166) (p 3286) (p 3292) (p 3438) (p 3853) (p 5063) (derived73378 p h) (derived53495 p h)

theorem derived96838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3438) ∨ (p 3266) ∨ (¬ p 3707) :=
  ElevenRUP.step96838 (p 3266) (p 3438) (p 3707) (p 4444) (derived73580 p h) (h 20151)

theorem derived96840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5152) ∨ (p 3654) ∨ (¬ p 4384) ∨ (¬ p 2383) ∨ (¬ p 3438) ∨ (¬ p 2528) :=
  ElevenRUP.step96840 (p 2383) (p 2528) (p 3438) (p 3654) (p 3946) (p 4384) (p 5152) (derived73492 p h) (derived57697 p h)

theorem derived96842 (p : Nat → Prop) (h : Inputs p) :
    (p 3297) ∨ (¬ p 3286) :=
  ElevenRUP.step96842 (p 3286) (p 3297) (p 3301) (derived73383 p h) (h 4721)

theorem derived96843 (p : Nat → Prop) (h : Inputs p) :
    (p 3298) ∨ (¬ p 3286) :=
  ElevenRUP.step96843 (p 3286) (p 3298) (p 3301) (derived73383 p h) (h 4722)

theorem derived96852 (p : Nat → Prop) (h : Inputs p) :
    (p 3232) ∨ (p 3193) :=
  ElevenRUP.step96852 (p 3193) (p 3232) (p 3236) (derived73371 p h) (h 4592)

theorem derived96853 (p : Nat → Prop) (h : Inputs p) :
    (p 3233) ∨ (p 3193) :=
  ElevenRUP.step96853 (p 3193) (p 3233) (p 3236) (derived73371 p h) (h 4593)

theorem derived96857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (¬ p 3232) ∨ (p 2241) ∨ (¬ p 3016) ∨ (p 3343) :=
  ElevenRUP.step96857 (p 2241) (p 2247) (p 3016) (p 3232) (p 3343) (p 3359) (p 3830) (derived73226 p h) (derived73388 p h) (derived45113 p h)

theorem derived96858 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 3830) ∨ (p 3343) ∨ (p 2440) ∨ (¬ p 3232) :=
  ElevenRUP.step96858 (p 2440) (p 2542) (p 3232) (p 3343) (p 3359) (p 3399) (p 3830) (p 4366) (derived73570 p h) (derived73388 p h) (derived73270 p h) (derived47287 p h)

theorem derived96864 (p : Nat → Prop) (h : Inputs p) :
    (p 3707) ∨ (¬ p 3232) ∨ (¬ p 4635) ∨ (¬ p 2761) ∨ (¬ p 4276) ∨ (¬ p 2396) :=
  ElevenRUP.step96864 (p 2396) (p 2761) (p 3232) (p 3707) (p 4276) (p 4321) (p 4635) (derived73554 p h) (derived48337 p h)

theorem derived96866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (p 3379) ∨ (¬ p 5217) ∨ (¬ p 3232) ∨ (¬ p 5160) :=
  ElevenRUP.step96866 (p 3232) (p 3379) (p 3452) (p 3830) (p 5160) (p 5217) (derived73394 p h) (derived51544 p h)

theorem derived96868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3229) ∨ (¬ p 3193) ∨ (p 3379) ∨ (¬ p 3830) :=
  ElevenRUP.step96868 (p 3193) (p 3229) (p 3379) (p 3452) (p 3830) (derived73394 p h) (derived65277 p h)

theorem derived96873 (p : Nat → Prop) (h : Inputs p) :
    (p 3178) ∨ (¬ p 3166) :=
  ElevenRUP.step96873 (p 3166) (p 3178) (p 3181) (derived73361 p h) (h 4480)

theorem derived96874 (p : Nat → Prop) (h : Inputs p) :
    (p 3180) ∨ (¬ p 3166) :=
  ElevenRUP.step96874 (p 3166) (p 3180) (p 3181) (derived73361 p h) (h 4481)

theorem derived96876 (p : Nat → Prop) (h : Inputs p) :
    (p 3177) ∨ (¬ p 3166) :=
  ElevenRUP.step96876 (p 3166) (p 3177) (p 3181) (derived73361 p h) (h 4483)

theorem derived96881 (p : Nat → Prop) (h : Inputs p) :
    (p 3037) ∨ (p 2996) :=
  ElevenRUP.step96881 (p 2996) (p 3037) (p 3041) (derived73347 p h) (h 4203)

theorem derived96882 (p : Nat → Prop) (h : Inputs p) :
    (p 3038) ∨ (p 2996) :=
  ElevenRUP.step96882 (p 2996) (p 3038) (p 3041) (derived73347 p h) (h 4204)

theorem derived96883 (p : Nat → Prop) (h : Inputs p) :
    (p 3040) ∨ (p 2996) :=
  ElevenRUP.step96883 (p 2996) (p 3040) (p 3041) (derived73347 p h) (h 4205)

theorem derived96884 (p : Nat → Prop) (h : Inputs p) :
    (p 3039) ∨ (p 2996) :=
  ElevenRUP.step96884 (p 2996) (p 3039) (p 3041) (derived73347 p h) (h 4207)

theorem derived96889 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (¬ p 3034) ∨ (p 3527) ∨ (¬ p 4378) ∨ (p 2807) :=
  ElevenRUP.step96889 (p 2807) (p 3034) (p 3166) (p 3414) (p 3527) (p 3548) (p 4378) (derived73404 p h) (derived73392 p h) (derived40989 p h)

theorem derived96892 (p : Nat → Prop) (h : Inputs p) :
    (p 2959) ∨ (¬ p 2946) :=
  ElevenRUP.step96892 (p 2946) (p 2959) (p 2961) (derived73335 p h) (h 4047)

theorem derived96894 (p : Nat → Prop) (h : Inputs p) :
    (p 2957) ∨ (¬ p 2946) :=
  ElevenRUP.step96894 (p 2946) (p 2957) (p 2961) (derived73335 p h) (h 4049)

theorem derived96895 (p : Nat → Prop) (h : Inputs p) :
    (p 2958) ∨ (¬ p 2946) :=
  ElevenRUP.step96895 (p 2946) (p 2958) (p 2961) (derived73335 p h) (h 4050)

theorem derived96899 (p : Nat → Prop) (h : Inputs p) :
    (p 2934) ∨ (¬ p 2922) :=
  ElevenRUP.step96899 (p 2922) (p 2934) (p 2937) (derived73325 p h) (h 3997)

theorem derived96901 (p : Nat → Prop) (h : Inputs p) :
    (p 2936) ∨ (¬ p 2922) :=
  ElevenRUP.step96901 (p 2922) (p 2936) (p 2937) (derived73325 p h) (h 3999)

theorem derived96902 (p : Nat → Prop) (h : Inputs p) :
    (p 2933) ∨ (¬ p 2922) :=
  ElevenRUP.step96902 (p 2922) (p 2933) (p 2937) (derived73325 p h) (h 4000)

theorem derived96908 (p : Nat → Prop) (h : Inputs p) :
    (p 2781) ∨ (p 2774) :=
  ElevenRUP.step96908 (p 2774) (p 2781) (p 2783) (derived73309 p h) (h 3687)

theorem derived96910 (p : Nat → Prop) (h : Inputs p) :
    (p 2778) ∨ (p 2774) :=
  ElevenRUP.step96910 (p 2774) (p 2778) (p 2783) (derived73309 p h) (h 3690)

theorem derived96911 (p : Nat → Prop) (h : Inputs p) :
    (p 2779) ∨ (p 2774) :=
  ElevenRUP.step96911 (p 2774) (p 2779) (p 2783) (derived73309 p h) (h 3691)

theorem derived96916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 5368) ∨ (p 2274) ∨ (¬ p 4384) ∨ (¬ p 2781) ∨ (¬ p 2187) ∨ (¬ p 2528) ∨ (p 2598) ∨ (p 3609) :=
  ElevenRUP.step96916 (p 2187) (p 2274) (p 2307) (p 2528) (p 2598) (p 2781) (p 3055) (p 3097) (p 3609) (p 4340) (p 4384) (p 5368) (derived73352 p h) (derived73350 p h) (derived73558 p h) (derived48890 p h)

theorem derived96917 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 2383) ∨ (p 2982) ∨ (p 2598) ∨ (¬ p 5059) ∨ (¬ p 3990) ∨ (¬ p 2781) ∨ (¬ p 3461) ∨ (p 2850) :=
  ElevenRUP.step96917 (p 2383) (p 2598) (p 2781) (p 2850) (p 2982) (p 3055) (p 3266) (p 3461) (p 3684) (p 3990) (p 4444) (p 4948) (p 5059) (derived73580 p h) (derived73846 p h) (derived73350 p h) (derived73442 p h) (derived41936 p h)

theorem derived96920 (p : Nat → Prop) (h : Inputs p) :
    (p 2744) ∨ (p 2737) :=
  ElevenRUP.step96920 (p 2737) (p 2744) (p 2746) (derived73299 p h) (h 3612)

theorem derived96922 (p : Nat → Prop) (h : Inputs p) :
    (p 2742) ∨ (p 2737) :=
  ElevenRUP.step96922 (p 2737) (p 2742) (p 2746) (derived73299 p h) (h 3614)

theorem derived96923 (p : Nat → Prop) (h : Inputs p) :
    (p 2741) ∨ (p 2737) :=
  ElevenRUP.step96923 (p 2737) (p 2741) (p 2746) (derived73299 p h) (h 3616)

theorem derived96927 (p : Nat → Prop) (h : Inputs p) :
    (p 2663) ∨ (¬ p 2651) :=
  ElevenRUP.step96927 (p 2651) (p 2663) (p 2666) (derived73293 p h) (h 3453)

theorem derived96928 (p : Nat → Prop) (h : Inputs p) :
    (p 2662) ∨ (¬ p 2651) :=
  ElevenRUP.step96928 (p 2651) (p 2662) (p 2666) (derived73293 p h) (h 3455)

theorem derived96934 (p : Nat → Prop) (h : Inputs p) :
    (p 2584) ∨ (¬ p 2573) :=
  ElevenRUP.step96934 (p 2573) (p 2584) (p 2587) (derived73279 p h) (h 3297)

theorem derived96935 (p : Nat → Prop) (h : Inputs p) :
    (p 2386) ∨ (¬ p 2573) :=
  ElevenRUP.step96935 (p 2386) (p 2573) (p 2587) (derived73279 p h) (h 3299)

theorem derived96943 (p : Nat → Prop) (h : Inputs p) :
    (p 2505) ∨ (¬ p 2493) :=
  ElevenRUP.step96943 (p 2493) (p 2505) (p 2508) (derived73265 p h) (h 3145)

theorem derived96944 (p : Nat → Prop) (h : Inputs p) :
    (p 2504) ∨ (¬ p 2493) :=
  ElevenRUP.step96944 (p 2493) (p 2504) (p 2508) (derived73265 p h) (h 3146)

theorem derived96945 (p : Nat → Prop) (h : Inputs p) :
    (p 2506) ∨ (¬ p 2493) :=
  ElevenRUP.step96945 (p 2493) (p 2506) (p 2508) (derived73265 p h) (h 3148)

theorem derived96946 (p : Nat → Prop) (h : Inputs p) :
    (p 2507) ∨ (¬ p 2493) :=
  ElevenRUP.step96946 (p 2493) (p 2507) (p 2508) (derived73265 p h) (h 3149)

theorem derived96954 (p : Nat → Prop) (h : Inputs p) :
    (p 2481) ∨ (¬ p 2470) :=
  ElevenRUP.step96954 (p 2470) (p 2481) (p 2485) (derived73255 p h) (h 3100)

theorem derived96955 (p : Nat → Prop) (h : Inputs p) :
    (p 2482) ∨ (¬ p 2470) :=
  ElevenRUP.step96955 (p 2470) (p 2482) (p 2485) (derived73255 p h) (h 3101)

theorem derived96962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2482) ∨ (p 3389) ∨ (p 2528) ∨ (¬ p 2088) :=
  ElevenRUP.step96962 (p 2088) (p 2437) (p 2482) (p 2528) (p 2534) (p 3389) (p 3540) (derived73402 p h) (derived73268 p h) (derived56441 p h)

theorem derived96966 (p : Nat → Prop) (h : Inputs p) :
    (p 2318) ∨ (¬ p 2307) :=
  ElevenRUP.step96966 (p 2307) (p 2318) (p 2322) (derived73243 p h) (h 2774)

theorem derived96969 (p : Nat → Prop) (h : Inputs p) :
    (p 2319) ∨ (¬ p 2307) :=
  ElevenRUP.step96969 (p 2307) (p 2319) (p 2322) (derived73243 p h) (h 2778)

theorem derived96975 (p : Nat → Prop) (h : Inputs p) :
    (p 2246) ∨ (p 2241) :=
  ElevenRUP.step96975 (p 2241) (p 2246) (p 2250) (derived73227 p h) (h 2630)

theorem derived96976 (p : Nat → Prop) (h : Inputs p) :
    (p 2245) ∨ (p 2241) :=
  ElevenRUP.step96976 (p 2241) (p 2245) (p 2250) (derived73227 p h) (h 2632)

theorem derived96981 (p : Nat → Prop) (h : Inputs p) :
    (p 2143) ∨ (¬ p 2132) :=
  ElevenRUP.step96981 (p 2132) (p 2143) (p 2147) (derived73219 p h) (h 2426)

theorem derived96982 (p : Nat → Prop) (h : Inputs p) :
    (p 2144) ∨ (¬ p 2132) :=
  ElevenRUP.step96982 (p 2132) (p 2144) (p 2147) (derived73219 p h) (h 2427)

theorem derived96983 (p : Nat → Prop) (h : Inputs p) :
    (p 2145) ∨ (¬ p 2132) :=
  ElevenRUP.step96983 (p 2132) (p 2145) (p 2147) (derived73219 p h) (h 2429)

theorem derived96988 (p : Nat → Prop) (h : Inputs p) :
    (p 2109) ∨ (¬ p 2098) :=
  ElevenRUP.step96988 (p 2098) (p 2109) (p 2113) (derived73209 p h) (h 2358)

theorem derived96989 (p : Nat → Prop) (h : Inputs p) :
    (p 2110) ∨ (¬ p 2098) :=
  ElevenRUP.step96989 (p 2098) (p 2110) (p 2113) (derived73209 p h) (h 2359)

theorem derived96990 (p : Nat → Prop) (h : Inputs p) :
    (p 2112) ∨ (¬ p 2098) :=
  ElevenRUP.step96990 (p 2098) (p 2112) (p 2113) (derived73209 p h) (h 2360)

theorem derived97000 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 4138) ∨ (¬ p 2363) :=
  ElevenRUP.step97000 (p 2363) (p 2459) (p 4138) (p 4347) (p 4348) (derived73562 p h) (derived73559 p h) (h 23467)

theorem derived97002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4441) ∨ (p 3146) ∨ (¬ p 2363) :=
  ElevenRUP.step97002 (p 2363) (p 3146) (p 3692) (p 4347) (p 4441) (derived73448 p h) (derived73559 p h) (h 27620)

theorem derived97015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2437) ∨ (¬ p 4186) :=
  ElevenRUP.step97015 (p 2437) (p 3083) (p 3742) (p 4186) (p 4256) (derived73541 p h) (derived73452 p h) (h 6402)

theorem derived97017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2470) ∨ (¬ p 2662) :=
  ElevenRUP.step97017 (p 2470) (p 2476) (p 2662) (p 3083) (p 4256) (derived73541 p h) (derived73250 p h) (h 27047)

theorem derived97019 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4344) ∨ (p 2717) ∨ (¬ p 2881) :=
  ElevenRUP.step97019 (p 2717) (p 2881) (p 3659) (p 4344) (derived73438 p h) (h 19748)

theorem derived97022 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3105) ∨ (¬ p 2881) ∨ (¬ p 4136) ∨ (¬ p 5104) :=
  ElevenRUP.step97022 (p 2717) (p 2881) (p 3105) (p 3659) (p 4136) (p 5104) (derived73438 p h) (derived57799 p h)

theorem derived97024 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3115) ∨ (p 2459) ∨ (¬ p 3425) ∨ (¬ p 2992) ∨ (¬ p 4450) ∨ (¬ p 2241) ∨ (¬ p 4736) :=
  ElevenRUP.step97024 (p 2241) (p 2459) (p 2717) (p 2992) (p 3115) (p 3425) (p 3659) (p 4348) (p 4450) (p 4736) (derived73438 p h) (derived73562 p h) (derived55712 p h)

theorem derived97026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (p 2829) ∨ (¬ p 2774) :=
  ElevenRUP.step97026 (p 2717) (p 2774) (p 2829) (p 3425) (p 3659) (p 3688) (derived73438 p h) (derived73444 p h) (derived43840 p h)

theorem derived97027 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3425) ∨ (¬ p 4119) ∨ (¬ p 4556) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 4736) ∨ (¬ p 2177) ∨ (¬ p 3379) :=
  ElevenRUP.step97027 (p 2177) (p 2373) (p 2406) (p 2717) (p 3379) (p 3425) (p 3659) (p 4119) (p 4556) (p 4736) (derived73438 p h) (derived49702 p h)

theorem derived97028 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3125) ∨ (¬ p 2210) ∨ (¬ p 2192) ∨ (¬ p 4736) ∨ (¬ p 3425) ∨ (¬ p 4330) ∨ (p 2459) :=
  ElevenRUP.step97028 (p 2192) (p 2210) (p 2459) (p 2717) (p 3125) (p 3425) (p 3659) (p 4330) (p 4348) (p 4736) (derived73438 p h) (derived73562 p h) (derived64061 p h)

theorem derived97030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2192) ∨ (¬ p 2911) ∨ (¬ p 4647) ∨ (¬ p 2156) ∨ (¬ p 3425) ∨ (p 2717) ∨ (¬ p 4736) ∨ (¬ p 4172) :=
  ElevenRUP.step97030 (p 2156) (p 2192) (p 2717) (p 2891) (p 2911) (p 3425) (p 3659) (p 4172) (p 4173) (p 4647) (p 4736) (derived73528 p h) (derived73438 p h) (derived49618 p h)

theorem derived97036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 3425) ∨ (p 2717) ∨ (¬ p 3379) ∨ (¬ p 2518) ∨ (¬ p 5122) ∨ (p 2459) ∨ (¬ p 4736) :=
  ElevenRUP.step97036 (p 2459) (p 2518) (p 2717) (p 3379) (p 3425) (p 3659) (p 4149) (p 4348) (p 4736) (p 5122) (derived73438 p h) (derived73562 p h) (derived54077 p h)

theorem derived97041 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2911) ∨ (¬ p 2437) ∨ (¬ p 3686) ∨ (¬ p 4750) :=
  ElevenRUP.step97041 (p 2437) (p 2717) (p 2911) (p 3659) (p 3686) (p 4750) (derived73438 p h) (derived49303 p h)

theorem derived97043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4403) ∨ (p 2088) ∨ (¬ p 3256) ∨ (¬ p 4044) ∨ (p 2717) ∨ (¬ p 4779) :=
  ElevenRUP.step97043 (p 2088) (p 2717) (p 3256) (p 3659) (p 3857) (p 4044) (p 4403) (p 4779) (derived73480 p h) (derived73438 p h) (derived41030 p h)

theorem derived97045 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (p 2761) ∨ (p 2717) ∨ (¬ p 5234) ∨ (¬ p 4668) :=
  ElevenRUP.step97045 (p 2717) (p 2761) (p 3659) (p 3670) (p 4381) (p 4668) (p 5234) (derived73574 p h) (derived73438 p h) (derived50530 p h)

theorem derived97047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 3461) ∨ (¬ p 5558) ∨ (p 2717) ∨ (¬ p 4200) ∨ (¬ p 3425) ∨ (¬ p 2331) ∨ (¬ p 4330) ∨ (¬ p 4786) ∨ (¬ p 4421) :=
  ElevenRUP.step97047 (p 2331) (p 2717) (p 3425) (p 3461) (p 3506) (p 3659) (p 4191) (p 4200) (p 4330) (p 4421) (p 4786) (p 5558) (derived73530 p h) (derived73438 p h) (derived56978 p h)

theorem derived97050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5558) ∨ (¬ p 5123) ∨ (¬ p 2331) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 3425) ∨ (p 2717) ∨ (¬ p 4786) :=
  ElevenRUP.step97050 (p 2331) (p 2717) (p 3323) (p 3425) (p 3461) (p 3659) (p 4786) (p 5123) (p 5558) (derived73438 p h) (derived42462 p h)

theorem derived97051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2717) ∨ (p 2440) ∨ (¬ p 5193) ∨ (p 2437) ∨ (p 2230) ∨ (¬ p 5083) ∨ (¬ p 3399) :=
  ElevenRUP.step97051 (p 2230) (p 2437) (p 2440) (p 2542) (p 2589) (p 2717) (p 3399) (p 3527) (p 3659) (p 3742) (p 5083) (p 5193) (derived73438 p h) (derived73270 p h) (derived73452 p h) (derived73284 p h) (derived41551 p h)

theorem derived97057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3687) ∨ (¬ p 3527) ∨ (¬ p 4897) ∨ (p 2717) ∨ (p 2839) :=
  ElevenRUP.step97057 (p 2717) (p 2839) (p 3527) (p 3583) (p 3659) (p 3687) (p 4897) (derived73438 p h) (derived73424 p h) (derived48453 p h)

theorem derived97058 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2608) ∨ (p 2717) ∨ (¬ p 3399) :=
  ElevenRUP.step97058 (p 2608) (p 2717) (p 3399) (p 3527) (p 3659) (p 3954) (derived73498 p h) (derived73438 p h) (derived45253 p h)

theorem derived97060 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2264) ∨ (¬ p 4117) ∨ (¬ p 2630) ∨ (¬ p 2807) :=
  ElevenRUP.step97060 (p 2264) (p 2630) (p 2717) (p 2807) (p 3553) (p 3659) (p 4117) (derived73438 p h) (derived73409 p h) (derived66986 p h)

theorem derived97061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (p 2717) ∨ (¬ p 4042) ∨ (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 3830) ∨ (¬ p 5123) ∨ (¬ p 4376) ∨ (¬ p 3707) ∨ (p 3379) :=
  ElevenRUP.step97061 (p 2717) (p 3366) (p 3379) (p 3425) (p 3452) (p 3659) (p 3707) (p 3830) (p 4042) (p 4376) (p 5123) (p 5568) (derived73438 p h) (derived73394 p h) (derived64946 p h)

end ElevenLogic
