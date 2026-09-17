import SunPrize.Certificate.Derived068
import SunPrize.Certificate.Logic069
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived120942 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3371) ∨ (¬ p 2166) ∨ (p 2737) :=
  ElevenRUP.step120942 (p 2166) (p 2619) (p 2737) (p 3371) (p 5052) (derived105473 p h) (derived84710 p h)

theorem derived120945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2608) ∨ (p 2619) ∨ (p 2839) ∨ (¬ p 3389) ∨ (p 2437) :=
  ElevenRUP.step120945 (p 2437) (p 2608) (p 2619) (p 2839) (p 3083) (p 3389) (p 4158) (p 5190) (derived105487 p h) (derived106187 p h) (derived84717 p h)

theorem derived120947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (p 2619) ∨ (¬ p 3256) ∨ (p 2608) ∨ (p 2363) ∨ (p 2839) :=
  ElevenRUP.step120947 (p 2248) (p 2363) (p 2608) (p 2619) (p 2839) (p 3166) (p 3256) (p 4134) (derived105365 p h) (derived105379 p h) (derived84730 p h)

theorem derived120952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 2307) ∨ (p 2619) ∨ (p 2132) ∨ (p 2553) ∨ (p 3146) ∨ (¬ p 2781) :=
  ElevenRUP.step120952 (p 2132) (p 2307) (p 2553) (p 2619) (p 2781) (p 3146) (p 3564) (p 4330) (derived106329 p h) (derived84741 p h)

theorem derived120954 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (p 2619) ∨ (¬ p 3830) ∨ (p 3146) ∨ (p 3461) ∨ (p 2132) :=
  ElevenRUP.step120954 (p 2132) (p 2619) (p 3146) (p 3461) (p 3707) (p 3830) (p 4330) (p 4736) (derived105431 p h) (derived106329 p h) (derived84749 p h)

theorem derived120956 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2528) ∨ (¬ p 2532) ∨ (¬ p 3105) :=
  ElevenRUP.step120956 (p 2528) (p 2532) (p 2619) (p 3105) (p 4158) (derived106187 p h) (derived84755 p h)

theorem derived120957 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3105) ∨ (p 3256) ∨ (¬ p 2532) :=
  ElevenRUP.step120957 (p 2532) (p 2619) (p 3105) (p 3256) (p 5063) (derived105474 p h) (derived84760 p h)

theorem derived120960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4355) ∨ (¬ p 2528) ∨ (p 2619) ∨ (p 3146) :=
  ElevenRUP.step120960 (p 2528) (p 2619) (p 3146) (p 4355) (p 4882) (derived105453 p h) (derived84768 p h)

theorem derived120963 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3645) ∨ (¬ p 3016) ∨ (p 3051) ∨ (¬ p 4506) ∨ (¬ p 2651) ∨ (¬ p 2246) ∨ (¬ p 2870) ∨ (¬ p 2553) ∨ (¬ p 4874) :=
  ElevenRUP.step120963 (p 2246) (p 2553) (p 2619) (p 2651) (p 2744) (p 2870) (p 3016) (p 3051) (p 3645) (p 4506) (p 4874) (derived106503 p h) (derived84776 p h)

theorem derived120965 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 2619) ∨ (¬ p 2331) ∨ (p 2608) ∨ (¬ p 2177) ∨ (¬ p 2295) :=
  ElevenRUP.step120965 (p 2177) (p 2248) (p 2295) (p 2331) (p 2608) (p 2619) (p 2839) (p 4905) (derived105365 p h) (derived105995 p h) (derived84778 p h)

theorem derived120966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 3366) ∨ (¬ p 3950) ∨ (¬ p 2396) ∨ (¬ p 3519) ∨ (p 3146) ∨ (¬ p 2573) :=
  ElevenRUP.step120966 (p 2132) (p 2396) (p 2553) (p 2573) (p 2619) (p 3146) (p 3366) (p 3519) (p 3950) (p 4376) (derived106320 p h) (derived84780 p h)

theorem derived120971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (p 3146) ∨ (p 2619) ∨ (p 2132) :=
  ElevenRUP.step120971 (p 2132) (p 2619) (p 2651) (p 3016) (p 3146) (p 3564) (p 4330) (p 4786) (derived106425 p h) (derived106329 p h) (derived84793 p h)

theorem derived120973 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2860) ∨ (p 2156) ∨ (¬ p 3166) ∨ (¬ p 2136) ∨ (p 2459) ∨ (¬ p 3256) :=
  ElevenRUP.step120973 (p 2136) (p 2156) (p 2459) (p 2619) (p 2860) (p 3166) (p 3256) (p 4786) (p 4905) (derived105995 p h) (derived106425 p h) (derived84797 p h)

theorem derived120977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3286) ∨ (p 2132) ∨ (p 2761) ∨ (p 2619) ∨ (p 3146) ∨ (¬ p 3950) :=
  ElevenRUP.step120977 (p 2132) (p 2619) (p 2761) (p 3146) (p 3286) (p 3506) (p 3950) (p 4786) (derived106425 p h) (derived84803 p h)

theorem derived120978 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2870) ∨ (p 2156) ∨ (¬ p 2220) :=
  ElevenRUP.step120978 (p 2156) (p 2220) (p 2619) (p 2870) (p 4558) (derived105400 p h) (derived84807 p h)

theorem derived120979 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 5568) ∨ (p 2132) ∨ (¬ p 2668) ∨ (¬ p 2331) ∨ (¬ p 2363) :=
  ElevenRUP.step120979 (p 2132) (p 2331) (p 2363) (p 2619) (p 2668) (p 4786) (p 5118) (p 5568) (derived106425 p h) (derived105482 p h) (derived84808 p h)

theorem derived120980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 4355) ∨ (p 2619) ∨ (¬ p 5568) :=
  ElevenRUP.step120980 (p 2619) (p 4149) (p 4355) (p 4882) (p 5568) (derived105453 p h) (derived84810 p h)

theorem derived120981 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 2331) ∨ (p 2132) ∨ (p 2619) ∨ (¬ p 5123) :=
  ElevenRUP.step120981 (p 2132) (p 2331) (p 2619) (p 3323) (p 3461) (p 4786) (p 5123) (p 5568) (derived106425 p h) (derived84811 p h)

theorem derived120982 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2563) ∨ (¬ p 2870) ∨ (¬ p 2373) :=
  ElevenRUP.step120982 (p 2373) (p 2563) (p 2619) (p 2870) (p 4558) (derived105400 p h) (derived84819 p h)

theorem derived120984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3519) ∨ (¬ p 3461) ∨ (¬ p 5568) ∨ (¬ p 3564) ∨ (¬ p 3366) ∨ (p 2619) ∨ (p 2132) ∨ (¬ p 5123) :=
  ElevenRUP.step120984 (p 2132) (p 2573) (p 2619) (p 3366) (p 3461) (p 3519) (p 3564) (p 4376) (p 5123) (p 5568) (derived106320 p h) (derived84823 p h)

theorem derived120985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4392) ∨ (p 2619) ∨ (¬ p 2992) ∨ (¬ p 3156) :=
  ElevenRUP.step120985 (p 2619) (p 2751) (p 2992) (p 3156) (p 4392) (derived106343 p h) (derived84824 p h)

theorem derived120988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 2132) ∨ (¬ p 2363) ∨ (¬ p 2352) ∨ (p 2619) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 5568) :=
  ElevenRUP.step120988 (p 2132) (p 2352) (p 2363) (p 2573) (p 2619) (p 3366) (p 3519) (p 4376) (p 5118) (p 5568) (derived106320 p h) (derived105482 p h) (derived84832 p h)

theorem derived120989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (¬ p 5568) ∨ (p 2619) ∨ (¬ p 5123) ∨ (¬ p 3366) ∨ (¬ p 3830) ∨ (p 2132) ∨ (p 3379) :=
  ElevenRUP.step120989 (p 2132) (p 2619) (p 3366) (p 3379) (p 3707) (p 3830) (p 4376) (p 5123) (p 5568) (derived106320 p h) (derived84833 p h)

theorem derived120991 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 2619) ∨ (¬ p 2220) ∨ (¬ p 2284) :=
  ElevenRUP.step120991 (p 2156) (p 2220) (p 2284) (p 2619) (p 4906) (derived105632 p h) (derived84842 p h)

theorem derived120996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2132) ∨ (p 2870) ∨ (¬ p 4185) :=
  ElevenRUP.step120996 (p 2132) (p 2774) (p 2870) (p 4185) (p 4555) (derived105542 p h) (derived84868 p h)

theorem derived120997 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 3051) ∨ (¬ p 4185) ∨ (¬ p 2143) ∨ (p 2839) :=
  ElevenRUP.step120997 (p 2143) (p 2829) (p 2839) (p 3051) (p 4185) (p 4555) (derived105542 p h) (derived84872 p h)

theorem derived120999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2449) ∨ (p 2156) ∨ (¬ p 5123) ∨ (p 2187) ∨ (¬ p 3580) ∨ (¬ p 2753) ∨ (¬ p 4117) ∨ (¬ p 3645) ∨ (¬ p 2651) ∨ (¬ p 5580) :=
  ElevenRUP.step120999 (p 2156) (p 2187) (p 2449) (p 2651) (p 2753) (p 2761) (p 3580) (p 3645) (p 4117) (p 4877) (p 5123) (p 5580) (derived105451 p h) (derived84893 p h)

theorem derived121002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (¬ p 3519) ∨ (¬ p 3246) ∨ (¬ p 3051) ∨ (p 2331) ∨ (¬ p 3366) ∨ (p 2668) ∨ (¬ p 2761) ∨ (¬ p 5580) ∨ (¬ p 4399) ∨ (¬ p 5123) :=
  ElevenRUP.step121002 (p 2331) (p 2668) (p 2761) (p 3051) (p 3246) (p 3366) (p 3519) (p 4236) (p 4376) (p 4399) (p 5123) (p 5580) (derived106320 p h) (derived84897 p h)

theorem derived121004 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5580) ∨ (¬ p 2190) ∨ (p 2274) :=
  ElevenRUP.step121004 (p 2190) (p 2274) (p 3969) (p 4405) (p 5580) (derived105512 p h) (derived84901 p h)

theorem derived121005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 5580) ∨ (¬ p 2528) ∨ (p 2352) :=
  ElevenRUP.step121005 (p 2352) (p 2528) (p 3564) (p 5118) (p 5580) (derived105482 p h) (derived84903 p h)

theorem derived121008 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3115) ∨ (¬ p 2946) ∨ (¬ p 5580) ∨ (p 2774) ∨ (p 2819) ∨ (¬ p 5123) :=
  ElevenRUP.step121008 (p 2774) (p 2819) (p 2946) (p 3115) (p 3680) (p 4786) (p 5123) (p 5580) (derived106425 p h) (derived84912 p h)

theorem derived121013 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 5580) ∨ (p 2241) ∨ (p 2829) ∨ (p 2819) ∨ (¬ p 3073) :=
  ElevenRUP.step121013 (p 2241) (p 2744) (p 2819) (p 2829) (p 3073) (p 3449) (p 5118) (p 5580) (derived106503 p h) (derived105482 p h) (derived84921 p h)

theorem derived121014 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 5580) ∨ (p 2187) ∨ (¬ p 2136) ∨ (p 2156) ∨ (¬ p 3366) ∨ (¬ p 3073) ∨ (p 2241) :=
  ElevenRUP.step121014 (p 2136) (p 2156) (p 2187) (p 2241) (p 2744) (p 3073) (p 3366) (p 3449) (p 5118) (p 5580) (derived106503 p h) (derived105482 p h) (derived84922 p h)

theorem derived121016 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (¬ p 5580) ∨ (p 2668) ∨ (p 2331) ∨ (¬ p 2252) ∨ (¬ p 3830) ∨ (p 2608) ∨ (¬ p 5123) :=
  ElevenRUP.step121016 (p 2252) (p 2331) (p 2608) (p 2668) (p 2750) (p 3707) (p 3830) (p 5123) (p 5580) (derived106345 p h) (derived84925 p h)

theorem derived121020 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3343) ∨ (¬ p 5580) ∨ (p 2819) ∨ (¬ p 2651) ∨ (p 2774) ∨ (¬ p 5123) :=
  ElevenRUP.step121020 (p 2651) (p 2774) (p 2819) (p 3276) (p 3343) (p 4786) (p 5123) (p 5580) (derived106425 p h) (derived84929 p h)

theorem derived121022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 5580) ∨ (¬ p 4149) ∨ (p 2553) :=
  ElevenRUP.step121022 (p 2510) (p 2553) (p 4149) (p 4405) (p 5580) (derived105512 p h) (derived84935 p h)

theorem derived121023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (p 2331) ∨ (¬ p 4399) ∨ (¬ p 5580) ∨ (¬ p 3922) ∨ (¬ p 2727) ∨ (¬ p 3923) ∨ (¬ p 2656) ∨ (¬ p 3680) ∨ (¬ p 5123) :=
  ElevenRUP.step121023 (p 2249) (p 2331) (p 2656) (p 2727) (p 3212) (p 3680) (p 3922) (p 3923) (p 4399) (p 5123) (p 5580) (derived106513 p h) (derived84945 p h)

theorem derived121024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3755) ∨ (p 2156) ∨ (¬ p 5580) ∨ (p 2187) ∨ (¬ p 2696) ∨ (¬ p 3645) ∨ (¬ p 2753) ∨ (¬ p 5123) :=
  ElevenRUP.step121024 (p 2156) (p 2187) (p 2696) (p 2753) (p 3506) (p 3645) (p 3755) (p 4877) (p 5123) (p 5580) (derived105451 p h) (derived84947 p h)

theorem derived121027 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 3987) :=
  ElevenRUP.step121027 (p 2383) (p 2668) (p 2946) (p 3987) (p 4566) (derived106307 p h) (derived84976 p h)

theorem derived121028 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2383) ∨ (¬ p 3987) ∨ (p 2668) :=
  ElevenRUP.step121028 (p 2383) (p 2668) (p 2797) (p 3987) (p 4790) (derived106424 p h) (derived84982 p h)

theorem derived121035 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 3527) ∨ (p 2553) ∨ (¬ p 4431) ∨ (p 2598) ∨ (¬ p 2210) ∨ (p 2881) :=
  ElevenRUP.step121035 (p 2210) (p 2553) (p 2598) (p 2881) (p 3422) (p 3527) (p 4431) (p 4556) (p 4736) (derived105431 p h) (derived105399 p h) (derived85069 p h)

theorem derived121037 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2696) ∨ (p 2881) ∨ (¬ p 3399) ∨ (p 2295) ∨ (¬ p 3527) :=
  ElevenRUP.step121037 (p 2295) (p 2696) (p 2797) (p 2881) (p 3399) (p 3527) (p 4556) (p 4736) (derived105431 p h) (derived105399 p h) (derived85077 p h)

theorem derived121041 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3527) ∨ (¬ p 4344) ∨ (p 2427) ∨ (¬ p 4431) ∨ (¬ p 3959) :=
  ElevenRUP.step121041 (p 2341) (p 2427) (p 3527) (p 3959) (p 4344) (p 4431) (p 4632) (derived106257 p h) (derived85086 p h)

theorem derived121042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 3645) ∨ (p 2608) ∨ (p 2156) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2274) ∨ (p 2396) ∨ (p 2911) :=
  ElevenRUP.step121042 (p 2156) (p 2274) (p 2396) (p 2441) (p 2608) (p 2911) (p 3399) (p 3527) (p 3645) (p 4877) (derived105451 p h) (derived85090 p h)

theorem derived121045 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3136) ∨ (p 2685) ∨ (¬ p 3399) ∨ (p 2177) ∨ (¬ p 3527) :=
  ElevenRUP.step121045 (p 2177) (p 2254) (p 2685) (p 2946) (p 3136) (p 3399) (p 3527) (p 4361) (derived105366 p h) (derived105382 p h) (derived85099 p h)

theorem derived121048 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 2946) ∨ (p 2274) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2284) ∨ (¬ p 4473) :=
  ElevenRUP.step121048 (p 2254) (p 2274) (p 2284) (p 2717) (p 2946) (p 3399) (p 3527) (p 4473) (derived105366 p h) (derived85123 p h)

theorem derived121059 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3309) ∨ (p 2295) ∨ (¬ p 4759) :=
  ElevenRUP.step121059 (p 2295) (p 2751) (p 2797) (p 3309) (p 4759) (derived106343 p h) (derived85159 p h)

theorem derived121062 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 3950) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (p 3256) ∨ (¬ p 2396) ∨ (p 2696) :=
  ElevenRUP.step121062 (p 2396) (p 2696) (p 3005) (p 3093) (p 3256) (p 3309) (p 3950) (p 4736) (derived105431 p h) (derived85175 p h)

theorem derived121065 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (p 2685) ∨ (¬ p 3093) ∨ (p 2449) ∨ (¬ p 2177) ∨ (¬ p 3309) :=
  ElevenRUP.step121065 (p 2177) (p 2449) (p 2685) (p 2696) (p 3093) (p 3309) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived85191 p h)

theorem derived121069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3361) ∨ (¬ p 3983) ∨ (¬ p 3309) ∨ (p 3367) ∨ (¬ p 4869) ∨ (p 2307) :=
  ElevenRUP.step121069 (p 2307) (p 3309) (p 3361) (p 3367) (p 3983) (p 4749) (p 4869) (derived105432 p h) (derived85201 p h)

theorem derived121071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3105) ∨ (p 2132) ∨ (p 3276) ∨ (¬ p 3309) ∨ (¬ p 4952) ∨ (¬ p 3093) :=
  ElevenRUP.step121071 (p 2132) (p 3093) (p 3105) (p 3276) (p 3309) (p 3791) (p 4736) (p 4826) (p 4952) (derived105431 p h) (derived105444 p h) (derived85213 p h)

theorem derived121073 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 3309) ∨ (p 2295) ∨ (¬ p 4759) :=
  ElevenRUP.step121073 (p 2295) (p 2727) (p 3309) (p 4759) (p 4975) (derived105464 p h) (derived85224 p h)

theorem derived121076 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2406) ∨ (p 2307) ∨ (¬ p 2386) ∨ (¬ p 2505) :=
  ElevenRUP.step121076 (p 2307) (p 2386) (p 2406) (p 2505) (p 3309) (p 4717) (derived105424 p h) (derived85232 p h)

theorem derived121078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 5015) ∨ (¬ p 3309) ∨ (¬ p 2373) ∨ (p 2307) ∨ (¬ p 3923) ∨ (¬ p 2850) :=
  ElevenRUP.step121078 (p 2307) (p 2373) (p 2598) (p 2850) (p 3309) (p 3923) (p 4433) (p 4733) (p 5015) (derived105430 p h) (derived106150 p h) (derived85245 p h)

theorem derived121079 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3093) ∨ (p 3083) ∨ (p 2651) ∨ (p 2528) ∨ (¬ p 2396) ∨ (¬ p 3950) :=
  ElevenRUP.step121079 (p 2254) (p 2396) (p 2528) (p 2651) (p 3083) (p 3093) (p 3309) (p 3950) (derived105366 p h) (derived85255 p h)

theorem derived121082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2474) ∨ (¬ p 4319) ∨ (¬ p 4438) ∨ (¬ p 2528) ∨ (p 2727) ∨ (p 2088) ∨ (¬ p 2662) ∨ (¬ p 2331) ∨ (¬ p 3309) ∨ (¬ p 2177) :=
  ElevenRUP.step121082 (p 2088) (p 2177) (p 2255) (p 2331) (p 2474) (p 2528) (p 2662) (p 2727) (p 3309) (p 4319) (p 4438) (derived105367 p h) (derived85261 p h)

theorem derived121087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 2608) ∨ (p 2307) ∨ (¬ p 5015) :=
  ElevenRUP.step121087 (p 2307) (p 2608) (p 3309) (p 4866) (p 5015) (derived106063 p h) (derived85272 p h)

theorem derived121088 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3309) ∨ (p 3166) ∨ (¬ p 2177) ∨ (¬ p 3093) ∨ (¬ p 3146) :=
  ElevenRUP.step121088 (p 2177) (p 2254) (p 3093) (p 3146) (p 3166) (p 3256) (p 3309) (p 4905) (derived105366 p h) (derived105995 p h) (derived85276 p h)

theorem derived121094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 3309) ∨ (¬ p 2341) ∨ (¬ p 4067) ∨ (p 2264) :=
  ElevenRUP.step121094 (p 2264) (p 2312) (p 2341) (p 3309) (p 4067) (p 4761) (derived106234 p h) (derived85298 p h)

theorem derived121095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (p 2331) ∨ (¬ p 3093) ∨ (p 2274) ∨ (¬ p 2797) ∨ (p 2630) ∨ (p 3379) ∨ (¬ p 3309) ∨ (¬ p 3366) :=
  ElevenRUP.step121095 (p 2274) (p 2331) (p 2630) (p 2797) (p 3093) (p 3309) (p 3366) (p 3379) (p 4236) (p 4376) (derived106320 p h) (derived85300 p h)

theorem derived121096 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2850) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2177) ∨ (p 2230) ∨ (¬ p 4438) :=
  ElevenRUP.step121096 (p 2177) (p 2230) (p 2850) (p 3093) (p 3309) (p 3641) (p 4438) (p 5193) (derived105488 p h) (derived85306 p h)

theorem derived121097 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4138) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 2341) :=
  ElevenRUP.step121097 (p 2321) (p 2341) (p 3309) (p 3923) (p 4138) (derived105369 p h) (derived48375 p h)

theorem derived121099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (p 3051) ∨ (¬ p 3309) ∨ (¬ p 4319) ∨ (¬ p 2177) ∨ (¬ p 2331) ∨ (p 2992) ∨ (p 3246) :=
  ElevenRUP.step121099 (p 2177) (p 2255) (p 2331) (p 2957) (p 2992) (p 3051) (p 3246) (p 3309) (p 4319) (p 4666) (derived105367 p h) (derived105658 p h) (derived85310 p h)

theorem derived121100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (¬ p 3309) ∨ (¬ p 2881) ∨ (¬ p 4113) ∨ (¬ p 3960) :=
  ElevenRUP.step121100 (p 2881) (p 3309) (p 3923) (p 3960) (p 4113) (p 4559) (derived105701 p h) (derived41876 p h)

theorem derived121101 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 2598) ∨ (p 2528) ∨ (¬ p 2396) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3950) :=
  ElevenRUP.step121101 (p 2396) (p 2528) (p 2598) (p 3093) (p 3309) (p 3641) (p 3950) (p 4736) (derived105431 p h) (derived85316 p h)

theorem derived121103 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2685) ∨ (¬ p 3366) ∨ (¬ p 3093) ∨ (¬ p 4769) ∨ (¬ p 3309) ∨ (p 2807) ∨ (¬ p 4236) ∨ (p 3379) :=
  ElevenRUP.step121103 (p 2685) (p 2807) (p 3005) (p 3093) (p 3309) (p 3366) (p 3379) (p 4236) (p 4376) (p 4769) (derived106320 p h) (derived85327 p h)

theorem derived121105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 3309) ∨ (p 2307) ∨ (¬ p 2505) ∨ (p 3016) :=
  ElevenRUP.step121105 (p 2307) (p 2386) (p 2505) (p 3016) (p 3309) (p 4814) (derived105440 p h) (derived85328 p h)

theorem derived121106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 3346) ∨ (p 2727) ∨ (¬ p 2331) ∨ (¬ p 2662) ∨ (¬ p 3309) ∨ (p 3276) ∨ (¬ p 4319) :=
  ElevenRUP.step121106 (p 2255) (p 2331) (p 2662) (p 2727) (p 3276) (p 3309) (p 3346) (p 3791) (p 4319) (p 4826) (derived105367 p h) (derived105444 p h) (derived85331 p h)

theorem derived121110 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (p 3201) ∨ (¬ p 2396) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (p 2911) :=
  ElevenRUP.step121110 (p 2396) (p 2598) (p 2911) (p 3093) (p 3201) (p 3309) (p 4668) (p 4736) (derived105431 p h) (derived105414 p h) (derived85345 p h)

theorem derived121111 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (¬ p 3309) ∨ (p 2850) ∨ (¬ p 3093) ∨ (p 2982) ∨ (¬ p 2396) :=
  ElevenRUP.step121111 (p 2396) (p 2598) (p 2850) (p 2982) (p 3093) (p 3309) (p 3951) (p 4736) (derived105431 p h) (derived106536 p h) (derived85346 p h)

theorem derived121112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (¬ p 3309) ∨ (¬ p 2383) ∨ (p 2598) ∨ (p 2850) ∨ (p 2427) ∨ (¬ p 5020) :=
  ElevenRUP.step121112 (p 2383) (p 2427) (p 2598) (p 2850) (p 3309) (p 3923) (p 4559) (p 4736) (p 5020) (derived105431 p h) (derived105701 p h) (derived85348 p h)

theorem derived121113 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2417) ∨ (p 2598) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 2177) :=
  ElevenRUP.step121113 (p 2177) (p 2417) (p 2598) (p 3093) (p 3201) (p 3309) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived85349 p h)

theorem derived121118 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3609) ∨ (¬ p 2528) ∨ (¬ p 3093) ∨ (¬ p 2177) ∨ (¬ p 3309) ∨ (¬ p 4438) :=
  ElevenRUP.step121118 (p 2098) (p 2177) (p 2528) (p 3093) (p 3309) (p 3609) (p 4438) (p 4736) (derived105431 p h) (derived85361 p h)

theorem derived121119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5015) ∨ (¬ p 2608) ∨ (¬ p 2505) ∨ (p 2307) ∨ (¬ p 3309) :=
  ElevenRUP.step121119 (p 2307) (p 2505) (p 2608) (p 3309) (p 4376) (p 5015) (derived106320 p h) (derived85366 p h)

theorem derived121120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (p 2553) ∨ (¬ p 4140) :=
  ElevenRUP.step121120 (p 2156) (p 2553) (p 3051) (p 3958) (p 4140) (derived105378 p h) (derived85385 p h)

theorem derived121121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3645) ∨ (p 2156) ∨ (p 2608) ∨ (p 2396) ∨ (¬ p 3037) ∨ (p 2274) ∨ (¬ p 3399) ∨ (¬ p 2264) :=
  ElevenRUP.step121121 (p 2156) (p 2264) (p 2274) (p 2396) (p 2608) (p 3037) (p 3399) (p 3645) (p 4666) (p 4877) (derived105658 p h) (derived105451 p h) (derived85388 p h)

theorem derived121122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (p 2156) ∨ (p 3246) ∨ (¬ p 3516) :=
  ElevenRUP.step121122 (p 2156) (p 3246) (p 3516) (p 4558) (p 4988) (derived105400 p h) (derived85390 p h)

theorem derived121123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4119) ∨ (¬ p 4140) ∨ (p 2553) ∨ (¬ p 2220) ∨ (p 2156) :=
  ElevenRUP.step121123 (p 2156) (p 2220) (p 2553) (p 3958) (p 4119) (p 4140) (derived105378 p h) (derived85394 p h)

theorem derived121127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 2156) ∨ (¬ p 3660) ∨ (p 2187) :=
  ElevenRUP.step121127 (p 2156) (p 2187) (p 2352) (p 3660) (p 4533) (derived105394 p h) (derived85406 p h)

theorem derived121132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5045) ∨ (¬ p 3212) ∨ (p 2274) ∨ (p 2156) :=
  ElevenRUP.step121132 (p 2156) (p 2274) (p 3212) (p 4624) (p 5045) (derived105408 p h) (derived85438 p h)

theorem derived121133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (p 2373) ∨ (¬ p 2284) :=
  ElevenRUP.step121133 (p 2156) (p 2220) (p 2284) (p 2373) (p 4705) (derived106238 p h) (derived85443 p h)

theorem derived121136 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 3904) ∨ (¬ p 3389) ∨ (¬ p 2563) :=
  ElevenRUP.step121136 (p 2156) (p 2563) (p 3389) (p 3904) (p 4646) (derived105534 p h) (derived85449 p h)

theorem derived121139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (p 2156) ∨ (p 2881) ∨ (¬ p 2341) :=
  ElevenRUP.step121139 (p 2156) (p 2341) (p 2881) (p 4558) (p 4988) (derived105400 p h) (derived85470 p h)

theorem derived121145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (¬ p 2098) ∨ (¬ p 2950) ∨ (p 3461) ∨ (p 2598) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (p 2156) ∨ (p 3125) ∨ (¬ p 5119) :=
  ElevenRUP.step121145 (p 2098) (p 2156) (p 2252) (p 2598) (p 2748) (p 2950) (p 3125) (p 3461) (p 4019) (p 4749) (p 5119) (derived105432 p h) (derived85504 p h)

theorem derived121147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 2156) ∨ (p 2901) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2911) ∨ (¬ p 2284) :=
  ElevenRUP.step121147 (p 2156) (p 2254) (p 2284) (p 2901) (p 2911) (p 2950) (p 3399) (p 3527) (p 4277) (derived105366 p h) (derived105380 p h) (derived85516 p h)

theorem derived121148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2156) ∨ (¬ p 2608) ∨ (¬ p 2284) ∨ (¬ p 2717) ∨ (p 3156) ∨ (¬ p 2950) :=
  ElevenRUP.step121148 (p 2156) (p 2254) (p 2284) (p 2608) (p 2707) (p 2717) (p 2950) (p 3156) (p 4905) (derived105366 p h) (derived105995 p h) (derived85517 p h)

theorem derived121149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 2156) ∨ (¬ p 2807) ∨ (¬ p 3413) ∨ (¬ p 2284) :=
  ElevenRUP.step121149 (p 2156) (p 2284) (p 2807) (p 2950) (p 3413) (p 4652) (derived105413 p h) (derived85518 p h)

theorem derived121152 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 3413) ∨ (¬ p 2284) ∨ (¬ p 2911) ∨ (p 2440) ∨ (¬ p 3016) ∨ (p 2156) ∨ (¬ p 3872) ∨ (¬ p 2659) :=
  ElevenRUP.step121152 (p 2156) (p 2284) (p 2440) (p 2573) (p 2659) (p 2911) (p 3016) (p 3413) (p 3872) (p 4705) (derived106238 p h) (derived85525 p h)

theorem derived121158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3355) ∨ (p 3115) ∨ (p 2761) ∨ (¬ p 3362) ∨ (p 2156) ∨ (¬ p 2284) ∨ (¬ p 2145) :=
  ElevenRUP.step121158 (p 2145) (p 2156) (p 2284) (p 2761) (p 3115) (p 3276) (p 3355) (p 3362) (p 3951) (derived106536 p h) (derived85553 p h)

theorem derived121161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4988) ∨ (p 2264) ∨ (¬ p 4333) ∨ (p 2156) :=
  ElevenRUP.step121161 (p 2156) (p 2264) (p 2341) (p 4333) (p 4558) (p 4988) (derived105400 p h) (derived85569 p h)

theorem derived121165 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 3379) ∨ (p 2396) ∨ (¬ p 2922) ∨ (¬ p 2911) ∨ (p 2274) :=
  ElevenRUP.step121165 (p 2156) (p 2274) (p 2396) (p 2911) (p 2922) (p 3379) (p 4666) (derived105658 p h) (derived85573 p h)

theorem derived121169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3922) ∨ (p 2341) ∨ (¬ p 2274) ∨ (¬ p 3546) ∨ (¬ p 4105) ∨ (¬ p 2177) :=
  ElevenRUP.step121169 (p 2177) (p 2274) (p 2341) (p 3546) (p 3922) (p 4105) (p 4564) (derived105401 p h) (derived85587 p h)

theorem derived121178 (p : Nat → Prop) (h : Inputs p) :
    (p 2145) ∨ (¬ p 2753) ∨ (¬ p 3645) :=
  ElevenRUP.step121178 (p 2145) (p 2753) (p 3645) (p 4877) (derived105451 p h) (h 23731)

theorem derived121183 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (¬ p 3323) ∨ (¬ p 4032) ∨ (¬ p 2383) ∨ (¬ p 4322) ∨ (¬ p 2761) ∨ (¬ p 2584) ∨ (¬ p 3519) ∨ (¬ p 3645) ∨ (¬ p 4874) :=
  ElevenRUP.step121183 (p 2383) (p 2584) (p 2668) (p 2761) (p 3323) (p 3519) (p 3645) (p 4032) (p 4322) (p 4376) (p 4621) (p 4874) (derived106320 p h) (derived105407 p h) (derived85643 p h)

theorem derived121186 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2749) ∨ (p 2156) ∨ (¬ p 2651) ∨ (¬ p 4343) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (p 2187) ∨ (¬ p 5580) ∨ (¬ p 2246) ∨ (¬ p 3645) ∨ (¬ p 5123) :=
  ElevenRUP.step121186 (p 2156) (p 2187) (p 2246) (p 2651) (p 2749) (p 3276) (p 3333) (p 3645) (p 4343) (p 4877) (p 5123) (p 5580) (derived105451 p h) (derived85660 p h)

theorem derived121197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2132) ∨ (¬ p 2493) ∨ (¬ p 4438) ∨ (¬ p 2881) ∨ (¬ p 2870) ∨ (¬ p 4108) ∨ (p 2573) :=
  ElevenRUP.step121197 (p 2132) (p 2493) (p 2509) (p 2573) (p 2870) (p 2881) (p 4108) (p 4438) (p 4733) (derived105430 p h) (derived85722 p h)

theorem derived121198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 2901) ∨ (¬ p 2493) ∨ (¬ p 4108) ∨ (p 2573) ∨ (p 2406) ∨ (¬ p 2132) ∨ (¬ p 2870) :=
  ElevenRUP.step121198 (p 2132) (p 2406) (p 2493) (p 2573) (p 2870) (p 2901) (p 3115) (p 4108) (p 4733) (derived105430 p h) (derived85723 p h)

theorem derived121203 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2493) ∨ (¬ p 2651) ∨ (¬ p 4389) :=
  ElevenRUP.step121203 (p 2331) (p 2493) (p 2651) (p 4389) (p 4814) (derived105440 p h) (derived85739 p h)

theorem derived121206 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2352) ∨ (¬ p 2957) ∨ (p 3051) ∨ (¬ p 2651) ∨ (p 2881) ∨ (¬ p 4116) ∨ (¬ p 2493) :=
  ElevenRUP.step121206 (p 2255) (p 2352) (p 2493) (p 2651) (p 2881) (p 2957) (p 2992) (p 3051) (p 4116) (p 4133) (derived105367 p h) (derived105712 p h) (derived85744 p h)

theorem derived121207 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 3379) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 2493) ∨ (p 3256) :=
  ElevenRUP.step121207 (p 2254) (p 2352) (p 2459) (p 2493) (p 3166) (p 3256) (p 3379) (p 4133) (derived105366 p h) (derived105712 p h) (derived85747 p h)

theorem derived121210 (p : Nat → Prop) (h : Inputs p) :
    (p 2901) ∨ (p 2946) ∨ (¬ p 3379) ∨ (¬ p 2352) ∨ (¬ p 2493) ∨ (p 2881) :=
  ElevenRUP.step121210 (p 2254) (p 2352) (p 2493) (p 2881) (p 2901) (p 2946) (p 3379) (p 4133) (derived105366 p h) (derived105712 p h) (derived85752 p h)

theorem derived121211 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3379) ∨ (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 2459) ∨ (p 3146) :=
  ElevenRUP.step121211 (p 2220) (p 2352) (p 2459) (p 2493) (p 3146) (p 3379) (p 4133) (derived105712 p h) (derived85755 p h)

theorem derived121212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3379) ∨ (¬ p 3919) ∨ (¬ p 2352) ∨ (p 3256) ∨ (p 2807) ∨ (¬ p 2459) :=
  ElevenRUP.step121212 (p 2254) (p 2352) (p 2459) (p 2493) (p 2807) (p 3256) (p 3379) (p 3919) (p 4133) (derived105366 p h) (derived105712 p h) (derived85757 p h)

theorem derived121213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4194) ∨ (¬ p 2352) ∨ (p 2668) ∨ (¬ p 2493) :=
  ElevenRUP.step121213 (p 2352) (p 2493) (p 2668) (p 4194) (p 4814) (derived105440 p h) (derived85759 p h)

theorem derived121214 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 3564) ∨ (¬ p 3379) ∨ (p 3146) ∨ (p 2946) ∨ (¬ p 2493) :=
  ElevenRUP.step121214 (p 2254) (p 2493) (p 2946) (p 3146) (p 3156) (p 3379) (p 3564) (p 4330) (derived105366 p h) (derived106329 p h) (derived85763 p h)

theorem derived121215 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 4116) ∨ (¬ p 2651) ∨ (¬ p 3879) ∨ (¬ p 2493) :=
  ElevenRUP.step121215 (p 2493) (p 2651) (p 2946) (p 3879) (p 4116) (p 4717) (derived105424 p h) (derived85767 p h)

theorem derived121218 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2493) ∨ (¬ p 3379) ∨ (¬ p 4034) :=
  ElevenRUP.step121218 (p 2210) (p 2493) (p 3379) (p 4034) (p 4717) (derived105424 p h) (derived85780 p h)

theorem derived121221 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2493) ∨ (¬ p 4203) ∨ (p 2406) :=
  ElevenRUP.step121221 (p 2156) (p 2406) (p 2493) (p 4203) (p 4533) (derived105394 p h) (derived85790 p h)

theorem derived121222 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (¬ p 2493) ∨ (¬ p 4203) ∨ (p 2406) :=
  ElevenRUP.step121222 (p 2284) (p 2406) (p 2493) (p 4203) (p 4702) (derived106079 p h) (derived85791 p h)

theorem derived121223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3575) ∨ (¬ p 2341) ∨ (¬ p 2926) ∨ (¬ p 2493) ∨ (p 3527) ∨ (¬ p 3741) :=
  ElevenRUP.step121223 (p 2341) (p 2493) (p 2926) (p 3527) (p 3575) (p 3741) (p 4717) (derived105424 p h) (derived85802 p h)

theorem derived121224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2926) ∨ (¬ p 2417) ∨ (¬ p 3741) ∨ (p 3631) ∨ (¬ p 2493) :=
  ElevenRUP.step121224 (p 2417) (p 2493) (p 2926) (p 3631) (p 3741) (p 4717) (derived105424 p h) (derived85803 p h)

theorem derived121225 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (p 2946) ∨ (¬ p 2553) ∨ (p 2187) ∨ (¬ p 2493) ∨ (¬ p 3379) :=
  ElevenRUP.step121225 (p 2187) (p 2254) (p 2284) (p 2493) (p 2553) (p 2946) (p 3379) (derived105366 p h) (derived85804 p h)

theorem derived121226 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 2427) ∨ (¬ p 2493) ∨ (¬ p 4203) :=
  ElevenRUP.step121226 (p 2406) (p 2427) (p 2493) (p 4203) (p 4555) (derived105542 p h) (derived85808 p h)

theorem derived121227 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 4279) ∨ (¬ p 2312) ∨ (¬ p 2274) ∨ (¬ p 2493) :=
  ElevenRUP.step121227 (p 2274) (p 2312) (p 2493) (p 2922) (p 3958) (p 4279) (derived105378 p h) (derived85810 p h)

theorem derived121234 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2992) ∨ (¬ p 2608) ∨ (¬ p 2245) :=
  ElevenRUP.step121234 (p 2245) (p 2608) (p 2744) (p 2946) (p 2992) (derived106503 p h) (derived85846 p h)

theorem derived121235 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2992) ∨ (p 2727) ∨ (¬ p 2807) :=
  ElevenRUP.step121235 (p 2727) (p 2807) (p 2946) (p 2992) (p 4652) (derived105413 p h) (derived85850 p h)

theorem derived121237 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2992) ∨ (p 2727) ∨ (¬ p 4241) :=
  ElevenRUP.step121237 (p 2727) (p 2850) (p 2992) (p 4241) (p 4750) (derived105433 p h) (derived85860 p h)

theorem derived121238 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2992) ∨ (p 2440) ∨ (p 2727) :=
  ElevenRUP.step121238 (p 2440) (p 2493) (p 2727) (p 2992) (p 4715) (derived105423 p h) (derived85863 p h)

theorem derived121239 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2992) ∨ (p 2727) ∨ (¬ p 4241) :=
  ElevenRUP.step121239 (p 2727) (p 2992) (p 3016) (p 4241) (p 4715) (derived105423 p h) (derived85864 p h)

theorem derived121245 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (p 2437) ∨ (¬ p 2992) ∨ (¬ p 4241) :=
  ElevenRUP.step121245 (p 2437) (p 2727) (p 2992) (p 4241) (p 4644) (derived105411 p h) (derived85890 p h)

theorem derived121246 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2992) ∨ (p 2727) ∨ (¬ p 4241) :=
  ElevenRUP.step121246 (p 2727) (p 2992) (p 3083) (p 4241) (p 4608) (derived105540 p h) (derived85892 p h)

theorem derived121248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2241) ∨ (p 2352) ∨ (¬ p 4450) ∨ (p 2573) ∨ (¬ p 3115) ∨ (p 2363) :=
  ElevenRUP.step121248 (p 2241) (p 2352) (p 2363) (p 2573) (p 2992) (p 3115) (p 4450) (p 5193) (derived105488 p h) (derived85903 p h)

theorem derived121249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2641) ∨ (¬ p 2563) :=
  ElevenRUP.step121249 (p 2563) (p 2641) (p 2992) (p 4702) (derived106079 p h) (derived85906 p h)

theorem derived121257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3745) ∨ (p 2641) ∨ (¬ p 3156) ∨ (¬ p 2992) :=
  ElevenRUP.step121257 (p 2641) (p 2992) (p 3156) (p 3745) (p 4509) (derived105392 p h) (derived85939 p h)

theorem derived121259 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2992) ∨ (¬ p 2901) ∨ (¬ p 3745) :=
  ElevenRUP.step121259 (p 2641) (p 2901) (p 2992) (p 3745) (p 4558) (derived105400 p h) (derived85941 p h)

theorem derived121260 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2742) ∨ (¬ p 2901) ∨ (¬ p 3745) ∨ (¬ p 2992) :=
  ElevenRUP.step121260 (p 2742) (p 2797) (p 2901) (p 2992) (p 3745) (p 4558) (derived105400 p h) (derived85943 p h)

theorem derived121261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3699) ∨ (¬ p 3051) :=
  ElevenRUP.step121261 (p 2960) (p 2992) (p 2996) (p 3051) (p 3699) (derived105377 p h) (derived52228 p h)

theorem derived121262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 2427) ∨ (¬ p 3699) :=
  ElevenRUP.step121262 (p 2427) (p 2992) (p 2996) (p 3699) (p 4702) (derived106079 p h) (derived51727 p h)

theorem derived121266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3699) ∨ (¬ p 2996) ∨ (¬ p 2284) :=
  ElevenRUP.step121266 (p 2284) (p 2992) (p 2996) (p 3699) (p 4555) (derived105542 p h) (derived54097 p h)

theorem derived121268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2992) ∨ (p 2573) ∨ (¬ p 2241) ∨ (p 2553) ∨ (p 2177) :=
  ElevenRUP.step121268 (p 2177) (p 2241) (p 2553) (p 2573) (p 2992) (p 3156) (p 4902) (p 5193) (derived105456 p h) (derived105488 p h) (derived85962 p h)

theorem derived121270 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2245) ∨ (p 2946) ∨ (¬ p 2992) ∨ (¬ p 2177) ∨ (¬ p 2774) ∨ (¬ p 2122) ∨ (¬ p 4041) :=
  ElevenRUP.step121270 (p 2122) (p 2177) (p 2245) (p 2774) (p 2946) (p 2992) (p 3189) (p 4041) (p 4733) (derived105430 p h) (derived85972 p h)

theorem derived121272 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2950) ∨ (¬ p 2992) ∨ (¬ p 2284) :=
  ElevenRUP.step121272 (p 2156) (p 2249) (p 2284) (p 2950) (p 2992) (derived106513 p h) (derived85979 p h)

theorem derived121274 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2245) ∨ (¬ p 2641) ∨ (¬ p 2608) :=
  ElevenRUP.step121274 (p 2245) (p 2331) (p 2608) (p 2641) (p 2744) (derived106503 p h) (derived86002 p h)

theorem derived121276 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (¬ p 2295) ∨ (p 3125) ∨ (p 2563) ∨ (¬ p 2641) ∨ (¬ p 2241) ∨ (¬ p 4620) :=
  ElevenRUP.step121276 (p 2230) (p 2241) (p 2295) (p 2563) (p 2641) (p 3125) (p 4620) (p 5193) (derived105488 p h) (derived86006 p h)

theorem derived121277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3487) ∨ (p 2651) ∨ (p 2406) ∨ (¬ p 2295) ∨ (¬ p 2641) ∨ (p 2373) ∨ (¬ p 2177) :=
  ElevenRUP.step121277 (p 2177) (p 2249) (p 2295) (p 2373) (p 2406) (p 2641) (p 2651) (p 3487) (p 4905) (derived106513 p h) (derived105995 p h) (derived86007 p h)

theorem derived121280 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (p 2992) ∨ (¬ p 2641) ∨ (¬ p 3986) :=
  ElevenRUP.step121280 (p 2641) (p 2992) (p 3115) (p 3986) (p 5043) (derived105471 p h) (derived86016 p h)

theorem derived121281 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 2156) ∨ (¬ p 2641) ∨ (¬ p 3986) :=
  ElevenRUP.step121281 (p 2156) (p 2641) (p 2954) (p 2992) (p 3986) (derived106494 p h) (derived86027 p h)

theorem derived121283 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2911) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 5197) ∨ (p 2341) ∨ (¬ p 3323) :=
  ElevenRUP.step121283 (p 2241) (p 2341) (p 2417) (p 2641) (p 2911) (p 3323) (p 4621) (p 5193) (p 5197) (derived105488 p h) (derived105407 p h) (derived86030 p h)

theorem derived121284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (p 2563) ∨ (p 2230) ∨ (¬ p 2241) ∨ (p 2274) :=
  ElevenRUP.step121284 (p 2230) (p 2241) (p 2274) (p 2563) (p 2641) (p 2668) (p 4405) (p 5193) (derived105512 p h) (derived105488 p h) (derived86031 p h)

theorem derived121285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 3051) ∨ (¬ p 4399) ∨ (p 2891) ∨ (¬ p 2656) ∨ (¬ p 2641) :=
  ElevenRUP.step121285 (p 2641) (p 2656) (p 2891) (p 3051) (p 3368) (p 4399) (p 4975) (derived105464 p h) (derived86038 p h)

theorem derived121286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3959) ∨ (p 2707) ∨ (p 2459) ∨ (¬ p 2641) ∨ (p 2341) ∨ (¬ p 3323) ∨ (¬ p 2742) ∨ (¬ p 2696) :=
  ElevenRUP.step121286 (p 2341) (p 2459) (p 2641) (p 2696) (p 2707) (p 2742) (p 3323) (p 3959) (p 4330) (derived106329 p h) (derived86043 p h)

theorem derived121287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (p 3051) ∨ (p 2992) ∨ (¬ p 3986) ∨ (¬ p 2641) :=
  ElevenRUP.step121287 (p 2641) (p 2957) (p 2992) (p 3051) (p 3986) (p 4555) (derived105542 p h) (derived86048 p h)

theorem derived121288 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 3986) ∨ (p 2563) ∨ (¬ p 2641) :=
  ElevenRUP.step121288 (p 2563) (p 2641) (p 2992) (p 3986) (p 4705) (derived106238 p h) (derived86050 p h)

theorem derived121289 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (p 3389) ∨ (p 2459) ∨ (¬ p 3323) :=
  ElevenRUP.step121289 (p 2241) (p 2459) (p 2641) (p 2911) (p 3323) (p 3389) (p 4330) (p 5193) (derived105488 p h) (derived106329 p h) (derived86058 p h)

theorem derived121291 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (p 3189) ∨ (¬ p 4041) ∨ (¬ p 2245) ∨ (p 2459) ∨ (¬ p 2641) ∨ (¬ p 2528) ∨ (¬ p 2470) :=
  ElevenRUP.step121291 (p 2245) (p 2331) (p 2459) (p 2470) (p 2528) (p 2641) (p 3189) (p 4041) (p 5190) (derived105487 p h) (derived86069 p h)

theorem derived121292 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 2651) ∨ (¬ p 2641) ∨ (¬ p 3166) :=
  ElevenRUP.step121292 (p 2641) (p 2651) (p 3166) (p 3189) (p 4975) (derived105464 p h) (derived86071 p h)

theorem derived121293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 2992) ∨ (¬ p 2641) ∨ (p 2563) ∨ (¬ p 4356) :=
  ElevenRUP.step121293 (p 2563) (p 2641) (p 2992) (p 3567) (p 4356) (p 4705) (derived106238 p h) (derived86072 p h)

theorem derived121294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 3567) ∨ (¬ p 3487) ∨ (¬ p 2396) ∨ (¬ p 2641) ∨ (p 2528) ∨ (¬ p 2307) ∨ (p 2651) ∨ (¬ p 3950) :=
  ElevenRUP.step121294 (p 2249) (p 2307) (p 2396) (p 2509) (p 2528) (p 2641) (p 2651) (p 3487) (p 3567) (p 3950) (derived106513 p h) (derived86073 p h)

theorem derived121297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (¬ p 2230) ∨ (p 2406) ∨ (¬ p 3402) ∨ (¬ p 2641) :=
  ElevenRUP.step121297 (p 2230) (p 2406) (p 2641) (p 2656) (p 3402) (p 4975) (derived105464 p h) (derived86077 p h)

theorem derived121298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3346) ∨ (¬ p 3323) ∨ (¬ p 2241) ∨ (¬ p 3266) ∨ (¬ p 2641) ∨ (p 3276) :=
  ElevenRUP.step121298 (p 2241) (p 2641) (p 3266) (p 3276) (p 3323) (p 3346) (p 4330) (p 5193) (derived105488 p h) (derived106329 p h) (derived86078 p h)

theorem derived121299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (p 2651) ∨ (¬ p 2807) :=
  ElevenRUP.step121299 (p 2641) (p 2651) (p 2807) (p 2996) (p 4975) (derived105464 p h) (derived86080 p h)

theorem derived121303 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2187) ∨ (¬ p 4769) ∨ (¬ p 2641) :=
  ElevenRUP.step121303 (p 2187) (p 2641) (p 3189) (p 4564) (p 4769) (derived105401 p h) (derived86090 p h)

theorem derived121304 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2187) ∨ (¬ p 3984) ∨ (¬ p 4769) ∨ (¬ p 2641) :=
  ElevenRUP.step121304 (p 2187) (p 2641) (p 3189) (p 3958) (p 3984) (p 4769) (derived105378 p h) (derived86091 p h)

theorem derived121306 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2373) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2241) ∨ (¬ p 2427) :=
  ElevenRUP.step121306 (p 2241) (p 2373) (p 2427) (p 2641) (p 2668) (p 3051) (p 4134) (derived105379 p h) (derived86099 p h)

theorem derived121307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (p 2383) ∨ (¬ p 2641) ∨ (¬ p 2668) :=
  ElevenRUP.step121307 (p 2249) (p 2383) (p 2641) (p 2668) (p 3983) (derived106513 p h) (derived86100 p h)

theorem derived121308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 2298) ∨ (¬ p 2553) :=
  ElevenRUP.step121308 (p 2298) (p 2553) (p 2641) (p 2996) (p 4973) (derived105835 p h) (derived49721 p h)

theorem derived121309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 2298) ∨ (¬ p 3323) :=
  ElevenRUP.step121309 (p 2298) (p 2641) (p 2996) (p 3323) (p 4624) (derived105408 p h) (derived50118 p h)

theorem derived121310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 3984) ∨ (¬ p 2298) ∨ (¬ p 2274) :=
  ElevenRUP.step121310 (p 2274) (p 2298) (p 2641) (p 2996) (p 3958) (p 3984) (derived105378 p h) (derived51731 p h)

theorem derived121311 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 2298) ∨ (¬ p 2307) :=
  ElevenRUP.step121311 (p 2298) (p 2307) (p 2641) (p 2996) (p 4584) (derived105406 p h) (derived49286 p h)

theorem derived121312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 2298) ∨ (¬ p 2668) :=
  ElevenRUP.step121312 (p 2298) (p 2641) (p 2668) (p 2996) (p 4405) (derived105512 p h) (derived42571 p h)

theorem derived121314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (¬ p 2641) ∨ (¬ p 2807) ∨ (p 2553) ∨ (¬ p 2274) ∨ (p 2573) ∨ (¬ p 2253) :=
  ElevenRUP.step121314 (p 2253) (p 2274) (p 2553) (p 2573) (p 2641) (p 2807) (p 2996) (p 4564) (p 5193) (derived105488 p h) (derived105401 p h) (derived86114 p h)

theorem derived121315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3848) ∨ (¬ p 4190) ∨ (¬ p 2641) ∨ (¬ p 3125) :=
  ElevenRUP.step121315 (p 2641) (p 3125) (p 3848) (p 4190) (p 4564) (derived105401 p h) (derived54909 p h)

theorem derived121316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (¬ p 4841) ∨ (p 2122) ∨ (¬ p 2307) ∨ (¬ p 2641) :=
  ElevenRUP.step121316 (p 2122) (p 2307) (p 2641) (p 2751) (p 3567) (p 4841) (derived106343 p h) (derived86118 p h)

theorem derived121319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3368) ∨ (¬ p 3212) ∨ (¬ p 2641) ∨ (p 2972) ∨ (¬ p 4399) ∨ (¬ p 2656) :=
  ElevenRUP.step121319 (p 2641) (p 2656) (p 2972) (p 3212) (p 3368) (p 4399) (p 4975) (derived105464 p h) (derived86126 p h)

theorem derived121322 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (p 2850) ∨ (¬ p 2295) ∨ (p 2427) ∨ (¬ p 2641) ∨ (¬ p 2241) :=
  ElevenRUP.step121322 (p 2241) (p 2295) (p 2427) (p 2598) (p 2641) (p 2850) (p 4559) (p 4736) (derived105431 p h) (derived105701 p h) (derived86146 p h)

theorem derived121324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2748) ∨ (¬ p 2819) ∨ (p 2696) ∨ (¬ p 2996) ∨ (¬ p 2829) ∨ (¬ p 2363) ∨ (p 2449) :=
  ElevenRUP.step121324 (p 2363) (p 2449) (p 2696) (p 2748) (p 2819) (p 2829) (p 2996) (p 4669) (derived105415 p h) (derived86171 p h)

theorem derived121326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2318) ∨ (p 3516) ∨ (p 2122) ∨ (¬ p 3550) :=
  ElevenRUP.step121326 (p 2122) (p 2318) (p 2819) (p 3516) (p 3550) (p 4666) (derived105658 p h) (derived86173 p h)

theorem derived121330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2406) ∨ (p 2122) ∨ (¬ p 3379) ∨ (¬ p 2427) ∨ (p 2383) ∨ (¬ p 5021) :=
  ElevenRUP.step121330 (p 2122) (p 2383) (p 2406) (p 2427) (p 2819) (p 3379) (p 4556) (p 5021) (derived105399 p h) (derived86192 p h)

theorem derived121331 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (¬ p 2307) ∨ (¬ p 5017) ∨ (p 2373) ∨ (¬ p 2819) ∨ (p 2122) ∨ (p 3379) :=
  ElevenRUP.step121331 (p 2122) (p 2307) (p 2373) (p 2406) (p 2819) (p 3379) (p 4134) (p 5017) (derived105379 p h) (derived86202 p h)

theorem derived121335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3146) ∨ (¬ p 2608) ∨ (p 3166) ∨ (¬ p 2829) ∨ (p 3256) :=
  ElevenRUP.step121335 (p 2254) (p 2608) (p 2819) (p 2829) (p 3146) (p 3166) (p 3256) (p 4134) (derived105366 p h) (derived105379 p h) (derived86207 p h)

theorem derived121336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4024) ∨ (¬ p 2252) ∨ (¬ p 2819) ∨ (p 3256) ∨ (¬ p 2459) ∨ (p 2608) ∨ (p 2807) ∨ (¬ p 3093) ∨ (¬ p 3919) :=
  ElevenRUP.step121336 (p 2252) (p 2459) (p 2608) (p 2750) (p 2807) (p 2819) (p 3093) (p 3256) (p 3919) (p 4024) (p 4133) (derived106345 p h) (derived105712 p h) (derived86219 p h)

theorem derived121337 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 2819) ∨ (¬ p 2608) ∨ (¬ p 2829) ∨ (p 3256) ∨ (¬ p 2459) :=
  ElevenRUP.step121337 (p 2254) (p 2459) (p 2608) (p 2819) (p 2829) (p 3166) (p 3256) (p 4133) (derived105366 p h) (derived105712 p h) (derived86220 p h)

theorem derived121339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 4426) ∨ (p 2641) ∨ (¬ p 2667) ∨ (p 2383) :=
  ElevenRUP.step121339 (p 2383) (p 2641) (p 2667) (p 2745) (p 2819) (p 4426) (derived105523 p h) (derived86224 p h)

theorem derived121342 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2819) ∨ (¬ p 2363) ∨ (¬ p 3573) :=
  ElevenRUP.step121342 (p 2363) (p 2528) (p 2819) (p 3573) (p 5225) (derived105495 p h) (derived86229 p h)

theorem derived121344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2753) ∨ (p 2651) ∨ (¬ p 2819) ∨ (p 2911) ∨ (p 2437) ∨ (¬ p 3654) ∨ (¬ p 2252) ∨ (¬ p 2786) :=
  ElevenRUP.step121344 (p 2252) (p 2437) (p 2651) (p 2750) (p 2753) (p 2786) (p 2819) (p 2911) (p 3654) (p 3917) (p 4133) (derived106345 p h) (derived105712 p h) (derived86231 p h)

theorem derived121346 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (¬ p 2829) ∨ (p 2274) ∨ (p 2563) ∨ (¬ p 2608) ∨ (¬ p 2819) :=
  ElevenRUP.step121346 (p 2230) (p 2274) (p 2563) (p 2608) (p 2819) (p 2829) (p 4405) (p 5193) (derived105512 p h) (derived105488 p h) (derived86234 p h)

theorem derived121351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4375) ∨ (¬ p 2819) ∨ (p 3016) ∨ (p 2383) ∨ (¬ p 2386) :=
  ElevenRUP.step121351 (p 2383) (p 2386) (p 2819) (p 3016) (p 4375) (p 4753) (derived105514 p h) (derived86248 p h)

theorem derived121353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (p 2651) ∨ (p 2528) ∨ (¬ p 2307) ∨ (¬ p 2786) ∨ (p 2122) ∨ (p 3083) ∨ (¬ p 2819) ∨ (¬ p 2753) ∨ (¬ p 3550) ∨ (¬ p 2252) :=
  ElevenRUP.step121353 (p 2122) (p 2252) (p 2307) (p 2528) (p 2651) (p 2750) (p 2753) (p 2786) (p 2819) (p 3083) (p 3550) (p 3941) (derived106345 p h) (derived86250 p h)

theorem derived121358 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2655) ∨ (¬ p 2819) ∨ (p 2122) ∨ (¬ p 2786) ∨ (p 2440) ∨ (p 2230) ∨ (¬ p 2307) :=
  ElevenRUP.step121358 (p 2122) (p 2230) (p 2307) (p 2440) (p 2655) (p 2786) (p 2819) (p 3083) (p 4384) (p 4789) (derived106167 p h) (derived105646 p h) (derived86261 p h)

theorem derived121361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 2819) ∨ (p 4149) ∨ (¬ p 3573) :=
  ElevenRUP.step121361 (p 2819) (p 3573) (p 3979) (p 4149) (p 5225) (derived105495 p h) (derived86269 p h)

theorem derived121364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 2509) ∨ (p 3379) ∨ (¬ p 2819) ∨ (p 2528) ∨ (¬ p 2774) :=
  ElevenRUP.step121364 (p 2509) (p 2528) (p 2774) (p 2819) (p 3379) (p 3979) (p 4733) (p 5122) (derived105430 p h) (derived105483 p h) (derived86275 p h)

theorem derived121369 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3953) ∨ (¬ p 3367) ∨ (¬ p 2819) ∨ (¬ p 3923) :=
  ElevenRUP.step121369 (p 2819) (p 3367) (p 3923) (p 3953) (p 5221) (derived105796 p h) (derived41149 p h)

theorem derived121370 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2187) ∨ (p 2274) ∨ (¬ p 3550) :=
  ElevenRUP.step121370 (p 2187) (p 2274) (p 2911) (p 3550) (p 4276) (derived105516 p h) (derived86290 p h)

theorem derived121373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2373) ∨ (¬ p 3379) ∨ (p 2177) ∨ (p 2122) ∨ (p 2774) :=
  ElevenRUP.step121373 (p 2122) (p 2177) (p 2373) (p 2406) (p 2774) (p 3379) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived86322 p h)

theorem derived121374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4342) ∨ (p 2774) ∨ (¬ p 3016) ∨ (¬ p 2598) :=
  ElevenRUP.step121374 (p 2598) (p 2774) (p 3016) (p 4342) (p 4750) (derived105433 p h) (derived86324 p h)

theorem derived121375 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2598) ∨ (¬ p 2493) ∨ (¬ p 4342) :=
  ElevenRUP.step121375 (p 2493) (p 2598) (p 2774) (p 4342) (p 5217) (derived105493 p h) (derived86334 p h)

theorem derived121377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3366) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 2246) ∨ (p 2774) ∨ (¬ p 3146) ∨ (¬ p 3156) :=
  ElevenRUP.step121377 (p 2122) (p 2246) (p 2396) (p 2744) (p 2774) (p 2946) (p 3146) (p 3156) (p 3366) (p 4669) (derived106503 p h) (derived105415 p h) (derived86338 p h)

theorem derived121379 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 3379) ∨ (¬ p 2922) ∨ (¬ p 2911) :=
  ElevenRUP.step121379 (p 2122) (p 2396) (p 2774) (p 2911) (p 2922) (p 3379) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived86350 p h)

theorem derived121381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2992) ∨ (p 2122) ∨ (p 2177) ∨ (¬ p 3189) ∨ (¬ p 4311) ∨ (¬ p 2253) ∨ (p 2774) :=
  ElevenRUP.step121381 (p 2122) (p 2177) (p 2253) (p 2774) (p 2946) (p 2992) (p 3189) (p 4311) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived86364 p h)

theorem derived121383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 3156) ∨ (¬ p 5119) ∨ (¬ p 2946) ∨ (¬ p 3366) ∨ (p 2774) ∨ (¬ p 2246) ∨ (¬ p 3917) ∨ (p 3461) :=
  ElevenRUP.step121383 (p 2246) (p 2744) (p 2774) (p 2946) (p 3156) (p 3366) (p 3461) (p 3917) (p 3969) (p 5119) (derived106503 p h) (derived86368 p h)

theorem derived121384 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3950) ∨ (¬ p 3379) ∨ (p 2819) ∨ (p 2363) ∨ (¬ p 2417) ∨ (¬ p 2922) :=
  ElevenRUP.step121384 (p 2363) (p 2417) (p 2774) (p 2819) (p 2922) (p 3379) (p 3950) (p 4736) (derived105431 p h) (derived86370 p h)

theorem derived121387 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2230) ∨ (¬ p 3362) ∨ (p 2774) :=
  ElevenRUP.step121387 (p 2230) (p 2774) (p 2850) (p 3362) (p 5221) (derived105796 p h) (derived86377 p h)

theorem derived121389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2230) ∨ (¬ p 3146) ∨ (¬ p 4419) ∨ (p 2774) ∨ (p 2122) ∨ (p 2396) :=
  ElevenRUP.step121389 (p 2122) (p 2230) (p 2373) (p 2396) (p 2774) (p 3146) (p 4419) (p 4669) (derived105415 p h) (derived86382 p h)

theorem derived121390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3917) ∨ (¬ p 2417) ∨ (p 2774) ∨ (p 2911) ∨ (¬ p 2696) ∨ (¬ p 5201) ∨ (¬ p 3759) :=
  ElevenRUP.step121390 (p 2341) (p 2417) (p 2696) (p 2774) (p 2911) (p 3759) (p 3917) (p 4625) (p 4749) (p 5201) (derived105432 p h) (derived106455 p h) (derived86383 p h)

theorem derived121396 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (p 2774) ∨ (p 2553) ∨ (¬ p 4475) :=
  ElevenRUP.step121396 (p 2553) (p 2774) (p 3425) (p 4475) (p 5225) (derived105495 p h) (derived86400 p h)

theorem derived121401 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2246) ∨ (p 2363) ∨ (¬ p 3950) ∨ (¬ p 2437) ∨ (¬ p 2417) ∨ (¬ p 2651) ∨ (p 2819) ∨ (¬ p 3366) :=
  ElevenRUP.step121401 (p 2246) (p 2363) (p 2417) (p 2437) (p 2651) (p 2744) (p 2774) (p 2819) (p 3366) (p 3950) (derived106503 p h) (derived86419 p h)

theorem derived121403 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2651) ∨ (¬ p 4395) ∨ (¬ p 2982) ∨ (p 2440) ∨ (p 2122) ∨ (p 2396) :=
  ElevenRUP.step121403 (p 2122) (p 2396) (p 2440) (p 2651) (p 2774) (p 2982) (p 4395) (p 4786) (derived106425 p h) (derived86435 p h)

theorem derived121404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (¬ p 5564) ∨ (¬ p 3399) ∨ (p 2241) ∨ (p 2774) ∨ (¬ p 3366) ∨ (¬ p 3037) ∨ (p 2122) ∨ (p 2177) :=
  ElevenRUP.step121404 (p 2122) (p 2177) (p 2241) (p 2744) (p 2774) (p 3037) (p 3366) (p 3399) (p 3931) (p 5564) (derived106503 p h) (derived86437 p h)

theorem derived121408 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 2774) ∨ (¬ p 2274) ∨ (¬ p 2641) ∨ (p 2122) ∨ (¬ p 3166) ∨ (¬ p 2253) :=
  ElevenRUP.step121408 (p 2122) (p 2253) (p 2274) (p 2641) (p 2774) (p 3166) (p 3189) (p 4564) (p 4736) (derived105431 p h) (derived105401 p h) (derived86455 p h)

theorem derived121411 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2774) ∨ (p 3146) ∨ (p 2177) ∨ (¬ p 3166) ∨ (¬ p 3256) :=
  ElevenRUP.step121411 (p 2122) (p 2177) (p 2774) (p 3146) (p 3166) (p 3256) (p 4786) (p 4902) (derived105456 p h) (derived106425 p h) (derived86469 p h)

theorem derived121413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 3166) ∨ (p 2122) ∨ (¬ p 3266) ∨ (¬ p 3256) ∨ (p 2774) :=
  ElevenRUP.step121413 (p 2122) (p 2774) (p 3166) (p 3256) (p 3266) (p 4260) (p 4786) (p 4831) (derived106425 p h) (derived105445 p h) (derived86473 p h)

theorem derived121415 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2449) ∨ (p 2264) ∨ (¬ p 4443) :=
  ElevenRUP.step121415 (p 2264) (p 2449) (p 2528) (p 4420) (p 4443) (derived105707 p h) (derived86496 p h)

theorem derived121416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 4849) ∨ (¬ p 2252) ∨ (p 3516) :=
  ElevenRUP.step121416 (p 2252) (p 2449) (p 2685) (p 2745) (p 3516) (p 4849) (derived105523 p h) (derived86506 p h)

theorem derived121418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4155) ∨ (¬ p 2881) ∨ (¬ p 2449) ∨ (p 2396) ∨ (p 2341) :=
  ElevenRUP.step121418 (p 2341) (p 2396) (p 2449) (p 2881) (p 4155) (p 4559) (derived105701 p h) (derived86520 p h)

theorem derived121419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2417) ∨ (¬ p 2449) ∨ (p 2264) :=
  ElevenRUP.step121419 (p 2264) (p 2417) (p 2449) (p 2881) (p 4277) (derived105380 p h) (derived86525 p h)

theorem derived121423 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 2449) ∨ (¬ p 5260) ∨ (¬ p 2132) ∨ (p 2264) ∨ (¬ p 2187) ∨ (¬ p 2860) :=
  ElevenRUP.step121423 (p 2132) (p 2187) (p 2264) (p 2449) (p 2860) (p 3516) (p 4133) (p 5260) (derived105712 p h) (derived86541 p h)

theorem derived121424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2449) ∨ (¬ p 3580) ∨ (p 2417) :=
  ElevenRUP.step121424 (p 2417) (p 2440) (p 2449) (p 3580) (p 4646) (derived105534 p h) (derived86542 p h)

theorem derived121425 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 2427) ∨ (p 3246) ∨ (¬ p 2995) :=
  ElevenRUP.step121425 (p 2427) (p 2449) (p 2995) (p 3246) (p 4705) (derived106238 p h) (derived86545 p h)

theorem derived121426 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2449) ∨ (¬ p 2441) ∨ (p 2417) ∨ (¬ p 3580) :=
  ElevenRUP.step121426 (p 2417) (p 2441) (p 2449) (p 3083) (p 3580) (p 4608) (derived105540 p h) (derived86547 p h)

theorem derived121427 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2449) ∨ (¬ p 2441) ∨ (p 2417) ∨ (¬ p 3580) :=
  ElevenRUP.step121427 (p 2417) (p 2441) (p 2449) (p 3016) (p 3580) (p 4715) (derived105423 p h) (derived86548 p h)

theorem derived121431 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2870) ∨ (¬ p 3399) ∨ (¬ p 3571) :=
  ElevenRUP.step121431 (p 2210) (p 2870) (p 3399) (p 3571) (p 4878) (derived105452 p h) (derived86570 p h)

theorem derived121433 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (p 2608) ∨ (p 2870) ∨ (¬ p 2807) ∨ (¬ p 2264) ∨ (p 2911) :=
  ElevenRUP.step121433 (p 2248) (p 2264) (p 2608) (p 2807) (p 2839) (p 2870) (p 2911) (p 4277) (derived105365 p h) (derived105380 p h) (derived86584 p h)

theorem derived121434 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 2839) ∨ (p 2870) ∨ (¬ p 2807) ∨ (¬ p 2449) ∨ (p 2608) :=
  ElevenRUP.step121434 (p 2248) (p 2396) (p 2449) (p 2608) (p 2807) (p 2839) (p 2870) (p 4559) (derived105365 p h) (derived105701 p h) (derived86588 p h)

theorem derived121440 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (p 3246) ∨ (¬ p 2241) ∨ (¬ p 2264) ∨ (p 2996) :=
  ElevenRUP.step121440 (p 2132) (p 2241) (p 2264) (p 2870) (p 2996) (p 3246) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived86597 p h)

theorem derived121441 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 3093) ∨ (p 3246) ∨ (¬ p 2363) ∨ (¬ p 3063) ∨ (p 2132) :=
  ElevenRUP.step121441 (p 2132) (p 2363) (p 2870) (p 3063) (p 3093) (p 3246) (p 4669) (p 4736) (derived105431 p h) (derived105415 p h) (derived86601 p h)

theorem derived121442 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2870) ∨ (¬ p 3309) ∨ (p 3246) ∨ (¬ p 3093) ∨ (¬ p 2177) :=
  ElevenRUP.step121442 (p 2132) (p 2177) (p 2870) (p 3093) (p 3246) (p 3309) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived86603 p h)

theorem derived121443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2352) ∨ (¬ p 4419) ∨ (p 2132) ∨ (p 3246) ∨ (¬ p 2363) ∨ (p 2870) :=
  ElevenRUP.step121443 (p 2132) (p 2352) (p 2363) (p 2573) (p 2870) (p 3246) (p 4419) (p 4669) (derived105415 p h) (derived86605 p h)

theorem derived121445 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 3083) ∨ (¬ p 2727) ∨ (¬ p 2241) ∨ (p 2881) ∨ (p 2132) :=
  ElevenRUP.step121445 (p 2132) (p 2241) (p 2727) (p 2870) (p 2881) (p 3083) (p 4420) (p 4736) (derived105431 p h) (derived105707 p h) (derived86619 p h)

theorem derived121446 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2651) ∨ (¬ p 2528) ∨ (¬ p 3083) ∨ (p 2132) ∨ (p 3246) :=
  ElevenRUP.step121446 (p 2132) (p 2528) (p 2651) (p 2870) (p 3083) (p 3246) (p 4669) (p 4786) (derived105415 p h) (derived106425 p h) (derived86621 p h)

theorem derived121447 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (p 2870) ∨ (p 2220) ∨ (¬ p 2619) ∨ (¬ p 2651) ∨ (¬ p 2553) ∨ (¬ p 3016) :=
  ElevenRUP.step121447 (p 2136) (p 2220) (p 2553) (p 2619) (p 2651) (p 2870) (p 3016) (p 4559) (p 4786) (derived105701 p h) (derived106425 p h) (derived86636 p h)

theorem derived121449 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 4283) ∨ (¬ p 4431) ∨ (p 2341) ∨ (¬ p 3527) :=
  ElevenRUP.step121449 (p 2341) (p 2870) (p 3527) (p 4283) (p 4431) (p 4878) (derived105452 p h) (derived86639 p h)

theorem derived121452 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2144) ∨ (¬ p 2241) ∨ (p 2870) ∨ (¬ p 2753) ∨ (¬ p 3051) ∨ (¬ p 2619) ∨ (¬ p 3923) :=
  ElevenRUP.step121452 (p 2144) (p 2241) (p 2619) (p 2750) (p 2753) (p 2870) (p 3051) (p 3093) (p 3923) (p 4433) (derived106345 p h) (derived106150 p h) (derived86649 p h)

theorem derived121455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2870) ∨ (p 2352) ∨ (¬ p 3051) ∨ (p 3379) ∨ (p 2493) ∨ (¬ p 4521) :=
  ElevenRUP.step121455 (p 2352) (p 2493) (p 2619) (p 2870) (p 3051) (p 3379) (p 4433) (p 4521) (derived106150 p h) (derived86652 p h)

theorem derived121456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2995) ∨ (p 3246) ∨ (p 2870) :=
  ElevenRUP.step121456 (p 2449) (p 2870) (p 2995) (p 3246) (p 4906) (derived105632 p h) (derived86654 p h)

theorem derived121457 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2619) ∨ (¬ p 4042) ∨ (p 3246) :=
  ElevenRUP.step121457 (p 2619) (p 2870) (p 3246) (p 4042) (p 4666) (derived105658 p h) (derived86655 p h)

theorem derived121460 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2619) ∨ (p 2373) ∨ (¬ p 3051) :=
  ElevenRUP.step121460 (p 2373) (p 2619) (p 2870) (p 3051) (p 4539) (derived105395 p h) (derived86661 p h)

theorem derived121461 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2870) ∨ (¬ p 3189) ∨ (¬ p 2241) ∨ (p 3246) ∨ (¬ p 3256) :=
  ElevenRUP.step121461 (p 2132) (p 2241) (p 2870) (p 3189) (p 3246) (p 3256) (p 4669) (p 4736) (derived105431 p h) (derived105415 p h) (derived86664 p h)

theorem derived121462 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2870) ∨ (¬ p 4419) ∨ (p 3016) ∨ (¬ p 2573) ∨ (p 2881) ∨ (¬ p 3083) :=
  ElevenRUP.step121462 (p 2132) (p 2573) (p 2870) (p 2881) (p 3016) (p 3083) (p 4419) (p 4420) (derived105707 p h) (derived86668 p h)

theorem derived121463 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2870) ∨ (¬ p 4079) ∨ (p 2363) ∨ (¬ p 2510) ∨ (p 2881) ∨ (¬ p 2528) ∨ (¬ p 2573) :=
  ElevenRUP.step121463 (p 2132) (p 2363) (p 2510) (p 2528) (p 2573) (p 2870) (p 2881) (p 4079) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived86669 p h)

theorem derived121464 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (¬ p 3379) ∨ (¬ p 2493) ∨ (¬ p 3564) ∨ (p 3246) :=
  ElevenRUP.step121464 (p 2132) (p 2493) (p 2870) (p 3246) (p 3379) (p 3564) (p 4621) (p 4736) (derived105431 p h) (derived105407 p h) (derived86671 p h)

theorem derived121465 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2518) ∨ (p 2132) ∨ (¬ p 3379) ∨ (¬ p 2528) ∨ (p 3246) :=
  ElevenRUP.step121465 (p 2132) (p 2518) (p 2528) (p 2870) (p 3246) (p 3379) (p 4669) (p 4736) (derived105431 p h) (derived105415 p h) (derived86674 p h)

theorem derived121468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2870) ∨ (¬ p 4042) ∨ (p 2177) :=
  ElevenRUP.step121468 (p 2177) (p 2619) (p 2870) (p 4042) (p 4559) (derived105701 p h) (derived86687 p h)

theorem derived121470 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2417) ∨ (p 2881) ∨ (p 2132) ∨ (¬ p 2922) ∨ (¬ p 3379) :=
  ElevenRUP.step121470 (p 2132) (p 2417) (p 2870) (p 2881) (p 2922) (p 3379) (p 4668) (p 4736) (derived105431 p h) (derived105414 p h) (derived86694 p h)

theorem derived121473 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (p 2241) ∨ (p 3246) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3366) :=
  ElevenRUP.step121473 (p 2132) (p 2241) (p 2744) (p 2870) (p 3073) (p 3246) (p 3366) (p 3449) (p 4669) (derived106503 p h) (derived105415 p h) (derived86701 p h)

theorem derived121476 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 3367) ∨ (¬ p 3759) ∨ (p 3246) ∨ (¬ p 3564) ∨ (p 2870) ∨ (¬ p 2573) :=
  ElevenRUP.step121476 (p 2132) (p 2573) (p 2870) (p 3246) (p 3367) (p 3564) (p 3759) (p 4621) (derived105407 p h) (derived86706 p h)

theorem derived121477 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (p 3016) ∨ (¬ p 3343) ∨ (¬ p 2573) ∨ (p 3246) ∨ (¬ p 4419) :=
  ElevenRUP.step121477 (p 2132) (p 2573) (p 2870) (p 3016) (p 3246) (p 3343) (p 4419) (p 4638) (derived105409 p h) (derived86707 p h)

theorem derived121478 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (p 2870) ∨ (¬ p 2341) ∨ (p 2156) ∨ (¬ p 2860) ∨ (p 3379) ∨ (¬ p 3366) ∨ (p 2911) ∨ (¬ p 3545) :=
  ElevenRUP.step121478 (p 2136) (p 2156) (p 2341) (p 2860) (p 2870) (p 2911) (p 3366) (p 3379) (p 3545) (p 4277) (p 4376) (derived106320 p h) (derived105380 p h) (derived86708 p h)

theorem derived121481 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (p 3246) ∨ (¬ p 3366) ∨ (¬ p 2246) :=
  ElevenRUP.step121481 (p 2132) (p 2246) (p 2331) (p 2363) (p 2668) (p 2744) (p 2870) (p 3246) (p 3366) (p 4669) (derived106503 p h) (derived105415 p h) (derived86715 p h)

theorem derived121482 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 2870) ∨ (¬ p 2427) :=
  ElevenRUP.step121482 (p 2427) (p 2440) (p 2870) (p 4750) (derived105433 p h) (derived86716 p h)

theorem derived121486 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (¬ p 2668) ∨ (¬ p 2641) ∨ (p 2881) ∨ (¬ p 2241) :=
  ElevenRUP.step121486 (p 2132) (p 2241) (p 2641) (p 2668) (p 2870) (p 2881) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived86735 p h)

theorem derived121488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2870) ∨ (¬ p 2651) ∨ (p 2727) ∨ (p 2996) ∨ (¬ p 2253) ∨ (p 2156) :=
  ElevenRUP.step121488 (p 2156) (p 2253) (p 2651) (p 2727) (p 2860) (p 2870) (p 2996) (p 4280) (derived105599 p h) (derived86738 p h)

theorem derived121489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4392) ∨ (p 2870) ∨ (¬ p 3051) ∨ (¬ p 2992) ∨ (¬ p 2951) :=
  ElevenRUP.step121489 (p 2751) (p 2870) (p 2951) (p 2992) (p 3051) (p 4392) (derived106343 p h) (derived86742 p h)

theorem derived121491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 4108) ∨ (¬ p 3051) ∨ (¬ p 2619) ∨ (¬ p 2493) ∨ (p 2573) ∨ (p 2870) ∨ (¬ p 4521) :=
  ElevenRUP.step121491 (p 2493) (p 2509) (p 2573) (p 2619) (p 2870) (p 3051) (p 4108) (p 4434) (p 4521) (derived106144 p h) (derived86747 p h)

theorem derived121492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2144) ∨ (p 3256) ∨ (p 2870) ∨ (¬ p 2363) ∨ (¬ p 3051) ∨ (¬ p 2753) ∨ (p 3166) ∨ (¬ p 2252) :=
  ElevenRUP.step121492 (p 2144) (p 2252) (p 2363) (p 2619) (p 2750) (p 2753) (p 2870) (p 3051) (p 3166) (p 3256) (p 4433) (derived106345 p h) (derived106150 p h) (derived86748 p h)

theorem derived121493 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 3093) ∨ (¬ p 2363) ∨ (¬ p 3051) ∨ (p 2870) ∨ (¬ p 2619) ∨ (¬ p 2144) ∨ (¬ p 4371) :=
  ElevenRUP.step121493 (p 2144) (p 2363) (p 2619) (p 2870) (p 3051) (p 3073) (p 3093) (p 4371) (p 4433) (p 4733) (derived105430 p h) (derived106150 p h) (derived86751 p h)

theorem derived121494 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 3083) ∨ (p 3246) ∨ (¬ p 2470) ∨ (¬ p 3366) ∨ (¬ p 2663) ∨ (¬ p 2246) ∨ (p 2132) ∨ (¬ p 3343) :=
  ElevenRUP.step121494 (p 2132) (p 2246) (p 2470) (p 2663) (p 2744) (p 2870) (p 3083) (p 3246) (p 3343) (p 3366) (p 4638) (derived106503 p h) (derived105409 p h) (derived86753 p h)

theorem derived121495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 4157) ∨ (¬ p 4079) ∨ (¬ p 2518) ∨ (p 2870) ∨ (p 2493) ∨ (p 2881) ∨ (p 2132) :=
  ElevenRUP.step121495 (p 2132) (p 2493) (p 2518) (p 2573) (p 2870) (p 2881) (p 4079) (p 4133) (p 4157) (p 4736) (derived105431 p h) (derived105712 p h) (derived86756 p h)

theorem derived121496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 2870) ∨ (p 2528) ∨ (¬ p 4450) ∨ (¬ p 3051) ∨ (p 2651) ∨ (p 3083) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 2252) :=
  ElevenRUP.step121496 (p 2252) (p 2528) (p 2651) (p 2750) (p 2870) (p 3051) (p 3083) (p 3105) (p 3370) (p 3371) (p 4450) (derived106345 p h) (derived86758 p h)

theorem derived121499 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 2870) ∨ (p 2363) ∨ (¬ p 3051) ∨ (¬ p 4450) ∨ (p 2331) ∨ (p 2668) ∨ (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2753) :=
  ElevenRUP.step121499 (p 2144) (p 2252) (p 2331) (p 2363) (p 2668) (p 2750) (p 2753) (p 2870) (p 3051) (p 3105) (p 4450) (derived106345 p h) (derived86763 p h)

theorem derived121500 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (¬ p 2144) ∨ (p 2870) ∨ (¬ p 3051) :=
  ElevenRUP.step121500 (p 2144) (p 2696) (p 2870) (p 3051) (p 5052) (derived105473 p h) (derived86765 p h)

theorem derived121501 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (¬ p 2911) ∨ (¬ p 3379) ∨ (¬ p 2922) ∨ (p 3246) :=
  ElevenRUP.step121501 (p 2132) (p 2870) (p 2911) (p 2922) (p 3246) (p 3379) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived86772 p h)

theorem derived121502 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (¬ p 3367) ∨ (p 3246) ∨ (p 2870) ∨ (¬ p 3389) ∨ (¬ p 3759) ∨ (¬ p 2911) :=
  ElevenRUP.step121502 (p 2132) (p 2870) (p 2911) (p 3246) (p 3367) (p 3389) (p 3759) (p 4666) (derived105658 p h) (derived86775 p h)

theorem derived121505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (p 2870) ∨ (¬ p 2563) :=
  ElevenRUP.step121505 (p 2156) (p 2563) (p 2870) (p 3051) (p 4882) (derived105453 p h) (derived86783 p h)

theorem derived121507 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2911) ∨ (p 2341) ∨ (¬ p 4283) ∨ (¬ p 3741) :=
  ElevenRUP.step121507 (p 2341) (p 2870) (p 2911) (p 3741) (p 4283) (p 4882) (derived105453 p h) (derived86786 p h)

theorem derived121508 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4283) ∨ (p 2870) ∨ (¬ p 2417) ∨ (¬ p 3741) ∨ (p 3516) :=
  ElevenRUP.step121508 (p 2417) (p 2870) (p 3516) (p 3741) (p 4283) (p 4882) (derived105453 p h) (derived86787 p h)

theorem derived121509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2363) ∨ (p 2870) ∨ (p 3246) ∨ (¬ p 2668) ∨ (p 2132) ∨ (¬ p 3873) :=
  ElevenRUP.step121509 (p 2132) (p 2248) (p 2331) (p 2363) (p 2668) (p 2870) (p 3246) (p 3873) (p 4669) (derived105365 p h) (derived105415 p h) (derived86790 p h)

theorem derived121512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (p 2870) ∨ (¬ p 3016) ∨ (p 3083) ∨ (¬ p 3051) ∨ (p 2493) :=
  ElevenRUP.step121512 (p 2144) (p 2493) (p 2619) (p 2753) (p 2870) (p 3016) (p 3051) (p 3083) (p 4434) (derived106144 p h) (derived86796 p h)

theorem derived121515 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2870) ∨ (¬ p 3083) ∨ (p 3246) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3366) ∨ (¬ p 2246) :=
  ElevenRUP.step121515 (p 2132) (p 2246) (p 2528) (p 2651) (p 2744) (p 2870) (p 3083) (p 3246) (p 3366) (p 4669) (derived106503 p h) (derived105415 p h) (derived86800 p h)

theorem derived121516 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (p 2241) ∨ (¬ p 3399) ∨ (p 3246) ∨ (¬ p 3527) ∨ (¬ p 3366) :=
  ElevenRUP.step121516 (p 2132) (p 2241) (p 2744) (p 2870) (p 3246) (p 3366) (p 3399) (p 3527) (p 4666) (derived106503 p h) (derived105658 p h) (derived86801 p h)

theorem derived121517 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2870) ∨ (¬ p 3051) ∨ (¬ p 4521) ∨ (¬ p 2619) ∨ (p 2241) ∨ (p 2727) :=
  ElevenRUP.step121517 (p 2241) (p 2619) (p 2727) (p 2870) (p 3051) (p 3083) (p 4434) (p 4521) (derived106144 p h) (derived86802 p h)

theorem derived121518 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (¬ p 2144) ∨ (¬ p 3051) ∨ (p 2870) :=
  ElevenRUP.step121518 (p 2144) (p 2598) (p 2870) (p 3051) (p 4884) (derived105454 p h) (derived86806 p h)

theorem derived121528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2341) ∨ (p 2417) ∨ (¬ p 2177) :=
  ElevenRUP.step121528 (p 2177) (p 2341) (p 2417) (p 3516) (p 4276) (derived105516 p h) (derived86838 p h)

theorem derived121532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2417) ∨ (¬ p 2881) ∨ (p 2341) :=
  ElevenRUP.step121532 (p 2341) (p 2417) (p 2881) (p 3516) (p 4277) (derived105380 p h) (derived86849 p h)

theorem derived121535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5201) ∨ (¬ p 3516) ∨ (p 2922) ∨ (p 2417) :=
  ElevenRUP.step121535 (p 2417) (p 2922) (p 3516) (p 5194) (p 5201) (derived105489 p h) (derived86870 p h)

theorem derived121536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2341) ∨ (¬ p 2177) ∨ (p 3246) :=
  ElevenRUP.step121536 (p 2177) (p 2341) (p 3246) (p 3516) (p 4556) (derived105399 p h) (derived86881 p h)

theorem derived121538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2341) ∨ (¬ p 4443) ∨ (p 3146) :=
  ElevenRUP.step121538 (p 2341) (p 3146) (p 3516) (p 4443) (p 4902) (derived105456 p h) (derived86885 p h)

theorem derived121540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 2319) ∨ (p 2396) ∨ (p 3309) :=
  ElevenRUP.step121540 (p 2319) (p 2396) (p 3309) (p 3516) (p 5022) (derived105470 p h) (derived86887 p h)

theorem derived121542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (p 2341) ∨ (p 2528) ∨ (¬ p 4443) :=
  ElevenRUP.step121542 (p 2341) (p 2528) (p 3516) (p 4420) (p 4443) (derived105707 p h) (derived86895 p h)

theorem derived121545 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 4066) ∨ (¬ p 2995) ∨ (p 3246) ∨ (p 2427) :=
  ElevenRUP.step121545 (p 2427) (p 2995) (p 3246) (p 3516) (p 4066) (p 4705) (derived106238 p h) (derived86905 p h)

theorem derived121546 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 4988) ∨ (p 3246) ∨ (p 2427) :=
  ElevenRUP.step121546 (p 2427) (p 3246) (p 3516) (p 4539) (p 4988) (derived105395 p h) (derived86906 p h)

theorem derived121553 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2143) ∨ (¬ p 4392) ∨ (¬ p 2901) ∨ (¬ p 2992) :=
  ElevenRUP.step121553 (p 2143) (p 2751) (p 2901) (p 2992) (p 3051) (p 4392) (derived106343 p h) (derived86925 p h)

theorem derived121554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 2619) ∨ (¬ p 4392) ∨ (p 3367) ∨ (¬ p 2166) :=
  ElevenRUP.step121554 (p 2166) (p 2619) (p 3367) (p 3371) (p 4392) (p 4749) (derived105432 p h) (derived86927 p h)

theorem derived121556 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3371) ∨ (p 3367) ∨ (¬ p 4392) ∨ (¬ p 2192) :=
  ElevenRUP.step121556 (p 2192) (p 2860) (p 3367) (p 3371) (p 4392) (p 4749) (derived105432 p h) (derived86929 p h)

theorem derived121557 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3399) ∨ (¬ p 2696) ∨ (¬ p 2177) ∨ (¬ p 2630) ∨ (¬ p 2437) :=
  ElevenRUP.step121557 (p 2177) (p 2437) (p 2630) (p 2696) (p 3399) (p 3527) (p 4276) (p 4733) (derived105430 p h) (derived105516 p h) (derived86930 p h)

theorem derived121559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2630) ∨ (p 2274) ∨ (p 2177) ∨ (¬ p 3083) ∨ (¬ p 2145) ∨ (p 2156) :=
  ElevenRUP.step121559 (p 2145) (p 2156) (p 2177) (p 2274) (p 2630) (p 2696) (p 3083) (p 4420) (derived105707 p h) (derived86937 p h)

theorem derived121560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 2274) ∨ (p 2307) ∨ (p 2187) ∨ (¬ p 4596) ∨ (¬ p 3083) :=
  ElevenRUP.step121560 (p 2187) (p 2274) (p 2307) (p 2630) (p 2696) (p 2787) (p 3083) (p 4596) (derived105374 p h) (derived86939 p h)

theorem derived121561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2145) ∨ (¬ p 2437) ∨ (p 2881) ∨ (¬ p 2177) ∨ (p 3051) ∨ (¬ p 2630) :=
  ElevenRUP.step121561 (p 2145) (p 2177) (p 2437) (p 2630) (p 2696) (p 2881) (p 3051) (p 4276) (derived105516 p h) (derived86940 p h)

theorem derived121563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 3093) ∨ (¬ p 2630) ∨ (p 3309) ∨ (¬ p 3343) ∨ (p 2396) :=
  ElevenRUP.step121563 (p 2396) (p 2630) (p 2696) (p 3093) (p 3309) (p 3343) (p 4638) (p 4733) (derived105430 p h) (derived105409 p h) (derived86942 p h)

theorem derived121567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3083) ∨ (p 3146) ∨ (¬ p 4596) ∨ (¬ p 2630) ∨ (p 2220) ∨ (¬ p 3645) ∨ (¬ p 2363) :=
  ElevenRUP.step121567 (p 2220) (p 2363) (p 2630) (p 2696) (p 2753) (p 3083) (p 3146) (p 3645) (p 4596) (p 4877) (derived105451 p h) (derived86952 p h)

theorem derived121568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2630) ∨ (p 3093) ∨ (¬ p 2437) ∨ (p 3309) ∨ (¬ p 2696) ∨ (¬ p 2753) :=
  ElevenRUP.step121568 (p 2210) (p 2437) (p 2630) (p 2696) (p 2753) (p 3093) (p 3309) (p 4276) (p 4877) (derived105516 p h) (derived105451 p h) (derived86953 p h)

theorem derived121571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2992) ∨ (¬ p 2946) ∨ (p 2651) :=
  ElevenRUP.step121571 (p 2630) (p 2651) (p 2745) (p 2946) (p 2992) (derived105523 p h) (derived86966 p h)

theorem derived121580 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 2651) ∨ (¬ p 2177) ∨ (¬ p 2630) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 4041) :=
  ElevenRUP.step121580 (p 2177) (p 2254) (p 2630) (p 2651) (p 3005) (p 3093) (p 3309) (p 4041) (derived105366 p h) (derived86990 p h)

theorem derived121581 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 4041) ∨ (¬ p 2891) ∨ (p 2651) ∨ (¬ p 2881) ∨ (¬ p 2630) ∨ (¬ p 2210) :=
  ElevenRUP.step121581 (p 2210) (p 2254) (p 2630) (p 2651) (p 2881) (p 2891) (p 3005) (p 4041) (derived105366 p h) (derived86993 p h)

theorem derived121586 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2630) ∨ (¬ p 2493) ∨ (¬ p 4389) :=
  ElevenRUP.step121586 (p 2493) (p 2630) (p 2797) (p 4389) (p 4814) (derived105440 p h) (derived87035 p h)

theorem derived121587 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2630) ∨ (¬ p 2573) ∨ (¬ p 4389) :=
  ElevenRUP.step121587 (p 2573) (p 2630) (p 2665) (p 2797) (p 4389) (derived105373 p h) (derived87037 p h)

theorem derived121593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 3402) ∨ (¬ p 2630) ∨ (¬ p 2470) ∨ (¬ p 2656) :=
  ElevenRUP.step121593 (p 2470) (p 2509) (p 2630) (p 2656) (p 2745) (p 3402) (derived105523 p h) (derived48258 p h)

theorem derived121595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 2220) ∨ (p 2807) ∨ (p 2264) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 4399) ∨ (p 2459) :=
  ElevenRUP.step121595 (p 2220) (p 2264) (p 2459) (p 2630) (p 2656) (p 2807) (p 3969) (p 4399) (p 5122) (derived105483 p h) (derived87072 p h)

theorem derived121598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2922) ∨ (¬ p 2437) ∨ (¬ p 3402) :=
  ElevenRUP.step121598 (p 2437) (p 2630) (p 2745) (p 2922) (p 3402) (derived105523 p h) (derived87089 p h)

theorem derived121605 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 3575) ∨ (¬ p 4155) ∨ (¬ p 2630) ∨ (¬ p 2922) :=
  ElevenRUP.step121605 (p 2630) (p 2685) (p 2922) (p 3575) (p 4155) (p 4814) (derived105440 p h) (derived87104 p h)

theorem derived121608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (p 2685) ∨ (¬ p 2553) :=
  ElevenRUP.step121608 (p 2553) (p 2685) (p 2797) (p 4973) (derived105835 p h) (derived87124 p h)

theorem derived121610 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2220) ∨ (p 2396) ∨ (p 2331) ∨ (p 2122) ∨ (¬ p 4395) ∨ (¬ p 3366) ∨ (¬ p 2982) ∨ (¬ p 4236) ∨ (¬ p 4399) ∨ (¬ p 4328) ∨ (¬ p 3519) :=
  ElevenRUP.step121610 (p 2122) (p 2220) (p 2331) (p 2373) (p 2396) (p 2982) (p 3366) (p 3519) (p 4236) (p 4328) (p 4376) (p 4395) (p 4399) (derived106320 p h) (derived87141 p h)

theorem derived121611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2630) ∨ (p 2696) ∨ (¬ p 4328) :=
  ElevenRUP.step121611 (p 2630) (p 2696) (p 2774) (p 4328) (p 4975) (derived105464 p h) (derived87143 p h)

theorem derived121613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 4328) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 3872) :=
  ElevenRUP.step121613 (p 2122) (p 2396) (p 3246) (p 3872) (p 4328) (p 4564) (derived105401 p h) (derived87153 p h)

theorem derived121614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3361) ∨ (¬ p 2829) ∨ (¬ p 4328) ∨ (p 2651) ∨ (p 2737) :=
  ElevenRUP.step121614 (p 2651) (p 2737) (p 2829) (p 3361) (p 4328) (p 4975) (derived105464 p h) (derived87163 p h)

theorem derived121620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4313) ∨ (p 2156) ∨ (¬ p 2860) ∨ (¬ p 2957) ∨ (p 2992) :=
  ElevenRUP.step121620 (p 2156) (p 2745) (p 2860) (p 2957) (p 2992) (p 4313) (derived105523 p h) (derived87188 p h)

theorem derived121621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (p 2383) ∨ (¬ p 2807) ∨ (¬ p 2668) ∨ (¬ p 3019) :=
  ElevenRUP.step121621 (p 2383) (p 2668) (p 2807) (p 3019) (p 3983) (p 4652) (derived105413 p h) (derived87213 p h)

theorem derived121639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2992) ∨ (¬ p 2241) ∨ (p 2528) ∨ (¬ p 2459) ∨ (p 2470) :=
  ElevenRUP.step121639 (p 2241) (p 2459) (p 2470) (p 2528) (p 2992) (p 3156) (p 4902) (p 5193) (derived105456 p h) (derived105488 p h) (derived87276 p h)

theorem derived121640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3453) ∨ (¬ p 2470) ∨ (p 3073) ∨ (¬ p 2528) :=
  ElevenRUP.step121640 (p 2470) (p 2528) (p 3073) (p 3453) (p 5194) (derived105489 p h) (derived87278 p h)

theorem derived121642 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 3073) ∨ (¬ p 3453) ∨ (¬ p 2528) :=
  ElevenRUP.step121642 (p 2406) (p 2528) (p 3073) (p 3453) (p 4608) (derived105540 p h) (derived87282 p h)

theorem derived121649 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (¬ p 3319) ∨ (¬ p 2386) ∨ (p 3654) ∨ (¬ p 2505) :=
  ElevenRUP.step121649 (p 2386) (p 2406) (p 2505) (p 3319) (p 3654) (p 4717) (derived105424 p h) (derived87296 p h)

theorem derived121651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2504) ∨ (p 4757) :=
  ElevenRUP.step121651 (p 2504) (p 4757) (p 4976) (derived105465 p h) (h 29318)

theorem derived121654 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2584) ∨ (¬ p 2307) ∨ (p 3016) ∨ (¬ p 2504) ∨ (p 3309) :=
  ElevenRUP.step121654 (p 2307) (p 2504) (p 2584) (p 2665) (p 3016) (p 3309) (derived105373 p h) (derived87305 p h)

theorem derived121658 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 3379) ∨ (¬ p 3093) :=
  ElevenRUP.step121658 (p 2406) (p 3093) (p 3379) (p 4717) (derived105424 p h) (derived87317 p h)

theorem derived121659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (p 3379) ∨ (¬ p 2504) ∨ (p 3016) :=
  ElevenRUP.step121659 (p 2504) (p 3016) (p 3093) (p 3379) (p 4814) (derived105440 p h) (derived87318 p h)

theorem derived121660 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 3379) ∨ (¬ p 3093) ∨ (¬ p 2504) :=
  ElevenRUP.step121660 (p 2504) (p 3093) (p 3379) (p 3422) (p 5217) (derived105493 p h) (derived87319 p h)

theorem derived121663 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2630) ∨ (¬ p 3402) ∨ (p 2493) :=
  ElevenRUP.step121663 (p 2493) (p 2573) (p 2630) (p 2656) (p 2745) (p 3402) (derived105523 p h) (derived87360 p h)

theorem derived121665 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2437) ∨ (¬ p 3402) ∨ (¬ p 2651) :=
  ElevenRUP.step121665 (p 2255) (p 2437) (p 2651) (p 2922) (p 3402) (derived105367 p h) (derived87365 p h)

theorem derived121669 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2230) ∨ (¬ p 3096) ∨ (¬ p 2427) :=
  ElevenRUP.step121669 (p 2230) (p 2427) (p 2573) (p 3096) (p 4558) (derived105400 p h) (derived87394 p h)

theorem derived121671 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 3096) :=
  ElevenRUP.step121671 (p 2230) (p 2573) (p 2982) (p 3096) (p 5046) (derived105472 p h) (derived87403 p h)

theorem derived121672 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3096) :=
  ElevenRUP.step121672 (p 2230) (p 2373) (p 2573) (p 3096) (p 4509) (derived105392 p h) (derived87404 p h)

theorem derived121673 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2284) ∨ (¬ p 2230) ∨ (¬ p 3096) :=
  ElevenRUP.step121673 (p 2230) (p 2284) (p 2573) (p 3096) (p 4705) (derived106238 p h) (derived87407 p h)

theorem derived121674 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2192) ∨ (¬ p 3096) ∨ (¬ p 2230) :=
  ElevenRUP.step121674 (p 2192) (p 2230) (p 2573) (p 3096) (p 4632) (derived106257 p h) (derived87408 p h)

theorem derived121682 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 2230) ∨ (¬ p 2373) :=
  ElevenRUP.step121682 (p 2230) (p 2373) (p 2470) (p 4434) (derived106144 p h) (derived87445 p h)

theorem derived121687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5197) ∨ (¬ p 2417) ∨ (p 3516) ∨ (¬ p 2230) :=
  ElevenRUP.step121687 (p 2230) (p 2417) (p 3516) (p 4644) (p 5197) (derived105411 p h) (derived87489 p h)

theorem derived121688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2577) ∨ (¬ p 2230) ∨ (¬ p 2352) ∨ (p 2383) :=
  ElevenRUP.step121688 (p 2230) (p 2352) (p 2383) (p 2577) (p 4715) (derived105423 p h) (derived87491 p h)

theorem derived121689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2577) ∨ (p 2307) ∨ (¬ p 2553) ∨ (¬ p 2230) :=
  ElevenRUP.step121689 (p 2230) (p 2307) (p 2553) (p 2577) (p 4715) (derived105423 p h) (derived87492 p h)

theorem derived121690 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 2737) ∨ (¬ p 2563) ∨ (¬ p 4774) ∨ (¬ p 2187) ∨ (p 2608) ∨ (¬ p 2230) :=
  ElevenRUP.step121690 (p 2187) (p 2230) (p 2563) (p 2608) (p 2737) (p 3005) (p 4774) (p 5190) (derived105487 p h) (derived87494 p h)

theorem derived121691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2577) ∨ (¬ p 3564) ∨ (p 3654) ∨ (¬ p 2230) :=
  ElevenRUP.step121691 (p 2230) (p 2577) (p 3564) (p 3654) (p 4715) (derived105423 p h) (derived87495 p h)

theorem derived121693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 4325) ∨ (p 2737) ∨ (p 2630) :=
  ElevenRUP.step121693 (p 2630) (p 2707) (p 2737) (p 4325) (p 4652) (derived105413 p h) (derived87507 p h)

theorem derived121696 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (p 2630) ∨ (¬ p 4325) ∨ (p 2696) :=
  ElevenRUP.step121696 (p 2630) (p 2696) (p 3425) (p 4325) (p 4652) (derived105413 p h) (derived87530 p h)

theorem derived121703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 2668) ∨ (p 2449) ∨ (¬ p 4067) ∨ (¬ p 2312) :=
  ElevenRUP.step121703 (p 2312) (p 2449) (p 2668) (p 3516) (p 4067) (p 4405) (derived105512 p h) (derived87560 p h)

theorem derived121704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (¬ p 2312) ∨ (¬ p 2493) ∨ (p 2922) ∨ (¬ p 2295) :=
  ElevenRUP.step121704 (p 2295) (p 2312) (p 2493) (p 2922) (p 4279) (p 4976) (derived105465 p h) (derived87561 p h)

theorem derived121705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2311) ∨ (¬ p 2553) ∨ (p 3516) ∨ (¬ p 2396) :=
  ElevenRUP.step121705 (p 2311) (p 2396) (p 2553) (p 2581) (p 3516) (derived105371 p h) (derived87563 p h)

theorem derived121708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2311) ∨ (p 5260) :=
  ElevenRUP.step121708 (p 2311) (p 2787) (p 5260) (derived105374 p h) (h 21376)

theorem derived121709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 3516) ∨ (¬ p 2396) ∨ (¬ p 2311) :=
  ElevenRUP.step121709 (p 2311) (p 2383) (p 2396) (p 3516) (p 4405) (derived105512 p h) (derived87571 p h)

theorem derived121712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2341) ∨ (¬ p 2311) ∨ (¬ p 2177) :=
  ElevenRUP.step121712 (p 2177) (p 2311) (p 2341) (p 3654) (p 4624) (derived105408 p h) (derived87582 p h)

theorem derived121720 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2651) ∨ (¬ p 2331) ∨ (¬ p 3984) :=
  ElevenRUP.step121720 (p 2331) (p 2651) (p 3422) (p 3984) (p 4750) (derived105433 p h) (derived87611 p h)

theorem derived121727 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 2166) ∨ (¬ p 3904) ∨ (¬ p 2573) ∨ (¬ p 4034) :=
  ElevenRUP.step121727 (p 2166) (p 2220) (p 2573) (p 3904) (p 4034) (p 4717) (derived105424 p h) (derived87644 p h)

theorem derived121734 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2577) ∨ (¬ p 3347) ∨ (¬ p 3487) ∨ (¬ p 2352) ∨ (¬ p 2449) ∨ (p 2630) ∨ (p 3564) ∨ (p 2996) ∨ (¬ p 2241) :=
  ElevenRUP.step121734 (p 2241) (p 2352) (p 2383) (p 2449) (p 2577) (p 2630) (p 2996) (p 3347) (p 3487) (p 3564) (p 4625) (derived106455 p h) (derived87662 p h)

theorem derived121738 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2493) ∨ (¬ p 3487) ∨ (¬ p 4241) ∨ (¬ p 2946) :=
  ElevenRUP.step121738 (p 2493) (p 2651) (p 2946) (p 3487) (p 4241) (p 4715) (derived105423 p h) (derived87676 p h)

theorem derived121743 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2307) ∨ (¬ p 3567) ∨ (¬ p 2641) ∨ (p 2417) ∨ (¬ p 3487) ∨ (p 2651) ∨ (¬ p 2177) :=
  ElevenRUP.step121743 (p 2177) (p 2249) (p 2307) (p 2417) (p 2641) (p 2651) (p 2922) (p 3487) (p 3567) (p 4666) (derived105658 p h) (derived106513 p h) (derived87684 p h)

theorem derived121749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4343) ∨ (¬ p 2850) ∨ (p 3093) ∨ (p 2363) ∨ (¬ p 2651) ∨ (¬ p 2982) ∨ (¬ p 3923) ∨ (¬ p 4450) :=
  ElevenRUP.step121749 (p 2248) (p 2363) (p 2651) (p 2850) (p 2982) (p 3093) (p 3923) (p 4343) (p 4450) (derived105365 p h) (derived87715 p h)

theorem derived121751 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3527) ∨ (¬ p 3905) ∨ (¬ p 2850) ∨ (¬ p 3399) ∨ (¬ p 4001) ∨ (p 2177) ∨ (p 2230) :=
  ElevenRUP.step121751 (p 2177) (p 2230) (p 2850) (p 3201) (p 3399) (p 3527) (p 3905) (p 4001) (p 4559) (p 4736) (derived105431 p h) (derived105701 p h) (derived87720 p h)

theorem derived121754 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2850) ∨ (¬ p 3399) ∨ (¬ p 4438) ∨ (p 2230) ∨ (¬ p 3527) ∨ (¬ p 3366) ∨ (p 2241) ∨ (¬ p 3905) :=
  ElevenRUP.step121754 (p 2230) (p 2241) (p 2744) (p 2850) (p 3366) (p 3399) (p 3527) (p 3641) (p 3905) (p 4438) (derived106503 p h) (derived87726 p h)

theorem derived121755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 2881) ∨ (p 2363) ∨ (¬ p 3923) ∨ (p 3093) ∨ (¬ p 2427) :=
  ElevenRUP.step121755 (p 2363) (p 2427) (p 2598) (p 2850) (p 2881) (p 3093) (p 3923) (p 4733) (derived105430 p h) (derived87727 p h)

theorem derived121759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 2373) ∨ (p 2307) ∨ (¬ p 2295) ∨ (p 2668) :=
  ElevenRUP.step121759 (p 2295) (p 2307) (p 2373) (p 2598) (p 2668) (p 2787) (p 2850) (p 4433) (derived106150 p h) (derived105374 p h) (derived87731 p h)

theorem derived121762 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2850) ∨ (¬ p 2383) ∨ (¬ p 2363) ∨ (p 2459) ∨ (¬ p 3693) ∨ (¬ p 3905) ∨ (p 2230) ∨ (¬ p 2781) :=
  ElevenRUP.step121762 (p 2230) (p 2363) (p 2383) (p 2459) (p 2781) (p 2850) (p 3641) (p 3693) (p 3905) (p 4905) (derived105995 p h) (derived87739 p h)

theorem derived121768 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2220) ∨ (¬ p 2850) ∨ (¬ p 3693) :=
  ElevenRUP.step121768 (p 2220) (p 2850) (p 3641) (p 3693) (p 4539) (derived105395 p h) (derived87775 p h)

theorem derived121769 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2850) ∨ (¬ p 4001) ∨ (¬ p 2373) ∨ (¬ p 3988) :=
  ElevenRUP.step121769 (p 2373) (p 2850) (p 3201) (p 3988) (p 4001) (p 4555) (derived105542 p h) (derived87780 p h)

theorem derived121773 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 2850) ∨ (¬ p 2598) ∨ (p 3527) ∨ (¬ p 2427) ∨ (¬ p 2177) :=
  ElevenRUP.step121773 (p 2177) (p 2427) (p 2598) (p 2850) (p 3399) (p 3527) (p 4556) (p 4733) (derived105430 p h) (derived105399 p h) (derived87786 p h)

theorem derived121775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (p 2992) ∨ (¬ p 2850) ∨ (¬ p 2727) ∨ (¬ p 4109) :=
  ElevenRUP.step121775 (p 2727) (p 2850) (p 2957) (p 2992) (p 4109) (p 4753) (derived105514 p h) (derived87802 p h)

theorem derived121779 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4106) ∨ (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 3425) :=
  ElevenRUP.step121779 (p 2598) (p 2850) (p 3425) (p 4106) (p 4644) (derived105411 p h) (derived61379 p h)

theorem derived121781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 2210) ∨ (¬ p 3379) ∨ (¬ p 4034) :=
  ElevenRUP.step121781 (p 2210) (p 2850) (p 3379) (p 4034) (p 5214) (derived105492 p h) (derived87820 p h)

theorem derived121785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4343) ∨ (¬ p 2651) ∨ (p 2459) ∨ (¬ p 4450) ∨ (p 2307) ∨ (p 2177) ∨ (¬ p 5015) ∨ (¬ p 2982) ∨ (¬ p 2850) :=
  ElevenRUP.step121785 (p 2177) (p 2248) (p 2307) (p 2459) (p 2651) (p 2850) (p 2982) (p 4343) (p 4450) (p 5015) (derived105365 p h) (derived87831 p h)

theorem derived121786 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2598) ∨ (¬ p 2982) ∨ (¬ p 4450) ∨ (p 2459) ∨ (p 3527) ∨ (p 3399) :=
  ElevenRUP.step121786 (p 2459) (p 2598) (p 2850) (p 2982) (p 3399) (p 3527) (p 4450) (p 4733) (derived105430 p h) (derived87832 p h)

theorem derived121788 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 5015) ∨ (¬ p 2982) ∨ (p 2307) ∨ (p 2177) ∨ (¬ p 4450) ∨ (¬ p 2850) ∨ (p 2459) :=
  ElevenRUP.step121788 (p 2177) (p 2307) (p 2459) (p 2598) (p 2850) (p 2982) (p 4450) (p 4733) (p 5015) (derived105430 p h) (derived87834 p h)

theorem derived121790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 2807) ∨ (¬ p 2598) ∨ (¬ p 2245) ∨ (p 2264) ∨ (p 2459) ∨ (¬ p 4450) ∨ (¬ p 2982) :=
  ElevenRUP.step121790 (p 2245) (p 2264) (p 2459) (p 2598) (p 2807) (p 2850) (p 2982) (p 4450) (p 4733) (derived105430 p h) (derived87836 p h)

theorem derived121793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2598) ∨ (p 2668) ∨ (¬ p 2982) ∨ (p 2331) ∨ (¬ p 2753) ∨ (p 2363) ∨ (¬ p 2252) ∨ (¬ p 4450) :=
  ElevenRUP.step121793 (p 2252) (p 2331) (p 2363) (p 2598) (p 2668) (p 2750) (p 2753) (p 2850) (p 2982) (p 4450) (derived106345 p h) (derived87853 p h)

theorem derived121795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4257) ∨ (¬ p 2737) ∨ (p 2406) ∨ (¬ p 2850) :=
  ElevenRUP.step121795 (p 2406) (p 2737) (p 2850) (p 4257) (p 4749) (derived105432 p h) (derived87863 p h)

theorem derived121796 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 4109) ∨ (p 2641) ∨ (¬ p 2667) ∨ (¬ p 2727) ∨ (¬ p 2962) :=
  ElevenRUP.step121796 (p 2641) (p 2667) (p 2727) (p 2850) (p 2962) (p 4109) (p 4753) (derived105514 p h) (derived87866 p h)

theorem derived121800 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3156) ∨ (¬ p 3693) ∨ (¬ p 2850) :=
  ElevenRUP.step121800 (p 2850) (p 3156) (p 3641) (p 3693) (p 4705) (derived106238 p h) (derived87873 p h)

theorem derived121801 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3693) ∨ (¬ p 3905) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (p 2230) ∨ (¬ p 2177) ∨ (¬ p 2850) :=
  ElevenRUP.step121801 (p 2177) (p 2230) (p 2295) (p 2331) (p 2850) (p 3641) (p 3693) (p 3905) (p 4786) (p 4905) (derived105995 p h) (derived106425 p h) (derived87876 p h)

theorem derived121805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4106) ∨ (p 2707) ∨ (¬ p 3367) ∨ (¬ p 2850) :=
  ElevenRUP.step121805 (p 2707) (p 2850) (p 3367) (p 4106) (p 4644) (derived105411 p h) (derived87882 p h)

theorem derived121807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 3422) ∨ (¬ p 3096) ∨ (¬ p 2284) :=
  ElevenRUP.step121807 (p 2284) (p 2850) (p 3096) (p 3422) (p 4705) (derived106238 p h) (derived87892 p h)

theorem derived121808 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2850) ∨ (¬ p 3096) ∨ (¬ p 2982) :=
  ElevenRUP.step121808 (p 2850) (p 2982) (p 3096) (p 3422) (p 5046) (derived105472 p h) (derived87893 p h)

theorem derived121809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 3422) ∨ (¬ p 3096) ∨ (¬ p 2156) ∨ (¬ p 3370) :=
  ElevenRUP.step121809 (p 2156) (p 2850) (p 3096) (p 3370) (p 3422) (p 4632) (derived106257 p h) (derived87894 p h)

theorem derived121810 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2850) ∨ (¬ p 3096) ∨ (¬ p 2373) :=
  ElevenRUP.step121810 (p 2373) (p 2850) (p 3096) (p 3422) (p 4509) (derived105392 p h) (derived87895 p h)

theorem derived121811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 3201) ∨ (¬ p 2891) ∨ (¬ p 4001) :=
  ElevenRUP.step121811 (p 2850) (p 2891) (p 3201) (p 4001) (p 4632) (derived106257 p h) (derived87896 p h)

theorem derived121813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4343) ∨ (p 2437) ∨ (¬ p 3366) ∨ (¬ p 3905) ∨ (¬ p 2850) ∨ (p 3093) ∨ (¬ p 2341) ∨ (¬ p 3545) ∨ (p 3527) ∨ (p 2230) :=
  ElevenRUP.step121813 (p 2230) (p 2341) (p 2437) (p 2850) (p 2930) (p 3093) (p 3366) (p 3527) (p 3545) (p 3905) (p 4343) (p 4866) (derived106063 p h) (derived105376 p h) (derived87898 p h)

theorem derived121820 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3683) ∨ (¬ p 3309) ∨ (¬ p 2177) ∨ (p 2417) ∨ (p 2651) ∨ (¬ p 3093) :=
  ElevenRUP.step121820 (p 2177) (p 2254) (p 2417) (p 2651) (p 3093) (p 3201) (p 3309) (p 3683) (p 4666) (derived105366 p h) (derived105658 p h) (derived87920 p h)

theorem derived121824 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (¬ p 3905) ∨ (p 2177) ∨ (p 2573) ∨ (p 2241) ∨ (¬ p 3037) ∨ (¬ p 3366) ∨ (p 2122) ∨ (¬ p 2449) ∨ (¬ p 4390) :=
  ElevenRUP.step121824 (p 2122) (p 2177) (p 2241) (p 2449) (p 2573) (p 2744) (p 3037) (p 3366) (p 3399) (p 3905) (p 4390) (p 4668) (derived106503 p h) (derived105414 p h) (derived87948 p h)

theorem derived121826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4390) ∨ (p 4889) :=
  ElevenRUP.step121826 (p 3958) (p 4390) (p 4889) (derived105378 p h) (h 25032)

theorem derived121828 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2850) ∨ (¬ p 4390) ∨ (p 3367) :=
  ElevenRUP.step121828 (p 2829) (p 2850) (p 3367) (p 4390) (p 4717) (derived105424 p h) (derived87960 p h)

theorem derived121830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 4390) ∨ (p 2598) ∨ (p 2493) :=
  ElevenRUP.step121830 (p 2493) (p 2598) (p 2774) (p 4390) (p 5214) (derived105492 p h) (derived87964 p h)

theorem derived121831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2850) ∨ (¬ p 4390) ∨ (p 2598) :=
  ElevenRUP.step121831 (p 2598) (p 2774) (p 2850) (p 4390) (p 4717) (derived105424 p h) (derived87965 p h)

theorem derived121832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2850) ∨ (¬ p 3366) ∨ (p 2598) ∨ (¬ p 4390) :=
  ElevenRUP.step121832 (p 2598) (p 2829) (p 2850) (p 3366) (p 4390) (p 4717) (derived105424 p h) (derived87966 p h)

theorem derived121834 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4390) ∨ (¬ p 2590) ∨ (p 2819) ∨ (¬ p 2192) ∨ (¬ p 2187) :=
  ElevenRUP.step121834 (p 2187) (p 2192) (p 2590) (p 2819) (p 4390) (p 4632) (derived106257 p h) (derived87969 p h)

theorem derived121854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3543) ∨ (p 2177) ∨ (¬ p 2341) ∨ (p 3276) ∨ (¬ p 2396) ∨ (¬ p 3347) ∨ (¬ p 3346) ∨ (¬ p 4257) :=
  ElevenRUP.step121854 (p 2177) (p 2341) (p 2396) (p 3276) (p 3346) (p 3347) (p 3543) (p 3680) (p 3951) (p 4257) (p 4793) (derived105438 p h) (derived106536 p h) (derived88051 p h)

theorem derived121856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2577) ∨ (p 5021) :=
  ElevenRUP.step121856 (p 2577) (p 5021) (p 5193) (derived105488 p h) (h 24506)

theorem derived121857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2241) ∨ (¬ p 2459) ∨ (p 2470) ∨ (p 2528) :=
  ElevenRUP.step121857 (p 2241) (p 2459) (p 2470) (p 2528) (p 2641) (p 2668) (p 4133) (p 5193) (derived105488 p h) (derived105712 p h) (derived88071 p h)

theorem derived121858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (p 3564) ∨ (p 3461) ∨ (p 2573) ∨ (¬ p 3189) ∨ (¬ p 2241) ∨ (¬ p 5119) :=
  ElevenRUP.step121858 (p 2241) (p 2573) (p 3189) (p 3461) (p 3564) (p 4009) (p 5119) (p 5193) (derived105488 p h) (derived88072 p h)

theorem derived121860 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (p 2573) ∨ (p 2363) ∨ (¬ p 2449) ∨ (p 2352) ∨ (¬ p 2241) ∨ (¬ p 3950) :=
  ElevenRUP.step121860 (p 2241) (p 2352) (p 2363) (p 2449) (p 2573) (p 2996) (p 3950) (p 5193) (derived105488 p h) (derived88074 p h)

theorem derived121862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (p 2230) ∨ (¬ p 3830) ∨ (p 3266) ∨ (p 2427) ∨ (p 3246) :=
  ElevenRUP.step121862 (p 2230) (p 2427) (p 3246) (p 3266) (p 3707) (p 3830) (p 4669) (p 5193) (derived105488 p h) (derived105415 p h) (derived88078 p h)

theorem derived121864 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2241) ∨ (¬ p 2630) ∨ (p 2911) ∨ (p 3389) ∨ (p 2459) ∨ (¬ p 2641) :=
  ElevenRUP.step121864 (p 2241) (p 2459) (p 2630) (p 2641) (p 2797) (p 2911) (p 3389) (p 5193) (derived105488 p h) (derived88081 p h)

theorem derived121865 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2946) ∨ (p 2406) ∨ (¬ p 4241) :=
  ElevenRUP.step121865 (p 2406) (p 2651) (p 2946) (p 4241) (p 4811) (derived105633 p h) (derived88082 p h)

theorem derived121866 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 2284) ∨ (¬ p 3413) ∨ (p 2406) ∨ (¬ p 4031) :=
  ElevenRUP.step121866 (p 2156) (p 2284) (p 2406) (p 3413) (p 4031) (p 4811) (derived105633 p h) (derived88083 p h)

theorem derived121875 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2651) ∨ (¬ p 5020) ∨ (p 3309) ∨ (p 2528) ∨ (¬ p 2307) ∨ (¬ p 3319) :=
  ElevenRUP.step121875 (p 2254) (p 2307) (p 2528) (p 2651) (p 3083) (p 3309) (p 3319) (p 4330) (p 5020) (derived105366 p h) (derived106329 p h) (derived88116 p h)

theorem derived121877 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2651) ∨ (¬ p 2608) ∨ (¬ p 3483) ∨ (¬ p 2829) ∨ (p 2528) :=
  ElevenRUP.step121877 (p 2254) (p 2528) (p 2608) (p 2651) (p 2829) (p 3083) (p 3483) (p 4330) (derived105366 p h) (derived106329 p h) (derived88118 p h)

theorem derived121878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3115) ∨ (p 2946) ∨ (¬ p 3093) ∨ (¬ p 4322) ∨ (¬ p 3309) :=
  ElevenRUP.step121878 (p 2254) (p 2946) (p 3093) (p 3115) (p 3309) (p 3791) (p 4322) (p 4826) (derived105366 p h) (derived105444 p h) (derived88119 p h)

theorem derived121881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4404) ∨ (¬ p 3083) ∨ (p 2881) ∨ (p 2437) :=
  ElevenRUP.step121881 (p 2437) (p 2881) (p 3083) (p 4404) (p 4647) (derived105412 p h) (derived88133 p h)

theorem derived121883 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2662) ∨ (p 2177) ∨ (¬ p 3083) ∨ (¬ p 4404) :=
  ElevenRUP.step121883 (p 2177) (p 2662) (p 3083) (p 3389) (p 4404) (p 4712) (derived105422 p h) (derived88137 p h)

theorem derived121886 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3527) ∨ (¬ p 5197) ∨ (¬ p 3363) ∨ (¬ p 3687) ∨ (p 2737) :=
  ElevenRUP.step121886 (p 2341) (p 2737) (p 3363) (p 3527) (p 3687) (p 4752) (p 5197) (derived105434 p h) (derived88146 p h)

theorem derived121888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 2210) ∨ (¬ p 5206) ∨ (p 3516) :=
  ElevenRUP.step121888 (p 2210) (p 3516) (p 3631) (p 3687) (p 4877) (p 5206) (derived105451 p h) (derived88149 p h)

theorem derived121891 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5206) ∨ (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 2241) ∨ (p 3516) :=
  ElevenRUP.step121891 (p 2241) (p 2750) (p 3516) (p 3631) (p 3687) (p 5206) (derived106345 p h) (derived88155 p h)

theorem derived121894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 4870) ∨ (¬ p 3204) ∨ (¬ p 3379) ∨ (p 2363) ∨ (¬ p 2459) ∨ (p 2608) ∨ (p 2383) :=
  ElevenRUP.step121894 (p 2363) (p 2383) (p 2459) (p 2518) (p 2608) (p 3204) (p 3379) (p 4420) (p 4870) (derived105707 p h) (derived88164 p h)

theorem derived121902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2498) ∨ (p 2850) ∨ (¬ p 2497) ∨ (¬ p 2573) ∨ (¬ p 2406) :=
  ElevenRUP.step121902 (p 2406) (p 2497) (p 2498) (p 2573) (p 2850) (p 4730) (derived106074 p h) (derived88185 p h)

theorem derived121906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2497) ∨ (¬ p 2553) ∨ (p 3309) ∨ (¬ p 2573) :=
  ElevenRUP.step121906 (p 2497) (p 2553) (p 2573) (p 3309) (p 5194) (derived105489 p h) (derived88191 p h)

theorem derived121909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (¬ p 3031) ∨ (¬ p 5201) ∨ (¬ p 2641) ∨ (p 3527) ∨ (¬ p 2341) :=
  ElevenRUP.step121909 (p 2341) (p 2641) (p 2656) (p 3031) (p 3527) (p 4975) (p 5201) (derived105464 p h) (derived88218 p h)

theorem derived121913 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3031) ∨ (¬ p 2807) ∨ (¬ p 2264) :=
  ElevenRUP.step121913 (p 2255) (p 2264) (p 2807) (p 3031) (p 3527) (derived105367 p h) (derived88242 p h)

theorem derived121915 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (¬ p 3367) ∨ (p 2696) :=
  ElevenRUP.step121915 (p 2696) (p 2707) (p 3367) (p 3425) (p 4752) (derived105434 p h) (derived88251 p h)

theorem derived121916 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 4777) ∨ (¬ p 2807) ∨ (¬ p 2737) :=
  ElevenRUP.step121916 (p 2707) (p 2737) (p 2807) (p 4777) (p 4790) (derived106424 p h) (derived88255 p h)

theorem derived121917 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 2210) ∨ (¬ p 3589) :=
  ElevenRUP.step121917 (p 2210) (p 2707) (p 3425) (p 3589) (p 4377) (derived106170 p h) (derived88268 p h)

theorem derived121918 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (p 2946) ∨ (¬ p 3537) ∨ (p 2187) ∨ (¬ p 4859) ∨ (p 2707) ∨ (¬ p 3589) ∨ (p 2284) :=
  ElevenRUP.step121918 (p 2187) (p 2254) (p 2284) (p 2707) (p 2946) (p 3425) (p 3537) (p 3589) (p 4859) (derived105366 p h) (derived88269 p h)

theorem derived121920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4153) ∨ (p 2946) ∨ (p 2295) ∨ (p 2707) ∨ (¬ p 4889) ∨ (¬ p 2274) ∨ (p 3425) ∨ (¬ p 3589) ∨ (¬ p 2829) :=
  ElevenRUP.step121920 (p 2254) (p 2274) (p 2295) (p 2707) (p 2829) (p 2946) (p 3425) (p 3589) (p 4153) (p 4889) (derived105366 p h) (derived88282 p h)

theorem derived121923 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 2651) ∨ (p 2608) ∨ (¬ p 2528) ∨ (¬ p 3083) ∨ (p 2707) :=
  ElevenRUP.step121923 (p 2248) (p 2528) (p 2608) (p 2651) (p 2707) (p 3083) (p 3434) (p 4669) (derived105365 p h) (derived105415 p h) (derived88291 p h)

theorem derived121924 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2668) ∨ (¬ p 2331) ∨ (p 3434) ∨ (p 2608) ∨ (¬ p 2363) :=
  ElevenRUP.step121924 (p 2248) (p 2331) (p 2363) (p 2608) (p 2668) (p 2707) (p 3434) (p 4669) (derived105365 p h) (derived105415 p h) (derived88292 p h)

theorem derived121931 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3434) ∨ (¬ p 2573) ∨ (¬ p 2363) ∨ (p 2608) ∨ (¬ p 2352) :=
  ElevenRUP.step121931 (p 2352) (p 2363) (p 2573) (p 2608) (p 2707) (p 3434) (p 4669) (p 5190) (derived105415 p h) (derived105487 p h) (derived88307 p h)

theorem derived121934 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2373) ∨ (p 2440) ∨ (p 2717) ∨ (¬ p 2651) ∨ (p 2608) :=
  ElevenRUP.step121934 (p 2248) (p 2373) (p 2440) (p 2608) (p 2651) (p 2707) (p 2717) (p 4902) (derived105365 p h) (derived105456 p h) (derived88312 p h)

theorem derived121935 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2230) ∨ (¬ p 2187) ∨ (p 2707) ∨ (¬ p 2563) ∨ (p 2608) :=
  ElevenRUP.step121935 (p 2187) (p 2230) (p 2563) (p 2608) (p 2707) (p 2717) (p 4133) (p 5190) (derived105712 p h) (derived105487 p h) (derived88322 p h)

theorem derived121943 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3434) ∨ (¬ p 3156) ∨ (p 2608) ∨ (¬ p 3146) ∨ (¬ p 2946) :=
  ElevenRUP.step121943 (p 2248) (p 2608) (p 2707) (p 2946) (p 3146) (p 3156) (p 3434) (p 4669) (derived105365 p h) (derived105415 p h) (derived88347 p h)

theorem derived121944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4106) ∨ (p 2707) ∨ (¬ p 3367) ∨ (¬ p 2437) :=
  ElevenRUP.step121944 (p 2437) (p 2707) (p 3367) (p 4106) (p 4750) (derived105433 p h) (derived88349 p h)

theorem derived121949 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 2241) ∨ (¬ p 3589) :=
  ElevenRUP.step121949 (p 2241) (p 2707) (p 2744) (p 3425) (p 3589) (derived106503 p h) (derived88381 p h)

theorem derived121950 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (p 2707) ∨ (p 2608) ∨ (¬ p 3146) ∨ (¬ p 2230) ∨ (¬ p 2373) :=
  ElevenRUP.step121950 (p 2230) (p 2373) (p 2608) (p 2707) (p 3146) (p 3434) (p 4669) (p 5190) (derived105415 p h) (derived105487 p h) (derived88389 p h)

theorem derived121951 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 2707) ∨ (p 2363) ∨ (¬ p 2510) ∨ (p 2717) ∨ (p 2608) ∨ (¬ p 2528) :=
  ElevenRUP.step121951 (p 2363) (p 2510) (p 2528) (p 2573) (p 2608) (p 2707) (p 2717) (p 4133) (p 5190) (derived105712 p h) (derived105487 p h) (derived88404 p h)

theorem derived121953 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (p 2707) ∨ (p 2608) ∨ (¬ p 2295) ∨ (¬ p 2177) ∨ (¬ p 2331) :=
  ElevenRUP.step121953 (p 2177) (p 2248) (p 2295) (p 2331) (p 2608) (p 2707) (p 3434) (p 4666) (derived105365 p h) (derived105658 p h) (derived88414 p h)

theorem derived121957 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2098) ∨ (¬ p 3873) ∨ (¬ p 2807) ∨ (p 3246) ∨ (¬ p 3537) ∨ (¬ p 2449) :=
  ElevenRUP.step121957 (p 2098) (p 2248) (p 2449) (p 2707) (p 2807) (p 3246) (p 3537) (p 3873) (p 4898) (derived105365 p h) (derived105455 p h) (derived88428 p h)

theorem derived121958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3537) ∨ (p 2098) ∨ (p 2440) ∨ (¬ p 3873) ∨ (¬ p 2427) ∨ (p 2707) ∨ (¬ p 2651) :=
  ElevenRUP.step121958 (p 2098) (p 2248) (p 2427) (p 2440) (p 2651) (p 2707) (p 3537) (p 3873) (p 4898) (derived105365 p h) (derived105455 p h) (derived88431 p h)

theorem derived121959 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2608) ∨ (¬ p 3016) ∨ (p 2717) ∨ (¬ p 2651) ∨ (¬ p 2352) :=
  ElevenRUP.step121959 (p 2248) (p 2352) (p 2608) (p 2651) (p 2707) (p 2717) (p 3016) (p 4133) (derived105365 p h) (derived105712 p h) (derived88432 p h)

theorem derived121960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3276) ∨ (p 2707) ∨ (p 3366) ∨ (¬ p 2651) ∨ (¬ p 2811) ∨ (¬ p 2132) ∨ (¬ p 4423) :=
  ElevenRUP.step121960 (p 2132) (p 2651) (p 2707) (p 2811) (p 3276) (p 3343) (p 3366) (p 4423) (p 4831) (p 5052) (derived105473 p h) (derived105445 p h) (derived88435 p h)

theorem derived121967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (p 2707) ∨ (p 2608) ∨ (p 2363) ∨ (¬ p 2528) ∨ (p 2717) :=
  ElevenRUP.step121967 (p 2363) (p 2470) (p 2528) (p 2608) (p 2707) (p 2717) (p 4133) (p 5190) (derived105712 p h) (derived105487 p h) (derived88454 p h)

theorem derived121974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3361) ∨ (p 2449) ∨ (¬ p 2891) ∨ (p 2807) ∨ (¬ p 2881) ∨ (p 2737) ∨ (¬ p 4418) :=
  ElevenRUP.step121974 (p 2132) (p 2449) (p 2737) (p 2807) (p 2881) (p 2891) (p 3361) (p 4418) (p 4666) (derived105658 p h) (derived88502 p h)

theorem derived121975 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2331) ∨ (p 2737) ∨ (¬ p 4418) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 3361) ∨ (p 3323) :=
  ElevenRUP.step121975 (p 2132) (p 2331) (p 2737) (p 2891) (p 3246) (p 3323) (p 3361) (p 4418) (p 4625) (derived106455 p h) (derived88503 p h)

theorem derived121976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 5164) ∨ (p 2807) ∨ (p 2598) ∨ (¬ p 3361) ∨ (p 2264) ∨ (¬ p 3619) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step121976 (p 2264) (p 2598) (p 2807) (p 3276) (p 3361) (p 3619) (p 4749) (p 5123) (p 5164) (p 5558) (derived105432 p h) (derived88511 p h)

theorem derived121980 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 3361) ∨ (¬ p 3683) ∨ (¬ p 3367) ∨ (p 2737) :=
  ElevenRUP.step121980 (p 2737) (p 3166) (p 3361) (p 3367) (p 3683) (p 5008) (derived105469 p h) (derived88530 p h)

theorem derived121982 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3361) ∨ (¬ p 2749) ∨ (p 3367) ∨ (¬ p 2992) ∨ (p 2946) :=
  ElevenRUP.step121982 (p 2749) (p 2946) (p 2992) (p 3361) (p 3367) (p 4749) (derived105432 p h) (derived88548 p h)

theorem derived121983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3425) ∨ (¬ p 2707) ∨ (p 2737) :=
  ElevenRUP.step121983 (p 2132) (p 2707) (p 2737) (p 3425) (p 5052) (derived105473 p h) (derived88553 p h)

theorem derived121984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4169) ∨ (¬ p 3425) ∨ (¬ p 2860) ∨ (¬ p 2132) :=
  ElevenRUP.step121984 (p 2132) (p 2860) (p 3425) (p 4169) (p 4555) (derived105542 p h) (derived41110 p h)

theorem derived121987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3425) ∨ (¬ p 2241) ∨ (¬ p 3873) :=
  ElevenRUP.step121987 (p 2241) (p 2707) (p 2750) (p 3425) (p 3873) (derived106345 p h) (derived42585 p h)

theorem derived121988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4169) ∨ (¬ p 3425) ∨ (¬ p 2132) ∨ (¬ p 2901) :=
  ElevenRUP.step121988 (p 2132) (p 2901) (p 3425) (p 4169) (p 4906) (derived105632 p h) (derived42287 p h)

theorem derived121989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4169) ∨ (¬ p 3425) ∨ (¬ p 2427) ∨ (¬ p 2132) :=
  ElevenRUP.step121989 (p 2132) (p 2427) (p 3425) (p 4169) (p 4882) (derived105453 p h) (derived50563 p h)

theorem derived121990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4169) ∨ (¬ p 3425) ∨ (¬ p 2891) ∨ (¬ p 2132) :=
  ElevenRUP.step121990 (p 2132) (p 2891) (p 3425) (p 4169) (p 4878) (derived105452 p h) (derived50050 p h)

theorem derived121992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 2696) ∨ (p 2996) ∨ (¬ p 4777) :=
  ElevenRUP.step121992 (p 2696) (p 2751) (p 2996) (p 3425) (p 4777) (derived106343 p h) (derived88569 p h)

theorem derived121996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3576) ∨ (¬ p 3425) ∨ (¬ p 2811) ∨ (p 3527) ∨ (p 2459) ∨ (¬ p 2331) ∨ (¬ p 2737) ∨ (¬ p 3323) :=
  ElevenRUP.step121996 (p 2331) (p 2459) (p 2737) (p 2811) (p 3323) (p 3425) (p 3527) (p 3576) (p 4330) (derived106329 p h) (derived88577 p h)

theorem derived122006 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3093) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (p 2241) ∨ (¬ p 3922) ∨ (¬ p 3323) ∨ (p 2459) :=
  ElevenRUP.step122006 (p 2241) (p 2459) (p 2717) (p 2744) (p 3093) (p 3323) (p 3366) (p 3425) (p 3922) (p 4330) (derived106503 p h) (derived106329 p h) (derived88597 p h)

theorem derived122010 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 2992) ∨ (¬ p 2253) ∨ (¬ p 2946) ∨ (p 2996) ∨ (¬ p 3425) ∨ (¬ p 2177) :=
  ElevenRUP.step122010 (p 2177) (p 2253) (p 2717) (p 2946) (p 2992) (p 2996) (p 3425) (p 4736) (derived105431 p h) (derived88607 p h)

theorem derived122015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (p 2459) ∨ (p 2717) ∨ (¬ p 3323) :=
  ElevenRUP.step122015 (p 2241) (p 2459) (p 2641) (p 2717) (p 3323) (p 3425) (p 4330) (p 4736) (derived105431 p h) (derived106329 p h) (derived88615 p h)

theorem derived122017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 2493) ∨ (¬ p 3379) ∨ (p 2717) ∨ (¬ p 3425) ∨ (p 2459) :=
  ElevenRUP.step122017 (p 2459) (p 2493) (p 2717) (p 3379) (p 3425) (p 3564) (p 4330) (p 4736) (derived105431 p h) (derived106329 p h) (derived88622 p h)

theorem derived122021 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3379) ∨ (¬ p 4450) ∨ (¬ p 2982) ∨ (¬ p 3425) ∨ (p 2459) ∨ (¬ p 2406) :=
  ElevenRUP.step122021 (p 2406) (p 2459) (p 2717) (p 2982) (p 3379) (p 3425) (p 4450) (p 4736) (derived105431 p h) (derived88630 p h)

theorem derived122022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (¬ p 2230) ∨ (p 2459) ∨ (¬ p 2563) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 3519) :=
  ElevenRUP.step122022 (p 2230) (p 2459) (p 2563) (p 2717) (p 3125) (p 3366) (p 3425) (p 3519) (p 4330) (p 4376) (derived106320 p h) (derived106329 p h) (derived88633 p h)

theorem derived122025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (p 2717) ∨ (¬ p 5123) ∨ (¬ p 3323) ∨ (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 5558) ∨ (¬ p 2331) ∨ (¬ p 3461) :=
  ElevenRUP.step122025 (p 2246) (p 2331) (p 2717) (p 2744) (p 3323) (p 3366) (p 3425) (p 3461) (p 5123) (p 5558) (derived106503 p h) (derived88641 p h)

theorem derived122028 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 3516) ∨ (¬ p 3873) ∨ (¬ p 3425) :=
  ElevenRUP.step122028 (p 3425) (p 3434) (p 3516) (p 3873) (p 5207) (derived105491 p h) (derived88645 p h)

theorem derived122030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 2156) ∨ (p 2717) ∨ (p 2459) ∨ (p 2284) ∨ (¬ p 2958) ∨ (¬ p 3115) ∨ (¬ p 2246) ∨ (¬ p 5045) :=
  ElevenRUP.step122030 (p 2156) (p 2246) (p 2284) (p 2459) (p 2717) (p 2744) (p 2958) (p 3115) (p 3366) (p 3425) (p 4330) (p 5045) (derived106503 p h) (derived106329 p h) (derived88650 p h)

theorem derived122034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 3083) ∨ (¬ p 2470) ∨ (p 3434) ∨ (p 2210) ∨ (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 3343) :=
  ElevenRUP.step122034 (p 2210) (p 2470) (p 3083) (p 3343) (p 3366) (p 3371) (p 3425) (p 3434) (p 4638) (p 5190) (derived105487 p h) (derived105409 p h) (derived88661 p h)

theorem derived122035 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (¬ p 2246) ∨ (¬ p 2881) ∨ (¬ p 2553) ∨ (¬ p 2651) ∨ (¬ p 3366) ∨ (¬ p 3016) :=
  ElevenRUP.step122035 (p 2246) (p 2553) (p 2651) (p 2717) (p 2744) (p 2881) (p 3016) (p 3366) (p 3425) (p 4559) (derived106503 p h) (derived105701 p h) (derived88662 p h)

theorem derived122036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (p 2459) ∨ (¬ p 3564) :=
  ElevenRUP.step122036 (p 2459) (p 2651) (p 2717) (p 3016) (p 3425) (p 3564) (p 4330) (p 4786) (derived106425 p h) (derived106329 p h) (derived88665 p h)

theorem derived122037 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (p 3016) ∨ (¬ p 4332) ∨ (¬ p 2663) ∨ (¬ p 3343) ∨ (¬ p 2573) ∨ (p 2459) :=
  ElevenRUP.step122037 (p 2459) (p 2573) (p 2663) (p 2717) (p 3016) (p 3343) (p 3425) (p 4332) (p 4786) (derived106425 p h) (derived88666 p h)

theorem derived122040 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 2707) ∨ (¬ p 3873) ∨ (¬ p 2156) ∨ (¬ p 4746) ∨ (¬ p 3156) ∨ (¬ p 4399) ∨ (p 2284) ∨ (¬ p 3425) :=
  ElevenRUP.step122040 (p 2156) (p 2284) (p 2707) (p 3156) (p 3425) (p 3537) (p 3873) (p 4399) (p 4746) (p 5190) (derived105487 p h) (derived88669 p h)

theorem derived122048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5558) ∨ (¬ p 2230) ∨ (¬ p 3425) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (p 2717) ∨ (¬ p 4419) :=
  ElevenRUP.step122048 (p 2230) (p 2373) (p 2717) (p 3146) (p 3425) (p 4419) (p 5118) (p 5558) (derived105482 p h) (derived88681 p h)

theorem derived122050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 4169) ∨ (p 2177) ∨ (¬ p 3425) ∨ (¬ p 4804) :=
  ElevenRUP.step122050 (p 2098) (p 2177) (p 3425) (p 4169) (p 4559) (p 4804) (derived105701 p h) (derived88692 p h)

theorem derived122052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2132) ∨ (¬ p 4108) ∨ (p 3389) ∨ (¬ p 2187) ∨ (¬ p 2860) ∨ (¬ p 2922) :=
  ElevenRUP.step122052 (p 2132) (p 2187) (p 2509) (p 2860) (p 2922) (p 3389) (p 4108) (p 4384) (p 4733) (derived105430 p h) (derived106167 p h) (derived88700 p h)

theorem derived122054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3905) ∨ (¬ p 2132) ∨ (¬ p 2922) ∨ (¬ p 2742) ∨ (p 3389) ∨ (¬ p 4281) :=
  ElevenRUP.step122054 (p 2132) (p 2742) (p 2922) (p 3389) (p 3905) (p 4281) (p 5052) (derived105473 p h) (derived88713 p h)

theorem derived122055 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2922) ∨ (¬ p 2911) ∨ (¬ p 2363) ∨ (p 2220) ∨ (¬ p 3379) :=
  ElevenRUP.step122055 (p 2220) (p 2363) (p 2911) (p 2922) (p 3146) (p 3379) (p 4503) (derived106530 p h) (derived88714 p h)

theorem derived122056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2749) ∨ (¬ p 4108) ∨ (¬ p 2922) ∨ (¬ p 4281) ∨ (p 3389) ∨ (¬ p 2210) :=
  ElevenRUP.step122056 (p 2210) (p 2749) (p 2922) (p 3389) (p 4108) (p 4281) (p 4877) (derived105451 p h) (derived88718 p h)

theorem derived122057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4108) ∨ (¬ p 3541) ∨ (¬ p 2241) ∨ (p 3389) ∨ (¬ p 2922) :=
  ElevenRUP.step122057 (p 2241) (p 2750) (p 2922) (p 3389) (p 3541) (p 4108) (derived106345 p h) (derived88719 p h)

theorem derived122060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2656) ∨ (¬ p 2630) ∨ (¬ p 2922) ∨ (¬ p 3347) ∨ (¬ p 3879) ∨ (p 3136) :=
  ElevenRUP.step122060 (p 2630) (p 2656) (p 2922) (p 3136) (p 3347) (p 3879) (p 4646) (derived105534 p h) (derived88734 p h)

theorem derived122063 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 2156) ∨ (p 2901) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 2252) ∨ (p 2608) ∨ (¬ p 2284) :=
  ElevenRUP.step122063 (p 2156) (p 2252) (p 2284) (p 2608) (p 2750) (p 2901) (p 2922) (p 2950) (p 3379) (p 4277) (derived106345 p h) (derived105380 p h) (derived88743 p h)

theorem derived122064 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2284) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (p 3125) ∨ (¬ p 2417) :=
  ElevenRUP.step122064 (p 2254) (p 2284) (p 2417) (p 2922) (p 2946) (p 3125) (p 3379) (p 4625) (derived105366 p h) (derived106455 p h) (derived88749 p h)

theorem derived122067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 2156) ∨ (p 2396) ∨ (¬ p 3986) ∨ (¬ p 2922) ∨ (¬ p 2911) ∨ (¬ p 3379) ∨ (p 2295) :=
  ElevenRUP.step122067 (p 2156) (p 2254) (p 2295) (p 2396) (p 2911) (p 2922) (p 2950) (p 3379) (p 3986) (p 4666) (derived105366 p h) (derived105658 p h) (derived88756 p h)

theorem derived122069 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 4202) ∨ (¬ p 2922) ∨ (¬ p 2373) :=
  ElevenRUP.step122069 (p 2166) (p 2373) (p 2922) (p 4202) (p 4646) (derived105534 p h) (derived88762 p h)

theorem derived122072 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 2406) ∨ (¬ p 2177) ∨ (¬ p 4079) ∨ (¬ p 2922) ∨ (¬ p 3425) ∨ (¬ p 2230) :=
  ElevenRUP.step122072 (p 2177) (p 2230) (p 2406) (p 2717) (p 2922) (p 3425) (p 4079) (p 4276) (p 4736) (derived105431 p h) (derived105516 p h) (derived88776 p h)

theorem derived122073 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2922) ∨ (¬ p 4034) ∨ (¬ p 3379) :=
  ElevenRUP.step122073 (p 2210) (p 2922) (p 3379) (p 4034) (p 4646) (derived105534 p h) (derived88778 p h)

theorem derived122074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (p 2807) ∨ (¬ p 2922) :=
  ElevenRUP.step122074 (p 2651) (p 2807) (p 2922) (p 4814) (derived105440 p h) (derived88786 p h)

theorem derived122077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 2331) ∨ (p 3461) ∨ (p 3323) ∨ (¬ p 2922) ∨ (¬ p 3379) :=
  ElevenRUP.step122077 (p 2254) (p 2331) (p 2922) (p 3323) (p 3379) (p 3461) (p 3868) (p 4826) (derived105366 p h) (derived105444 p h) (derived88798 p h)

theorem derived122078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (p 2717) ∨ (p 2493) ∨ (¬ p 2573) ∨ (¬ p 2922) ∨ (¬ p 2881) ∨ (¬ p 4079) :=
  ElevenRUP.step122078 (p 2493) (p 2573) (p 2717) (p 2881) (p 2922) (p 3425) (p 4079) (p 4277) (p 4736) (derived105431 p h) (derived105380 p h) (derived88799 p h)

theorem derived122079 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3379) ∨ (p 2295) ∨ (p 2177) ∨ (p 2331) ∨ (¬ p 2417) :=
  ElevenRUP.step122079 (p 2177) (p 2254) (p 2295) (p 2331) (p 2417) (p 2922) (p 3379) (p 4668) (derived105366 p h) (derived105414 p h) (derived88808 p h)

theorem derived122084 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 3136) ∨ (¬ p 4079) ∨ (¬ p 2573) ∨ (p 2493) ∨ (¬ p 2922) ∨ (¬ p 4236) ∨ (¬ p 4653) ∨ (p 2946) :=
  ElevenRUP.step122084 (p 2493) (p 2573) (p 2685) (p 2922) (p 2946) (p 3136) (p 4079) (p 4236) (p 4653) (p 4736) (derived105431 p h) (derived88816 p h)

theorem derived122085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 2901) ∨ (¬ p 4079) ∨ (p 3136) ∨ (¬ p 2922) ∨ (p 2493) ∨ (p 2696) :=
  ElevenRUP.step122085 (p 2493) (p 2573) (p 2696) (p 2901) (p 2922) (p 3136) (p 4079) (p 4277) (p 4736) (derived105431 p h) (derived105380 p h) (derived88817 p h)

theorem derived122086 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2437) ∨ (¬ p 4281) ∨ (¬ p 2922) :=
  ElevenRUP.step122086 (p 2249) (p 2437) (p 2651) (p 2922) (p 4281) (derived106513 p h) (derived88818 p h)

theorem derived122087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4116) ∨ (p 3189) ∨ (¬ p 2363) ∨ (¬ p 2922) ∨ (¬ p 2911) ∨ (p 2088) ∨ (¬ p 2651) ∨ (¬ p 3177) :=
  ElevenRUP.step122087 (p 2088) (p 2255) (p 2363) (p 2651) (p 2911) (p 2922) (p 3177) (p 3189) (p 4116) (p 4503) (derived106530 p h) (derived105367 p h) (derived88822 p h)

theorem derived122088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 4383) ∨ (¬ p 2881) ∨ (¬ p 2922) :=
  ElevenRUP.step122088 (p 2509) (p 2881) (p 2922) (p 4277) (p 4383) (derived105380 p h) (derived41332 p h)

theorem derived122089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2417) ∨ (¬ p 2785) ∨ (p 2307) ∨ (¬ p 3590) ∨ (p 2177) ∨ (p 2829) ∨ (¬ p 2598) :=
  ElevenRUP.step122089 (p 2177) (p 2307) (p 2417) (p 2598) (p 2785) (p 2829) (p 2922) (p 3590) (p 4668) (derived105414 p h) (derived88824 p h)

theorem derived122091 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 3379) ∨ (¬ p 4140) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (p 2295) ∨ (p 3246) :=
  ElevenRUP.step122091 (p 2254) (p 2295) (p 2331) (p 2911) (p 2922) (p 3246) (p 3379) (p 4140) (p 4666) (derived105366 p h) (derived105658 p h) (derived88827 p h)

theorem derived122092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3950) ∨ (¬ p 3379) ∨ (¬ p 2922) ∨ (p 2331) ∨ (p 2363) ∨ (p 2668) ∨ (¬ p 2417) :=
  ElevenRUP.step122092 (p 2254) (p 2331) (p 2363) (p 2417) (p 2668) (p 2922) (p 3379) (p 3950) (derived105366 p h) (derived88831 p h)

theorem derived122093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2911) ∨ (¬ p 2608) ∨ (p 3093) ∨ (¬ p 2459) ∨ (p 3319) :=
  ElevenRUP.step122093 (p 2459) (p 2608) (p 2911) (p 2922) (p 3093) (p 3319) (p 4376) (p 4604) (derived106320 p h) (derived106293 p h) (derived88833 p h)

theorem derived122095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3575) ∨ (¬ p 4636) ∨ (¬ p 2922) ∨ (¬ p 2341) :=
  ElevenRUP.step122095 (p 2341) (p 2922) (p 3193) (p 3575) (p 4636) (p 4666) (derived105658 p h) (derived53150 p h)

theorem derived122098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 4636) ∨ (¬ p 2922) ∨ (¬ p 2396) :=
  ElevenRUP.step122098 (p 2396) (p 2922) (p 3193) (p 4276) (p 4636) (derived105516 p h) (derived41361 p h)

theorem derived122100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4108) ∨ (p 3389) ∨ (¬ p 2608) ∨ (¬ p 2922) :=
  ElevenRUP.step122100 (p 2608) (p 2922) (p 3389) (p 4108) (p 4376) (derived106320 p h) (derived88849 p h)

theorem derived122102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 3156) ∨ (¬ p 3379) ∨ (p 2946) ∨ (¬ p 5568) ∨ (¬ p 2922) :=
  ElevenRUP.step122102 (p 2254) (p 2922) (p 2946) (p 3156) (p 3379) (p 3868) (p 5560) (p 5568) (derived105366 p h) (derived106188 p h) (derived88861 p h)

theorem derived122103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3575) ∨ (p 2901) ∨ (p 2406) ∨ (¬ p 4283) ∨ (¬ p 2922) :=
  ElevenRUP.step122103 (p 2406) (p 2901) (p 2922) (p 3575) (p 4283) (p 4702) (derived106079 p h) (derived88870 p h)

theorem derived122104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 2563) ∨ (p 2274) :=
  ElevenRUP.step122104 (p 2274) (p 2563) (p 2982) (p 4624) (derived105408 p h) (derived88877 p h)

theorem derived122106 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (p 2553) ∨ (¬ p 3347) ∨ (¬ p 3527) ∨ (p 2396) ∨ (p 2608) ∨ (¬ p 3399) :=
  ElevenRUP.step122106 (p 2396) (p 2553) (p 2573) (p 2608) (p 3347) (p 3399) (p 3527) (p 4666) (derived105658 p h) (derived88906 p h)

theorem derived122107 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 2166) ∨ (¬ p 3347) ∨ (p 2528) ∨ (¬ p 2210) ∨ (¬ p 2459) ∨ (p 2608) :=
  ElevenRUP.step122107 (p 2166) (p 2210) (p 2459) (p 2470) (p 2528) (p 2608) (p 3347) (p 4902) (derived105456 p h) (derived88909 p h)

theorem derived122112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 2753) ∨ (p 2459) ∨ (p 2187) ∨ (p 2230) ∨ (¬ p 3256) ∨ (¬ p 3347) ∨ (p 2563) ∨ (¬ p 3166) :=
  ElevenRUP.step122112 (p 2187) (p 2230) (p 2459) (p 2563) (p 2753) (p 3166) (p 3256) (p 3347) (p 4117) (p 4503) (derived106530 p h) (derived88924 p h)

theorem derived122113 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (p 2982) ∨ (¬ p 2493) ∨ (¬ p 4203) ∨ (¬ p 3347) :=
  ElevenRUP.step122113 (p 2230) (p 2493) (p 2982) (p 3347) (p 4203) (p 5043) (derived105471 p h) (derived88925 p h)

theorem derived122114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3347) ∨ (¬ p 3063) ∨ (p 2373) ∨ (p 2608) ∨ (¬ p 2427) ∨ (p 3051) ∨ (¬ p 3904) ∨ (¬ p 3093) :=
  ElevenRUP.step122114 (p 2373) (p 2427) (p 2608) (p 3051) (p 3063) (p 3093) (p 3347) (p 3904) (p 4134) (derived105379 p h) (derived88930 p h)

theorem derived122117 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3347) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2230) ∨ (p 3246) ∨ (p 2427) :=
  ElevenRUP.step122117 (p 2230) (p 2427) (p 2608) (p 3246) (p 3347) (p 3399) (p 3527) (p 4666) (derived105658 p h) (derived88934 p h)

theorem derived122121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2498) ∨ (p 3093) ∨ (¬ p 4257) ∨ (¬ p 2230) ∨ (¬ p 3379) :=
  ElevenRUP.step122121 (p 2230) (p 2498) (p 3093) (p 3379) (p 4257) (p 4715) (p 4866) (derived105423 p h) (derived106063 p h) (derived88948 p h)

theorem derived122126 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3579) ∨ (¬ p 2685) ∨ (p 3016) :=
  ElevenRUP.step122126 (p 2630) (p 2685) (p 3016) (p 3579) (p 4711) (derived105655 p h) (derived88963 p h)

theorem derived122127 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 4066) ∨ (p 2427) ∨ (¬ p 4283) ∨ (¬ p 2685) :=
  ElevenRUP.step122127 (p 2427) (p 2685) (p 3136) (p 4066) (p 4283) (p 4705) (derived106238 p h) (derived88971 p h)

theorem derived122128 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2922) ∨ (¬ p 2685) ∨ (¬ p 3579) :=
  ElevenRUP.step122128 (p 2630) (p 2685) (p 2922) (p 3579) (p 4811) (derived105633 p h) (derived88972 p h)

theorem derived122133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2749) ∨ (¬ p 3032) ∨ (p 2630) ∨ (¬ p 2651) ∨ (¬ p 2685) ∨ (¬ p 2246) :=
  ElevenRUP.step122133 (p 2246) (p 2630) (p 2651) (p 2685) (p 2749) (p 3032) (p 4796) (derived105439 p h) (derived88986 p h)

theorem derived122134 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3399) ∨ (¬ p 2651) ∨ (¬ p 2396) ∨ (p 3631) ∨ (¬ p 2685) :=
  ElevenRUP.step122134 (p 2248) (p 2396) (p 2630) (p 2651) (p 2685) (p 3399) (p 3631) (derived105365 p h) (derived88988 p h)

theorem derived122138 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2230) ∨ (¬ p 2685) ∨ (¬ p 3347) ∨ (¬ p 2449) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (p 2563) :=
  ElevenRUP.step122138 (p 2230) (p 2449) (p 2563) (p 2685) (p 2696) (p 2753) (p 3125) (p 3347) (p 4625) (derived106455 p h) (derived88997 p h)

theorem derived122139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (¬ p 2696) ∨ (p 2230) ∨ (¬ p 4322) ∨ (¬ p 2685) ∨ (p 2982) :=
  ElevenRUP.step122139 (p 2230) (p 2685) (p 2696) (p 2982) (p 3931) (p 4322) (p 4729) (p 4826) (derived105444 p h) (derived105429 p h) (derived88998 p h)

theorem derived122144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2927) ∨ (p 3399) ∨ (¬ p 2696) ∨ (¬ p 3379) ∨ (¬ p 2264) ∨ (p 2417) ∨ (¬ p 2685) ∨ (¬ p 2753) :=
  ElevenRUP.step122144 (p 2264) (p 2417) (p 2685) (p 2696) (p 2753) (p 2927) (p 3379) (p 3399) (p 4666) (derived105658 p h) (derived89007 p h)

theorem derived122145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (¬ p 2685) ∨ (¬ p 2449) ∨ (¬ p 2696) ∨ (p 3093) ∨ (p 2363) ∨ (¬ p 3950) :=
  ElevenRUP.step122145 (p 2363) (p 2449) (p 2685) (p 2696) (p 3093) (p 3923) (p 3950) (p 4733) (derived105430 p h) (derived89008 p h)

theorem derived122146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (¬ p 2696) ∨ (p 2470) ∨ (p 2528) ∨ (¬ p 2685) ∨ (p 3266) :=
  ElevenRUP.step122146 (p 2470) (p 2528) (p 2685) (p 2696) (p 3266) (p 3931) (p 4729) (p 4826) (derived105444 p h) (derived105429 p h) (derived89010 p h)

theorem derived122147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 3399) ∨ (¬ p 2685) ∨ (¬ p 2753) ∨ (¬ p 2264) ∨ (¬ p 2210) ∨ (p 3631) :=
  ElevenRUP.step122147 (p 2210) (p 2264) (p 2685) (p 2696) (p 2753) (p 3399) (p 3631) (p 4666) (p 4877) (derived105658 p h) (derived105451 p h) (derived89011 p h)

theorem derived122149 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (p 2156) ∨ (¬ p 4333) ∨ (¬ p 2685) ∨ (¬ p 2957) :=
  ElevenRUP.step122149 (p 2156) (p 2685) (p 2957) (p 3136) (p 4333) (p 4558) (derived105400 p h) (derived89027 p h)

theorem derived122150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2685) ∨ (p 2417) ∨ (¬ p 2608) ∨ (¬ p 3581) ∨ (¬ p 2396) ∨ (p 2573) :=
  ElevenRUP.step122150 (p 2396) (p 2417) (p 2573) (p 2608) (p 2685) (p 2737) (p 3581) (p 5193) (derived105488 p h) (derived89033 p h)

theorem derived122152 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2166) ∨ (¬ p 4172) ∨ (p 2192) ∨ (¬ p 2156) ∨ (¬ p 4043) ∨ (¬ p 2685) ∨ (p 2807) :=
  ElevenRUP.step122152 (p 2156) (p 2166) (p 2192) (p 2254) (p 2685) (p 2807) (p 3005) (p 4043) (p 4172) (derived105366 p h) (derived89036 p h)

theorem derived122154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (¬ p 2352) ∨ (¬ p 2685) ∨ (p 3564) ∨ (¬ p 2696) ∨ (¬ p 2449) ∨ (¬ p 2753) ∨ (¬ p 4870) :=
  ElevenRUP.step122154 (p 2352) (p 2449) (p 2685) (p 2696) (p 2753) (p 3564) (p 3923) (p 4625) (p 4870) (derived106455 p h) (derived89043 p h)

theorem derived122155 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2192) ∨ (¬ p 4236) ∨ (¬ p 2210) ∨ (¬ p 2685) ∨ (¬ p 2187) ∨ (p 2807) ∨ (¬ p 4774) :=
  ElevenRUP.step122155 (p 2187) (p 2192) (p 2210) (p 2685) (p 2807) (p 3005) (p 4236) (p 4736) (p 4774) (derived105431 p h) (derived89044 p h)

theorem derived122157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (p 2363) ∨ (¬ p 2696) ∨ (¬ p 2449) ∨ (p 2573) ∨ (p 2352) ∨ (¬ p 3950) :=
  ElevenRUP.step122157 (p 2352) (p 2363) (p 2449) (p 2573) (p 2685) (p 2696) (p 3950) (p 4729) (derived105429 p h) (derived89053 p h)

theorem derived122160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (p 2807) ∨ (¬ p 2685) ∨ (p 2727) :=
  ElevenRUP.step122160 (p 2651) (p 2685) (p 2727) (p 2745) (p 2807) (derived105523 p h) (derived89056 p h)

theorem derived122162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (¬ p 2696) ∨ (¬ p 2145) ∨ (p 3266) ∨ (p 3146) ∨ (¬ p 2685) ∨ (p 2220) :=
  ElevenRUP.step122162 (p 2145) (p 2220) (p 2685) (p 2696) (p 3146) (p 3266) (p 3931) (p 4826) (derived105444 p h) (derived89063 p h)

theorem derived122163 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 3519) ∨ (p 2363) ∨ (¬ p 2996) ∨ (¬ p 2528) ∨ (¬ p 2470) ∨ (¬ p 2685) ∨ (¬ p 2741) ∨ (¬ p 4774) :=
  ElevenRUP.step122163 (p 2363) (p 2470) (p 2528) (p 2685) (p 2741) (p 2996) (p 3005) (p 3519) (p 4376) (p 4774) (derived106320 p h) (derived89065 p h)

theorem derived122164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3031) ∨ (¬ p 4066) ∨ (p 3527) ∨ (¬ p 2685) ∨ (¬ p 2341) :=
  ElevenRUP.step122164 (p 2341) (p 2685) (p 2745) (p 3031) (p 3527) (p 4066) (derived105523 p h) (derived89066 p h)

theorem derived122165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2363) ∨ (¬ p 3573) ∨ (p 2573) ∨ (¬ p 2264) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (p 2528) :=
  ElevenRUP.step122165 (p 2264) (p 2363) (p 2528) (p 2573) (p 2685) (p 2696) (p 2753) (p 3347) (p 3573) (p 4503) (derived106530 p h) (derived89074 p h)

theorem derived122168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (p 2230) ∨ (¬ p 3950) ∨ (p 3146) ∨ (¬ p 2696) ∨ (¬ p 2449) ∨ (p 2373) :=
  ElevenRUP.step122168 (p 2230) (p 2373) (p 2449) (p 2685) (p 2696) (p 3146) (p 3950) (p 4729) (derived105429 p h) (derived89082 p h)

end ElevenLogic
