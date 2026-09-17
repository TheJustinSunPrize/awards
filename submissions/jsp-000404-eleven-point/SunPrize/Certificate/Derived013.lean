import SunPrize.Certificate.Derived012
import SunPrize.Certificate.Logic013
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived51810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3347) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3950) ∨ (¬ p 3954) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 5216) :=
  ElevenRUP.step51810 (p 2027) (p 2579) (p 3347) (p 3399) (p 3631) (p 3950) (p 3954) (p 3956) (p 4347) (p 5216) (derived40810 p h) (h 24971)

theorem derived51811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2573) ∨ (¬ p 3540) ∨ (¬ p 3921) ∨ (¬ p 3958) :=
  ElevenRUP.step51811 (p 2027) (p 2274) (p 2573) (p 3540) (p 3921) (p 3958) (derived40810 p h) (h 24972)

theorem derived51812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3950) ∨ (¬ p 3954) ∨ (¬ p 3989) ∨ (¬ p 4347) ∨ (¬ p 4877) :=
  ElevenRUP.step51812 (p 2027) (p 3399) (p 3631) (p 3645) (p 3646) (p 3950) (p 3954) (p 3989) (p 4347) (p 4877) (derived40810 p h) (h 24973)

theorem derived51813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2373) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 3951) ∨ (¬ p 4120) ∨ (¬ p 4524) ∨ (¬ p 4948) :=
  ElevenRUP.step51813 (p 2027) (p 2241) (p 2373) (p 2449) (p 3027) (p 3951) (p 4120) (p 4524) (p 4948) (derived40810 p h) (h 24974)

theorem derived51814 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3027) ∨ (¬ p 3692) ∨ (¬ p 3931) ∨ (¬ p 4120) ∨ (¬ p 4444) ∨ (¬ p 4524) ∨ (¬ p 4826) :=
  ElevenRUP.step51814 (p 2027) (p 2241) (p 3027) (p 3692) (p 3931) (p 4120) (p 4444) (p 4524) (p 4826) (derived40810 p h) (h 24975)

theorem derived51821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3319) ∨ (¬ p 3549) ∨ (¬ p 3956) :=
  ElevenRUP.step51821 (p 1999) (p 2027) (p 2169) (p 2553) (p 3319) (p 3549) (p 3956) (h 2159) (derived40810 p h) (derived40866 p h) (h 24982)

theorem derived51835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4137) ∨ (p 4718) :=
  ElevenRUP.step51835 (p 1990) (p 3128) (p 4137) (p 4718) (h 2150) (derived40894 p h) (h 24998)

theorem derived51837 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2579) ∨ (¬ p 2608) ∨ (¬ p 4108) ∨ (¬ p 4376) :=
  ElevenRUP.step51837 (p 2027) (p 2493) (p 2579) (p 2608) (p 4108) (p 4376) (derived40810 p h) (h 25001)

theorem derived51838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3527) ∨ (¬ p 3644) ∨ (¬ p 3742) :=
  ElevenRUP.step51838 (p 1991) (p 2027) (p 2657) (p 3527) (p 3623) (p 3644) (p 3742) (h 2151) (derived40810 p h) (derived40903 p h) (h 25003)

theorem derived51841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2951) ∨ (¬ p 2963) ∨ (¬ p 2992) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3904) ∨ (¬ p 3922) ∨ (¬ p 3923) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step51841 (p 2027) (p 2249) (p 2951) (p 2963) (p 2992) (p 3276) (p 3355) (p 3904) (p 3922) (p 3923) (p 5123) (p 5580) (derived40810 p h) (h 25008)

theorem derived51842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2249) ∨ (¬ p 2951) ∨ (¬ p 2963) ∨ (¬ p 2992) ∨ (¬ p 3922) ∨ (¬ p 3969) ∨ (¬ p 4026) ∨ (¬ p 4191) ∨ (¬ p 5119) :=
  ElevenRUP.step51842 (p 2027) (p 2220) (p 2249) (p 2951) (p 2963) (p 2992) (p 3922) (p 3969) (p 4026) (p 4191) (p 5119) (derived40810 p h) (h 25009)

theorem derived51847 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2657) ∨ (¬ p 2807) ∨ (¬ p 4278) :=
  ElevenRUP.step51847 (p 2010) (p 2027) (p 2449) (p 2545) (p 2657) (p 2807) (p 4278) (h 2170) (derived40810 p h) (derived40876 p h) (h 25014)

theorem derived51848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 2584) ∨ (¬ p 2588) ∨ (¬ p 4347) :=
  ElevenRUP.step51848 (p 1981) (p 2027) (p 2233) (p 2307) (p 2510) (p 2528) (p 2584) (p 2588) (p 4347) (h 2141) (derived40810 p h) (derived40868 p h) (h 25015)

theorem derived51849 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3343) ∨ (¬ p 3364) ∨ (¬ p 4704) ∨ (¬ p 5160) :=
  ElevenRUP.step51849 (p 2027) (p 3136) (p 3343) (p 3364) (p 4704) (p 5160) (derived40810 p h) (h 25016)

theorem derived51850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2274) ∨ (¬ p 3546) ∨ (¬ p 3551) ∨ (¬ p 3922) ∨ (¬ p 4105) ∨ (¬ p 4564) :=
  ElevenRUP.step51850 (p 2027) (p 2177) (p 2274) (p 3546) (p 3551) (p 3922) (p 4105) (p 4564) (derived40810 p h) (h 25017)

theorem derived51851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 3039) ∨ (¬ p 3266) ∨ (¬ p 3286) ∨ (¬ p 3817) ∨ (¬ p 4191) ∨ (¬ p 4450) ∨ (¬ p 4623) ∨ (¬ p 4952) ∨ (¬ p 5175) :=
  ElevenRUP.step51851 (p 2027) (p 2657) (p 2727) (p 3039) (p 3266) (p 3286) (p 3817) (p 4191) (p 4450) (p 4623) (p 4952) (p 5175) (derived40810 p h) (h 25018)

theorem derived51853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2891) ∨ (¬ p 2952) ∨ (¬ p 4320) ∨ (¬ p 4365) :=
  ElevenRUP.step51853 (p 2027) (p 2249) (p 2891) (p 2952) (p 4320) (p 4365) (derived40810 p h) (h 25020)

theorem derived51858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 3821) ∨ (¬ p 4849) :=
  ElevenRUP.step51858 (p 2027) (p 2249) (p 2449) (p 3027) (p 3821) (p 4849) (derived40810 p h) (h 25025)

theorem derived51859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 3422) ∨ (¬ p 3876) ∨ (¬ p 3921) ∨ (¬ p 3958) :=
  ElevenRUP.step51859 (p 2027) (p 2274) (p 3422) (p 3876) (p 3921) (p 3958) (derived40810 p h) (h 25026)

theorem derived51860 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 3581) ∨ (¬ p 3958) ∨ (¬ p 4278) :=
  ElevenRUP.step51860 (p 2027) (p 2274) (p 2396) (p 3581) (p 3958) (p 4278) (derived40810 p h) (h 25027)

theorem derived51865 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2249) ∨ (¬ p 2417) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2952) ∨ (¬ p 3389) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 4282) :=
  ElevenRUP.step51865 (p 2027) (p 2191) (p 2249) (p 2417) (p 2656) (p 2727) (p 2952) (p 3389) (p 3692) (p 3950) (p 4282) (derived40810 p h) (h 25034)

theorem derived51866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2417) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2952) ∨ (¬ p 3389) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 3950) :=
  ElevenRUP.step51866 (p 2027) (p 2249) (p 2417) (p 2656) (p 2727) (p 2952) (p 3389) (p 3497) (p 3692) (p 3950) (derived40810 p h) (h 25035)

theorem derived51868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 4733) :=
  ElevenRUP.step51868 (p 2027) (p 2247) (p 2417) (p 2598) (p 3201) (p 3950) (p 4118) (p 4360) (p 4733) (derived40810 p h) (h 25040)

theorem derived51869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3952) ∨ (¬ p 3956) ∨ (¬ p 3958) ∨ (¬ p 4441) :=
  ElevenRUP.step51869 (p 2027) (p 3156) (p 3952) (p 3956) (p 3958) (p 4441) (derived40810 p h) (h 25041)

theorem derived51871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 3222) ∨ (¬ p 3359) ∨ (¬ p 3379) :=
  ElevenRUP.step51871 (p 1997) (p 2027) (p 2542) (p 2699) (p 3222) (p 3359) (p 3379) (h 2157) (derived40810 p h) (derived40881 p h) (h 25043)

theorem derived51873 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2241) ∨ (¬ p 2437) ∨ (¬ p 2727) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4276) ∨ (¬ p 4524) :=
  ElevenRUP.step51873 (p 2027) (p 2177) (p 2241) (p 2437) (p 2727) (p 3556) (p 3570) (p 4276) (p 4524) (derived40810 p h) (h 25045)

theorem derived51878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2440) ∨ (¬ p 2663) ∨ (¬ p 3879) ∨ (p 4705) :=
  ElevenRUP.step51878 (p 1994) (p 2230) (p 2323) (p 2440) (p 2663) (p 3879) (p 4705) (h 2154) (derived40870 p h) (h 25055)

theorem derived51882 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 3379) ∨ (¬ p 3553) ∨ (¬ p 3556) ∨ (¬ p 3690) ∨ (¬ p 4524) :=
  ElevenRUP.step51882 (p 1982) (p 2027) (p 2449) (p 2518) (p 2528) (p 2633) (p 3379) (p 3553) (p 3556) (p 3690) (p 4524) (h 2142) (derived40810 p h) (derived40879 p h) (h 25059)

theorem derived51883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2963) ∨ (¬ p 3379) ∨ (¬ p 3568) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step51883 (p 2027) (p 2254) (p 2518) (p 2528) (p 2963) (p 3379) (p 3568) (p 4107) (p 4669) (derived40810 p h) (h 25060)

theorem derived51884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 3156) ∨ (¬ p 3434) ∨ (¬ p 3951) ∨ (¬ p 4120) ∨ (¬ p 4208) ∨ (¬ p 4524) :=
  ElevenRUP.step51884 (p 2027) (p 2608) (p 2707) (p 3156) (p 3434) (p 3951) (p 4120) (p 4208) (p 4524) (derived40810 p h) (h 25061)

theorem derived51885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2312) ∨ (¬ p 2493) ∨ (¬ p 2928) ∨ (¬ p 3958) ∨ (¬ p 4279) :=
  ElevenRUP.step51885 (p 2027) (p 2274) (p 2312) (p 2493) (p 2928) (p 3958) (p 4279) (derived40810 p h) (h 25062)

theorem derived51887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2819) ∨ (¬ p 3822) ∨ (¬ p 3956) ∨ (¬ p 3958) :=
  ElevenRUP.step51887 (p 2027) (p 2274) (p 2819) (p 3822) (p 3956) (p 3958) (derived40810 p h) (h 25065)

theorem derived51890 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3367) ∨ (¬ p 3549) ∨ (¬ p 3953) ∨ (¬ p 4426) ∨ (¬ p 4752) :=
  ElevenRUP.step51890 (p 2027) (p 2122) (p 3367) (p 3549) (p 3953) (p 4426) (p 4752) (derived40810 p h) (h 25069)

theorem derived51891 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 3367) ∨ (¬ p 3486) ∨ (¬ p 4313) ∨ (¬ p 4752) ∨ (¬ p 4874) :=
  ElevenRUP.step51891 (p 2027) (p 2870) (p 3367) (p 3486) (p 4313) (p 4752) (p 4874) (derived40810 p h) (h 25070)

theorem derived51892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3568) ∨ (¬ p 3646) ∨ (¬ p 4140) ∨ (¬ p 4564) :=
  ElevenRUP.step51892 (p 2027) (p 3051) (p 3568) (p 3646) (p 4140) (p 4564) (derived40810 p h) (h 25071)

theorem derived51893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 3483) ∨ (¬ p 3953) ∨ (¬ p 4026) ∨ (¬ p 4426) ∨ (¬ p 4752) :=
  ElevenRUP.step51893 (p 2027) (p 3367) (p 3483) (p 3953) (p 4026) (p 4426) (p 4752) (derived40810 p h) (h 25072)

theorem derived51897 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2427) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3556) ∨ (¬ p 3880) ∨ (¬ p 4134) ∨ (¬ p 4524) :=
  ElevenRUP.step51897 (p 2027) (p 2241) (p 2427) (p 2641) (p 2668) (p 3556) (p 3880) (p 4134) (p 4524) (derived40810 p h) (h 25076)

theorem derived51899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2811) ∨ (¬ p 2958) ∨ (¬ p 3367) ∨ (¬ p 4173) ∨ (¬ p 4752) ∨ (¬ p 4874) :=
  ElevenRUP.step51899 (p 2027) (p 2156) (p 2811) (p 2958) (p 3367) (p 4173) (p 4752) (p 4874) (derived40810 p h) (h 25078)

theorem derived51900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2870) ∨ (¬ p 3366) ∨ (¬ p 3367) ∨ (¬ p 3556) ∨ (¬ p 4313) ∨ (¬ p 4752) :=
  ElevenRUP.step51900 (p 2027) (p 2136) (p 2870) (p 3366) (p 3367) (p 3556) (p 4313) (p 4752) (derived40810 p h) (h 25079)

theorem derived51905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step51905 (p 2027) (p 2138) (p 2363) (p 3063) (p 3093) (p 3690) (p 4244) (p 4669) (p 4736) (derived40810 p h) (h 25085)

theorem derived51906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 3365) ∨ (¬ p 4035) ∨ (¬ p 5284) :=
  ElevenRUP.step51906 (p 1976) (p 2027) (p 2766) (p 3266) (p 3365) (p 4035) (p 5284) (h 2136) (derived40810 p h) (derived40884 p h) (h 25086)

theorem derived51911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2254) ∨ (¬ p 2952) ∨ (¬ p 3093) ∨ (¬ p 3136) ∨ (¬ p 3309) ∨ (¬ p 3877) ∨ (¬ p 4041) :=
  ElevenRUP.step51911 (p 2027) (p 2177) (p 2254) (p 2952) (p 3093) (p 3136) (p 3309) (p 3877) (p 4041) (derived40810 p h) (h 25091)

theorem derived51913 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3256) ∨ (¬ p 3399) ∨ (¬ p 4189) ∨ (¬ p 4288) ∨ (¬ p 4348) :=
  ElevenRUP.step51913 (p 1998) (p 2027) (p 2247) (p 2688) (p 3256) (p 3399) (p 4189) (p 4288) (p 4348) (h 2158) (derived40810 p h) (derived40880 p h) (h 25093)

theorem derived51916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2934) ∨ (¬ p 3584) ∨ (¬ p 3590) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4031) ∨ (¬ p 4715) ∨ (¬ p 4984) :=
  ElevenRUP.step51916 (p 2027) (p 2934) (p 3584) (p 3590) (p 3631) (p 3821) (p 4031) (p 4715) (p 4984) (derived40810 p h) (h 25096)

theorem derived51917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 3038) ∨ (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 3820) ∨ (¬ p 4752) :=
  ElevenRUP.step51917 (p 2027) (p 2598) (p 2742) (p 3038) (p 3527) (p 3551) (p 3820) (p 4752) (derived40810 p h) (h 25097)

theorem derived51920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2440) ∨ (¬ p 2696) ∨ (¬ p 2743) ∨ (¬ p 3541) :=
  ElevenRUP.step51920 (p 1994) (p 2027) (p 2406) (p 2440) (p 2611) (p 2696) (p 2743) (p 3541) (h 2154) (derived40810 p h) (derived40877 p h) (h 25101)

theorem derived51922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2807) ∨ (¬ p 2911) ∨ (¬ p 4278) :=
  ElevenRUP.step51922 (p 1998) (p 2027) (p 2323) (p 2449) (p 2807) (p 2911) (p 4278) (h 2158) (derived40810 p h) (derived40870 p h) (h 25103)

theorem derived51925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3516) ∨ (¬ p 3551) ∨ (¬ p 4277) ∨ (¬ p 4278) :=
  ElevenRUP.step51925 (p 2027) (p 2881) (p 3516) (p 3551) (p 4277) (p 4278) (derived40810 p h) (h 25106)

theorem derived51929 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2630) ∨ (¬ p 3016) ∨ (¬ p 4195) :=
  ElevenRUP.step51929 (p 1975) (p 2027) (p 2287) (p 2553) (p 2630) (p 3016) (p 4195) (h 2135) (derived40810 p h) (derived40869 p h) (h 25113)

theorem derived51930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 3367) ∨ (¬ p 4313) ∨ (¬ p 4363) ∨ (¬ p 4752) ∨ (¬ p 4874) :=
  ElevenRUP.step51930 (p 2027) (p 3105) (p 3367) (p 4313) (p 4363) (p 4752) (p 4874) (derived40810 p h) (h 25115)

theorem derived51932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2156) ∨ (¬ p 2246) ∨ (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 2958) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 4752) ∨ (¬ p 5123) ∨ (¬ p 5612) :=
  ElevenRUP.step51932 (p 2027) (p 2104) (p 2156) (p 2246) (p 2598) (p 2742) (p 2958) (p 3125) (p 3461) (p 4752) (p 5123) (p 5612) (derived40810 p h) (h 25118)

theorem derived51933 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 4752) ∨ (¬ p 5123) ∨ (¬ p 5612) :=
  ElevenRUP.step51933 (p 2027) (p 2104) (p 2246) (p 2331) (p 2598) (p 2742) (p 3323) (p 3461) (p 4752) (p 5123) (p 5612) (derived40810 p h) (h 25119)

theorem derived51935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2192) ∨ (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 3646) ∨ (¬ p 4365) ∨ (¬ p 4752) :=
  ElevenRUP.step51935 (p 2027) (p 2136) (p 2192) (p 2598) (p 2742) (p 3646) (p 4365) (p 4752) (derived40810 p h) (h 25121)

theorem derived51939 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2246) ∨ (¬ p 2449) ∨ (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 2761) ∨ (¬ p 2807) ∨ (¬ p 4752) ∨ (¬ p 5123) ∨ (¬ p 5612) :=
  ElevenRUP.step51939 (p 2027) (p 2104) (p 2246) (p 2449) (p 2598) (p 2742) (p 2761) (p 2807) (p 4752) (p 5123) (p 5612) (derived40810 p h) (h 25125)

theorem derived51940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2743) ∨ (¬ p 3541) ∨ (¬ p 3584) ∨ (¬ p 4752) :=
  ElevenRUP.step51940 (p 2027) (p 2493) (p 2743) (p 3541) (p 3584) (p 4752) (derived40810 p h) (h 25126)

theorem derived51941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2780) ∨ (¬ p 2829) ∨ (¬ p 3362) ∨ (¬ p 3363) ∨ (¬ p 4752) :=
  ElevenRUP.step51941 (p 2027) (p 2743) (p 2780) (p 2829) (p 3362) (p 3363) (p 4752) (derived40810 p h) (h 25127)

theorem derived51945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 2743) ∨ (¬ p 3541) ∨ (¬ p 3874) ∨ (¬ p 4752) :=
  ElevenRUP.step51945 (p 2027) (p 2518) (p 2743) (p 3541) (p 3874) (p 4752) (derived40810 p h) (h 25131)

theorem derived51946 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2396) ∨ (¬ p 2779) ∨ (¬ p 2829) ∨ (¬ p 3055) ∨ (¬ p 3238) ∨ (¬ p 3951) ∨ (¬ p 4030) ∨ (¬ p 4734) ∨ (¬ p 4948) :=
  ElevenRUP.step51946 (p 2027) (p 2307) (p 2396) (p 2779) (p 2829) (p 3055) (p 3238) (p 3951) (p 4030) (p 4734) (p 4948) (derived40810 p h) (h 25132)

theorem derived51947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2839) ∨ (¬ p 3051) ∨ (¬ p 3055) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4030) ∨ (¬ p 4734) :=
  ElevenRUP.step51947 (p 2027) (p 2137) (p 2509) (p 2534) (p 2839) (p 3051) (p 3055) (p 3246) (p 3950) (p 4030) (p 4734) (derived40810 p h) (h 25133)

theorem derived51948 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2577) ∨ (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3063) ∨ (¬ p 4026) :=
  ElevenRUP.step51948 (p 1987) (p 2027) (p 2387) (p 2577) (p 2662) (p 2810) (p 3063) (p 3128) (p 4026) (h 2147) (derived40810 p h) (derived40894 p h) (h 25134)

theorem derived51949 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2774) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 4845) :=
  ElevenRUP.step51949 (p 2027) (p 2743) (p 2774) (p 3055) (p 3367) (p 4845) (derived40810 p h) (h 25135)

theorem derived51955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2657) ∨ (¬ p 3146) ∨ (¬ p 3742) ∨ (¬ p 4278) ∨ (¬ p 4669) :=
  ElevenRUP.step51955 (p 2027) (p 2166) (p 2210) (p 2254) (p 2657) (p 3146) (p 3742) (p 4278) (p 4669) (derived40810 p h) (h 25141)

theorem derived51956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2573) ∨ (¬ p 3362) ∨ (¬ p 3364) ∨ (¬ p 3584) ∨ (¬ p 5049) :=
  ElevenRUP.step51956 (p 2027) (p 2138) (p 2573) (p 3362) (p 3364) (p 3584) (p 5049) (derived40810 p h) (h 25142)

theorem derived51958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2963) ∨ (¬ p 3146) ∨ (¬ p 3568) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step51958 (p 2027) (p 2166) (p 2210) (p 2254) (p 2963) (p 3146) (p 3568) (p 4107) (p 4669) (derived40810 p h) (h 25144)

theorem derived51959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2619) ∨ (¬ p 3367) ∨ (¬ p 4313) ∨ (¬ p 4752) ∨ (¬ p 4874) :=
  ElevenRUP.step51959 (p 2027) (p 2191) (p 2619) (p 3367) (p 4313) (p 4752) (p 4874) (derived40810 p h) (h 25145)

theorem derived51965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2363) ∨ (¬ p 2657) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3742) ∨ (¬ p 4278) ∨ (¬ p 4669) :=
  ElevenRUP.step51965 (p 2027) (p 2254) (p 2363) (p 2657) (p 3063) (p 3093) (p 3742) (p 4278) (p 4669) (derived40810 p h) (h 25153)

theorem derived51966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 3016) ∨ (¬ p 3325) ∨ (¬ p 3958) ∨ (¬ p 4256) ∨ (¬ p 4432) :=
  ElevenRUP.step51966 (p 2027) (p 2274) (p 3016) (p 3325) (p 3958) (p 4256) (p 4432) (derived40810 p h) (h 25154)

theorem derived51967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2668) ∨ (¬ p 3568) ∨ (¬ p 3956) ∨ (¬ p 3958) :=
  ElevenRUP.step51967 (p 2027) (p 2274) (p 2668) (p 3568) (p 3956) (p 3958) (derived40810 p h) (h 25155)

theorem derived51970 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 3422) ∨ (¬ p 3958) ∨ (¬ p 4022) ∨ (¬ p 5160) :=
  ElevenRUP.step51970 (p 2027) (p 3125) (p 3422) (p 3958) (p 4022) (p 5160) (derived40810 p h) (h 25158)

theorem derived51984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 3051) ∨ (¬ p 3365) ∨ (¬ p 3486) ∨ (¬ p 4030) ∨ (¬ p 4202) ∨ (¬ p 4752) :=
  ElevenRUP.step51984 (p 2027) (p 2144) (p 3051) (p 3365) (p 3486) (p 4030) (p 4202) (p 4752) (derived40810 p h) (h 25173)

theorem derived51986 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 3309) ∨ (¬ p 3365) ∨ (¬ p 3568) ∨ (¬ p 3918) :=
  ElevenRUP.step51986 (p 1980) (p 2027) (p 2622) (p 2774) (p 3309) (p 3365) (p 3568) (p 3918) (h 2140) (derived40810 p h) (derived40878 p h) (h 25175)

theorem derived51991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3347) ∨ (¬ p 3365) ∨ (¬ p 3609) ∨ (¬ p 4030) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4752) :=
  ElevenRUP.step51991 (p 2027) (p 2098) (p 2579) (p 2588) (p 3347) (p 3365) (p 3609) (p 4030) (p 4107) (p 4669) (p 4752) (derived40810 p h) (h 25180)

theorem derived51992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2542) ∨ (¬ p 3096) ∨ (¬ p 3574) ∨ (¬ p 4539) :=
  ElevenRUP.step51992 (p 2027) (p 2156) (p 2542) (p 3096) (p 3574) (p 4539) (derived40810 p h) (h 25181)

theorem derived51993 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2589) ∨ (¬ p 2881) ∨ (¬ p 3389) ∨ (¬ p 3569) :=
  ElevenRUP.step51993 (p 1998) (p 2027) (p 2542) (p 2545) (p 2589) (p 2881) (p 3389) (p 3569) (h 2158) (derived40810 p h) (derived40876 p h) (h 25183)

theorem derived51994 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2780) ∨ (¬ p 3367) ∨ (¬ p 3759) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4734) :=
  ElevenRUP.step51994 (p 2027) (p 2470) (p 2528) (p 2780) (p 3367) (p 3759) (p 3822) (p 4107) (p 4669) (p 4734) (derived40810 p h) (h 25185)

theorem derived51997 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3367) ∨ (¬ p 3486) ∨ (¬ p 3690) ∨ (¬ p 3759) ∨ (¬ p 4243) ∨ (¬ p 4669) ∨ (¬ p 4734) :=
  ElevenRUP.step51997 (p 2027) (p 2138) (p 2470) (p 2528) (p 3367) (p 3486) (p 3690) (p 3759) (p 4243) (p 4669) (p 4734) (derived40810 p h) (h 25190)

theorem derived51998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3414) ∨ (¬ p 3471) ∨ (¬ p 4111) ∨ (¬ p 4236) :=
  ElevenRUP.step51998 (p 2008) (p 2027) (p 2545) (p 3027) (p 3414) (p 3471) (p 4111) (p 4236) (h 2168) (derived40810 p h) (derived40876 p h) (h 25191)

theorem derived51999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4341) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4843) :=
  ElevenRUP.step51999 (p 2027) (p 3256) (p 4341) (p 4347) (p 4358) (p 4843) (derived40810 p h) (h 25192)

theorem derived52002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2220) ∨ (¬ p 2748) ∨ (¬ p 2839) ∨ (¬ p 2996) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4734) :=
  ElevenRUP.step52002 (p 2027) (p 2137) (p 2220) (p 2748) (p 2839) (p 2996) (p 3146) (p 3365) (p 3947) (p 4669) (p 4734) (derived40810 p h) (h 25195)

theorem derived52005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (¬ p 2922) ∨ (¬ p 2946) ∨ (¬ p 3540) ∨ (¬ p 4116) ∨ (¬ p 4704) :=
  ElevenRUP.step52005 (p 2027) (p 2655) (p 2922) (p 2946) (p 3540) (p 4116) (p 4704) (derived40810 p h) (h 25198)

theorem derived52006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2110) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 4348) :=
  ElevenRUP.step52006 (p 1998) (p 2027) (p 2088) (p 2110) (p 2114) (p 3055) (p 3367) (p 4348) (h 2158) (derived40810 p h) (derived40864 p h) (h 25199)

theorem derived52008 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (¬ p 2972) ∨ (¬ p 4032) ∨ (¬ p 4111) ∨ (¬ p 4365) ∨ (¬ p 4704) :=
  ElevenRUP.step52008 (p 2027) (p 2957) (p 2972) (p 4032) (p 4111) (p 4365) (p 4704) (derived40810 p h) (h 25202)

theorem derived52009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 2946) ∨ (¬ p 3585) ∨ (¬ p 4343) ∨ (¬ p 4704) :=
  ElevenRUP.step52009 (p 2027) (p 2737) (p 2811) (p 2946) (p 3585) (p 4343) (p 4704) (derived40810 p h) (h 25203)

theorem derived52012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2573) ∨ (¬ p 3276) ∨ (¬ p 4118) ∨ (¬ p 4191) ∨ (¬ p 4330) ∨ (¬ p 4360) ∨ (¬ p 4422) ∨ (¬ p 5190) :=
  ElevenRUP.step52012 (p 2027) (p 2247) (p 2573) (p 3276) (p 4118) (p 4191) (p 4330) (p 4360) (p 4422) (p 5190) (derived40810 p h) (h 25207)

theorem derived52014 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3859) ∨ (¬ p 4111) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4975) :=
  ElevenRUP.step52014 (p 2027) (p 3073) (p 3859) (p 4111) (p 4118) (p 4196) (p 4975) (derived40810 p h) (h 25211)

theorem derived52015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2563) ∨ (¬ p 2870) ∨ (¬ p 4235) :=
  ElevenRUP.step52015 (p 1990) (p 2027) (p 2132) (p 2563) (p 2611) (p 2870) (p 4235) (h 2150) (derived40810 p h) (derived40877 p h) (h 25212)

theorem derived52016 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2573) ∨ (¬ p 3201) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 4710) :=
  ElevenRUP.step52016 (p 1998) (p 2027) (p 2177) (p 2573) (p 2611) (p 3201) (p 3362) (p 3584) (p 4710) (h 2158) (derived40810 p h) (derived40877 p h) (h 25213)

theorem derived52017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3136) ∨ (¬ p 3364) ∨ (¬ p 3584) ∨ (¬ p 4116) ∨ (¬ p 4704) :=
  ElevenRUP.step52017 (p 2027) (p 2493) (p 3136) (p 3364) (p 3584) (p 4116) (p 4704) (derived40810 p h) (h 25214)

theorem derived52018 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2584) ∨ (¬ p 2656) ∨ (¬ p 3136) ∨ (¬ p 3822) ∨ (¬ p 4704) ∨ (¬ p 4841) :=
  ElevenRUP.step52018 (p 2027) (p 2307) (p 2584) (p 2656) (p 3136) (p 3822) (p 4704) (p 4841) (derived40810 p h) (h 25215)

theorem derived52019 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2505) ∨ (¬ p 3136) ∨ (¬ p 3319) ∨ (¬ p 3917) ∨ (¬ p 4116) ∨ (¬ p 4704) ∨ (¬ p 4841) :=
  ElevenRUP.step52019 (p 2027) (p 2505) (p 3136) (p 3319) (p 3917) (p 4116) (p 4704) (p 4841) (derived40810 p h) (h 25217)

theorem derived52021 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3644) ∨ (¬ p 3684) ∨ (¬ p 4646) ∨ (¬ p 5085) :=
  ElevenRUP.step52021 (p 2027) (p 2717) (p 3644) (p 3684) (p 4646) (p 5085) (derived40810 p h) (h 25219)

theorem derived52023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3555) ∨ (¬ p 3744) ∨ (¬ p 4173) ∨ (¬ p 4620) ∨ (¬ p 4733) :=
  ElevenRUP.step52023 (p 2027) (p 2295) (p 2696) (p 2797) (p 3555) (p 3744) (p 4173) (p 4620) (p 4733) (derived40810 p h) (h 25221)

theorem derived52025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2589) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3690) ∨ (¬ p 4235) ∨ (¬ p 4669) ∨ (¬ p 4729) :=
  ElevenRUP.step52025 (p 2027) (p 2363) (p 2589) (p 2774) (p 2819) (p 3690) (p 4235) (p 4669) (p 4729) (derived40810 p h) (h 25223)

theorem derived52026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3690) ∨ (¬ p 3941) ∨ (¬ p 4445) ∨ (¬ p 5122) :=
  ElevenRUP.step52026 (p 2027) (p 2881) (p 3690) (p 3941) (p 4445) (p 5122) (derived40810 p h) (h 25224)

theorem derived52029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 3125) ∨ (¬ p 3297) ∨ (¬ p 4035) ∨ (¬ p 4564) ∨ (¬ p 5379) :=
  ElevenRUP.step52029 (p 2027) (p 2797) (p 3125) (p 3297) (p 4035) (p 4564) (p 5379) (derived40810 p h) (h 25228)

theorem derived52030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3097) ∨ (¬ p 3256) ∨ (¬ p 3646) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step52030 (p 2027) (p 2145) (p 2696) (p 3005) (p 3097) (p 3256) (p 3646) (p 4107) (p 4669) (derived40810 p h) (h 25229)

theorem derived52032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2459) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3363) ∨ (¬ p 3683) :=
  ElevenRUP.step52032 (p 2010) (p 2027) (p 2437) (p 2459) (p 2476) (p 2534) (p 2633) (p 3363) (p 3683) (h 2170) (derived40810 p h) (derived40879 p h) (h 25231)

theorem derived52033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2797) ∨ (¬ p 3177) ∨ (¬ p 3877) ∨ (¬ p 4170) ∨ (¬ p 4564) :=
  ElevenRUP.step52033 (p 2027) (p 2187) (p 2797) (p 3177) (p 3877) (p 4170) (p 4564) (derived40810 p h) (h 25232)

theorem derived52034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 3952) ∨ (¬ p 3954) ∨ (¬ p 4393) ∨ (¬ p 5254) :=
  ElevenRUP.step52034 (p 2027) (p 2252) (p 2750) (p 2952) (p 3707) (p 3830) (p 3952) (p 3954) (p 4393) (p 5254) (derived40810 p h) (h 25233)

theorem derived52038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2509) ∨ (¬ p 3055) ∨ (¬ p 5214) ∨ (¬ p 5373) :=
  ElevenRUP.step52038 (p 2027) (p 2098) (p 2509) (p 3055) (p 5214) (p 5373) (derived40810 p h) (h 25237)

theorem derived52042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 3256) ∨ (¬ p 3955) ∨ (¬ p 4341) ∨ (¬ p 4347) ∨ (¬ p 4976) :=
  ElevenRUP.step52042 (p 2027) (p 2588) (p 3256) (p 3955) (p 4341) (p 4347) (p 4976) (derived40810 p h) (h 25241)

theorem derived52043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2870) ∨ (¬ p 2957) ∨ (¬ p 3556) ∨ (¬ p 4313) ∨ (¬ p 4704) :=
  ElevenRUP.step52043 (p 2027) (p 2810) (p 2870) (p 2957) (p 3556) (p 4313) (p 4704) (derived40810 p h) (h 25243)

theorem derived52044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2396) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4786) :=
  ElevenRUP.step52044 (p 2027) (p 2138) (p 2295) (p 2331) (p 2396) (p 3692) (p 3694) (p 3950) (p 4786) (derived40810 p h) (h 25244)

theorem derived52046 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2958) ∨ (¬ p 3051) ∨ (¬ p 4320) ∨ (¬ p 4704) :=
  ElevenRUP.step52046 (p 2027) (p 2657) (p 2958) (p 3051) (p 4320) (p 4704) (derived40810 p h) (h 25246)

theorem derived52047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2534) ∨ (¬ p 2780) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3822) ∨ (¬ p 4420) ∨ (¬ p 4786) :=
  ElevenRUP.step52047 (p 2027) (p 2299) (p 2534) (p 2780) (p 3166) (p 3256) (p 3822) (p 4420) (p 4786) (derived40810 p h) (h 25247)

theorem derived52048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3989) ∨ (p 4601) :=
  ElevenRUP.step52048 (p 1990) (p 3128) (p 3989) (p 4601) (h 2150) (derived40894 p h) (h 25248)

theorem derived52049 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2743) ∨ (¬ p 3361) ∨ (¬ p 3414) ∨ (¬ p 3641) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4737) :=
  ElevenRUP.step52049 (p 2027) (p 2528) (p 2598) (p 2743) (p 3361) (p 3414) (p 3641) (p 3947) (p 4669) (p 4737) (derived40810 p h) (h 25249)

theorem derived52050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2992) ∨ (¬ p 3402) ∨ (¬ p 3641) ∨ (¬ p 4343) ∨ (¬ p 4704) :=
  ElevenRUP.step52050 (p 2027) (p 2509) (p 2992) (p 3402) (p 3641) (p 4343) (p 4704) (derived40810 p h) (h 25250)

theorem derived52051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3333) ∨ (¬ p 3367) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4332) ∨ (¬ p 4348) ∨ (¬ p 4524) :=
  ElevenRUP.step52051 (p 2027) (p 2608) (p 3333) (p 3367) (p 3556) (p 3570) (p 4332) (p 4348) (p 4524) (derived40810 p h) (h 25251)

theorem derived52052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3568) ∨ (¬ p 3956) ∨ (¬ p 4347) :=
  ElevenRUP.step52052 (p 1980) (p 2027) (p 2553) (p 2766) (p 3568) (p 3956) (p 4347) (h 2140) (derived40810 p h) (derived40884 p h) (h 25252)

theorem derived52055 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2298) ∨ (¬ p 2553) ∨ (¬ p 3570) ∨ (¬ p 4204) ∨ (¬ p 4718) :=
  ElevenRUP.step52055 (p 2027) (p 2264) (p 2298) (p 2553) (p 3570) (p 4204) (p 4718) (derived40810 p h) (h 25255)

theorem derived52056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3016) ∨ (¬ p 3958) ∨ (¬ p 4256) ∨ (¬ p 4432) :=
  ElevenRUP.step52056 (p 2027) (p 2187) (p 3016) (p 3958) (p 4256) (p 4432) (derived40810 p h) (h 25256)

theorem derived52058 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4108) ∨ (¬ p 4376) :=
  ElevenRUP.step52058 (p 2027) (p 2608) (p 2922) (p 3540) (p 4108) (p 4376) (derived40810 p h) (h 25258)

theorem derived52059 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2811) ∨ (¬ p 2958) ∨ (¬ p 3051) ∨ (¬ p 3486) ∨ (¬ p 4282) ∨ (¬ p 4704) :=
  ElevenRUP.step52059 (p 2027) (p 2810) (p 2811) (p 2958) (p 3051) (p 3486) (p 4282) (p 4704) (derived40810 p h) (h 25259)

theorem derived52061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2553) ∨ (¬ p 2641) ∨ (¬ p 3567) ∨ (¬ p 3956) :=
  ElevenRUP.step52061 (p 1975) (p 2027) (p 2383) (p 2553) (p 2641) (p 2688) (p 3567) (p 3956) (h 2135) (derived40810 p h) (derived40880 p h) (h 25262)

theorem derived52062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3742) ∨ (¬ p 4111) ∨ (¬ p 4279) ∨ (¬ p 5207) :=
  ElevenRUP.step52062 (p 2027) (p 2247) (p 3742) (p 4111) (p 4279) (p 5207) (derived40810 p h) (h 25265)

theorem derived52066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3690) ∨ (¬ p 4042) ∨ (¬ p 4235) ∨ (¬ p 4666) :=
  ElevenRUP.step52066 (p 2027) (p 2373) (p 3690) (p 4042) (p 4235) (p 4666) (derived40810 p h) (h 25269)

theorem derived52067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3641) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4669) :=
  ElevenRUP.step52067 (p 2027) (p 2241) (p 2528) (p 2598) (p 2750) (p 2753) (p 3641) (p 3817) (p 4366) (p 4669) (derived40810 p h) (h 25270)

theorem derived52068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2396) ∨ (¬ p 2427) ∨ (¬ p 4110) ∨ (¬ p 4140) ∨ (¬ p 4399) :=
  ElevenRUP.step52068 (p 1983) (p 2027) (p 2156) (p 2233) (p 2396) (p 2427) (p 4110) (p 4140) (p 4399) (h 2143) (derived40810 p h) (derived40868 p h) (h 25271)

theorem derived52069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3073) ∨ (¬ p 3949) ∨ (¬ p 4498) ∨ (¬ p 4948) :=
  ElevenRUP.step52069 (p 2027) (p 2373) (p 3073) (p 3949) (p 4498) (p 4948) (derived40810 p h) (h 25272)

theorem derived52071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2963) ∨ (¬ p 3549) ∨ (¬ p 3922) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step52071 (p 2027) (p 2249) (p 2470) (p 2528) (p 2656) (p 2727) (p 2963) (p 3549) (p 3922) (p 4107) (p 4669) (derived40810 p h) (h 25274)

theorem derived52072 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2528) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3292) ∨ (¬ p 3363) ∨ (¬ p 3461) ∨ (¬ p 3641) ∨ (¬ p 4604) ∨ (¬ p 5284) :=
  ElevenRUP.step52072 (p 2027) (p 2249) (p 2528) (p 2656) (p 2727) (p 3292) (p 3363) (p 3461) (p 3641) (p 4604) (p 5284) (derived40810 p h) (h 25275)

theorem derived52073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2761) ∨ (¬ p 3414) ∨ (¬ p 3564) ∨ (¬ p 4429) ∨ (¬ p 4621) ∨ (¬ p 5284) :=
  ElevenRUP.step52073 (p 2027) (p 2249) (p 2573) (p 2656) (p 2727) (p 2761) (p 3414) (p 3564) (p 4429) (p 4621) (p 5284) (derived40810 p h) (h 25276)

theorem derived52074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step52074 (p 2027) (p 2249) (p 2470) (p 2528) (p 2656) (p 2727) (p 2963) (p 3324) (p 5118) (p 5580) (derived40810 p h) (h 25277)

theorem derived52075 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2963) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3549) ∨ (¬ p 3922) ∨ (¬ p 4260) ∨ (¬ p 4831) :=
  ElevenRUP.step52075 (p 2027) (p 2249) (p 2656) (p 2727) (p 2963) (p 3276) (p 3355) (p 3549) (p 3922) (p 4260) (p 4831) (derived40810 p h) (h 25278)

theorem derived52077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 3212) ∨ (¬ p 3680) ∨ (¬ p 4399) ∨ (¬ p 4444) :=
  ElevenRUP.step52077 (p 1982) (p 2027) (p 2622) (p 2630) (p 2656) (p 3212) (p 3680) (p 4399) (p 4444) (h 2142) (derived40810 p h) (derived40878 p h) (h 25280)

theorem derived52078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2952) ∨ (¬ p 3379) ∨ (¬ p 3690) ∨ (¬ p 4320) ∨ (¬ p 4669) :=
  ElevenRUP.step52078 (p 2027) (p 2254) (p 2518) (p 2528) (p 2952) (p 3379) (p 3690) (p 4320) (p 4669) (derived40810 p h) (h 25281)

theorem derived52080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2663) ∨ (¬ p 2743) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3361) ∨ (¬ p 3540) ∨ (¬ p 3553) ∨ (¬ p 3579) ∨ (¬ p 4418) ∨ (¬ p 4668) ∨ (¬ p 4737) :=
  ElevenRUP.step52080 (p 2027) (p 2132) (p 2663) (p 2743) (p 2891) (p 3246) (p 3361) (p 3540) (p 3553) (p 3579) (p 4418) (p 4668) (p 4737) (derived40810 p h) (h 25283)

theorem derived52085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 2901) ∨ (¬ p 3379) ∨ (¬ p 3497) ∨ (¬ p 3556) ∨ (¬ p 4134) ∨ (¬ p 4524) :=
  ElevenRUP.step52085 (p 2027) (p 2352) (p 2493) (p 2901) (p 3379) (p 3497) (p 3556) (p 4134) (p 4524) (derived40810 p h) (h 25289)

theorem derived52086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3019) ∨ (¬ p 3323) ∨ (¬ p 3527) ∨ (¬ p 3644) ∨ (¬ p 4026) ∨ (¬ p 4452) :=
  ElevenRUP.step52086 (p 2010) (p 2027) (p 2545) (p 3019) (p 3323) (p 3527) (p 3644) (p 4026) (p 4452) (h 2170) (derived40810 p h) (derived40876 p h) (h 25290)

theorem derived52087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 2252) ∨ (¬ p 2363) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2819) ∨ (¬ p 3742) ∨ (¬ p 4278) ∨ (¬ p 4428) ∨ (¬ p 4669) :=
  ElevenRUP.step52087 (p 2027) (p 2144) (p 2156) (p 2252) (p 2363) (p 2657) (p 2750) (p 2753) (p 2819) (p 3742) (p 4278) (p 4428) (p 4669) (derived40810 p h) (h 25291)

theorem derived52088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3379) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52088 (p 2027) (p 2363) (p 2753) (p 2774) (p 2819) (p 3379) (p 3817) (p 4366) (p 4669) (p 5216) (derived40810 p h) (h 25292)

theorem derived52090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2952) ∨ (¬ p 3537) ∨ (¬ p 3609) ∨ (¬ p 3690) ∨ (¬ p 4320) ∨ (¬ p 4669) :=
  ElevenRUP.step52090 (p 2027) (p 2254) (p 2608) (p 2952) (p 3537) (p 3609) (p 3690) (p 4320) (p 4669) (derived40810 p h) (h 25294)

theorem derived52091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2657) ∨ (¬ p 3537) ∨ (¬ p 3609) ∨ (¬ p 3742) ∨ (¬ p 4278) ∨ (¬ p 4669) :=
  ElevenRUP.step52091 (p 2027) (p 2254) (p 2608) (p 2657) (p 3537) (p 3609) (p 3742) (p 4278) (p 4669) (derived40810 p h) (h 25295)

theorem derived52092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2963) ∨ (¬ p 3537) ∨ (¬ p 3568) ∨ (¬ p 3609) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step52092 (p 2027) (p 2254) (p 2608) (p 2963) (p 3537) (p 3568) (p 3609) (p 4107) (p 4669) (derived40810 p h) (h 25296)

theorem derived52093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3954) ∨ (¬ p 4256) ∨ (¬ p 4330) :=
  ElevenRUP.step52093 (p 2027) (p 2252) (p 2534) (p 2657) (p 2750) (p 3093) (p 3319) (p 3954) (p 4256) (p 4330) (derived40810 p h) (h 25298)

theorem derived52094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3323) ∨ (¬ p 3834) ∨ (¬ p 5148) :=
  ElevenRUP.step52094 (p 1975) (p 2027) (p 2287) (p 3093) (p 3309) (p 3323) (p 3834) (p 5148) (h 2135) (derived40810 p h) (derived40869 p h) (h 25299)

theorem derived52095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2528) ∨ (¬ p 2748) ∨ (¬ p 2761) ∨ (¬ p 3055) ∨ (¬ p 3368) ∨ (¬ p 4039) ∨ (¬ p 4363) ∨ (¬ p 4669) ∨ (¬ p 4749) ∨ (¬ p 5284) ∨ (¬ p 5373) :=
  ElevenRUP.step52095 (p 2027) (p 2098) (p 2528) (p 2748) (p 2761) (p 3055) (p 3368) (p 4039) (p 4363) (p 4669) (p 4749) (p 5284) (p 5373) (derived40810 p h) (h 25300)

theorem derived52096 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3556) ∨ (¬ p 3694) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4524) :=
  ElevenRUP.step52096 (p 2027) (p 2870) (p 3073) (p 3449) (p 3556) (p 3694) (p 4134) (p 4347) (p 4524) (derived40810 p h) (h 25301)

theorem derived52097 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52097 (p 2027) (p 2363) (p 3063) (p 3093) (p 3365) (p 3572) (p 3947) (p 4669) (p 4736) (derived40810 p h) (h 25302)

theorem derived52098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 2870) ∨ (¬ p 2922) ∨ (¬ p 3556) ∨ (¬ p 3758) ∨ (¬ p 4079) ∨ (¬ p 4524) :=
  ElevenRUP.step52098 (p 1983) (p 2027) (p 2417) (p 2499) (p 2573) (p 2765) (p 2870) (p 2922) (p 3556) (p 3758) (p 4079) (p 4524) (h 2143) (derived40810 p h) (derived40883 p h) (h 25303)

theorem derived52100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2459) ∨ (¬ p 2598) ∨ (¬ p 3414) ∨ (¬ p 3537) ∨ (¬ p 3585) ∨ (¬ p 3589) ∨ (¬ p 3919) ∨ (¬ p 4118) ∨ (¬ p 4802) :=
  ElevenRUP.step52100 (p 2027) (p 2254) (p 2459) (p 2598) (p 3414) (p 3537) (p 3585) (p 3589) (p 3919) (p 4118) (p 4802) (derived40810 p h) (h 25305)

theorem derived52102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3073) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4376) ∨ (¬ p 4669) :=
  ElevenRUP.step52102 (p 2027) (p 2138) (p 3073) (p 3366) (p 3449) (p 3452) (p 3690) (p 4244) (p 4376) (p 4669) (derived40810 p h) (h 25309)

theorem derived52103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4376) ∨ (¬ p 4669) :=
  ElevenRUP.step52103 (p 2027) (p 3073) (p 3365) (p 3366) (p 3449) (p 3452) (p 3572) (p 3947) (p 4376) (p 4669) (derived40810 p h) (h 25310)

theorem derived52104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4376) ∨ (¬ p 4669) :=
  ElevenRUP.step52104 (p 2027) (p 2352) (p 2363) (p 2573) (p 3365) (p 3366) (p 3519) (p 3572) (p 3947) (p 4376) (p 4669) (derived40810 p h) (h 25311)

theorem derived52105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3958) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 4334) :=
  ElevenRUP.step52105 (p 2027) (p 3680) (p 3958) (p 4137) (p 4191) (p 4334) (derived40810 p h) (h 25312)

theorem derived52106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2761) ∨ (¬ p 3292) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 4669) ∨ (¬ p 5284) :=
  ElevenRUP.step52106 (p 2027) (p 2352) (p 2363) (p 2573) (p 2761) (p 3292) (p 4236) (p 4419) (p 4669) (p 5284) (derived40810 p h) (h 25313)

theorem derived52108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2780) ∨ (¬ p 3146) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52108 (p 2027) (p 2166) (p 2210) (p 2780) (p 3146) (p 3822) (p 4107) (p 4669) (p 4736) (derived40810 p h) (h 25315)

theorem derived52109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2579) ∨ (¬ p 2807) ∨ (¬ p 3422) ∨ (¬ p 3570) ∨ (¬ p 3876) ∨ (¬ p 3905) ∨ (¬ p 4647) ∨ (¬ p 4786) :=
  ElevenRUP.step52109 (p 2027) (p 2264) (p 2579) (p 2807) (p 3422) (p 3570) (p 3876) (p 3905) (p 4647) (p 4786) (derived40810 p h) (h 25316)

theorem derived52110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 3363) ∨ (¬ p 3540) ∨ (¬ p 3585) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4737) :=
  ElevenRUP.step52110 (p 2027) (p 2696) (p 2742) (p 3189) (p 3256) (p 3363) (p 3540) (p 3585) (p 4278) (p 4669) (p 4737) (derived40810 p h) (h 25317)

theorem derived52112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 3105) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4348) ∨ (¬ p 4450) ∨ (¬ p 5193) :=
  ElevenRUP.step52112 (p 2027) (p 2608) (p 2839) (p 3105) (p 3540) (p 3644) (p 4348) (p 4450) (p 5193) (derived40810 p h) (h 25319)

theorem derived52113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3055) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4786) ∨ (¬ p 5123) :=
  ElevenRUP.step52113 (p 2027) (p 2331) (p 3055) (p 3323) (p 3461) (p 3874) (p 4286) (p 4786) (p 5123) (derived40810 p h) (h 25320)

theorem derived52114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 3055) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4786) :=
  ElevenRUP.step52114 (p 2027) (p 2331) (p 2363) (p 2668) (p 3055) (p 3876) (p 4278) (p 4669) (p 4786) (derived40810 p h) (h 25321)

theorem derived52115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 3905) ∨ (¬ p 4786) ∨ (¬ p 4905) :=
  ElevenRUP.step52115 (p 2027) (p 2177) (p 2295) (p 2331) (p 2476) (p 2534) (p 3146) (p 3905) (p 4786) (p 4905) (derived40810 p h) (h 25323)

theorem derived52118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2807) ∨ (¬ p 3744) ∨ (¬ p 3758) ∨ (¬ p 4604) ∨ (¬ p 4786) :=
  ElevenRUP.step52118 (p 2027) (p 2138) (p 2264) (p 2459) (p 2807) (p 3744) (p 3758) (p 4604) (p 4786) (derived40810 p h) (h 25326)

theorem derived52119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (¬ p 3758) ∨ (¬ p 4393) ∨ (¬ p 4786) ∨ (¬ p 5254) :=
  ElevenRUP.step52119 (p 2027) (p 2138) (p 3166) (p 3256) (p 3266) (p 3758) (p 4393) (p 4786) (p 5254) (derived40810 p h) (h 25327)

theorem derived52126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3073) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4376) ∨ (¬ p 4669) :=
  ElevenRUP.step52126 (p 2027) (p 2780) (p 3073) (p 3366) (p 3449) (p 3452) (p 3822) (p 4107) (p 4376) (p 4669) (derived40810 p h) (h 25335)

theorem derived52127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 2608) ∨ (¬ p 3146) ∨ (¬ p 3519) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4376) ∨ (¬ p 4669) :=
  ElevenRUP.step52127 (p 2027) (p 2230) (p 2373) (p 2608) (p 3146) (p 3519) (p 3817) (p 4366) (p 4376) (p 4669) (derived40810 p h) (h 25336)

theorem derived52128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4419) ∨ (¬ p 4669) :=
  ElevenRUP.step52128 (p 2027) (p 2230) (p 2373) (p 3146) (p 3365) (p 3572) (p 3947) (p 4419) (p 4669) (derived40810 p h) (h 25337)

theorem derived52129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4669) :=
  ElevenRUP.step52129 (p 2027) (p 2139) (p 2156) (p 2187) (p 2363) (p 3365) (p 3572) (p 3947) (p 4669) (derived40810 p h) (h 25338)

theorem derived52130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4377) ∨ (¬ p 4446) ∨ (¬ p 4669) :=
  ElevenRUP.step52130 (p 2027) (p 3146) (p 3365) (p 3366) (p 3449) (p 3555) (p 3572) (p 3947) (p 4377) (p 4446) (p 4669) (derived40810 p h) (h 25339)

theorem derived52131 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2427) ∨ (¬ p 3646) ∨ (¬ p 3880) ∨ (¬ p 4558) :=
  ElevenRUP.step52131 (p 2027) (p 2220) (p 2427) (p 3646) (p 3880) (p 4558) (derived40810 p h) (h 25340)

theorem derived52132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3146) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3683) ∨ (¬ p 3876) ∨ (¬ p 4236) ∨ (¬ p 4278) ∨ (¬ p 4377) ∨ (¬ p 4446) ∨ (¬ p 4669) :=
  ElevenRUP.step52132 (p 2027) (p 2657) (p 3146) (p 3366) (p 3449) (p 3555) (p 3683) (p 3876) (p 4236) (p 4278) (p 4377) (p 4446) (p 4669) (derived40810 p h) (h 25342)

theorem derived52134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 2533) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3680) ∨ (¬ p 3947) ∨ (¬ p 4444) ∨ (¬ p 4669) :=
  ElevenRUP.step52134 (p 2027) (p 2139) (p 2220) (p 2533) (p 3365) (p 3572) (p 3680) (p 3947) (p 4444) (p 4669) (derived40810 p h) (h 25344)

theorem derived52137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52137 (p 2027) (p 2166) (p 2210) (p 3146) (p 3365) (p 3572) (p 3947) (p 4669) (p 4736) (derived40810 p h) (h 25347)

theorem derived52138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2230) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4034) ∨ (¬ p 4079) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52138 (p 2027) (p 2166) (p 2230) (p 3146) (p 3365) (p 3572) (p 3947) (p 4034) (p 4079) (p 4669) (p 4736) (derived40810 p h) (h 25348)

theorem derived52145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52145 (p 2027) (p 2166) (p 2210) (p 3055) (p 3146) (p 3876) (p 4278) (p 4669) (p 4736) (derived40810 p h) (h 25355)

theorem derived52147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2780) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4736) :=
  ElevenRUP.step52147 (p 2027) (p 2241) (p 2780) (p 3189) (p 3256) (p 3822) (p 4107) (p 4669) (p 4736) (derived40810 p h) (h 25357)

theorem derived52148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2531) ∨ (¬ p 2589) ∨ (¬ p 2850) ∨ (¬ p 3146) :=
  ElevenRUP.step52148 (p 1982) (p 2027) (p 2470) (p 2531) (p 2589) (p 2842) (p 2850) (p 3146) (h 2142) (derived40810 p h) (derived40885 p h) (h 25358)

theorem derived52150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3584) ∨ (¬ p 4137) ∨ (¬ p 4604) ∨ (¬ p 4786) :=
  ElevenRUP.step52150 (p 2027) (p 2946) (p 3055) (p 3146) (p 3156) (p 3584) (p 4137) (p 4604) (p 4786) (derived40810 p h) (h 25360)

theorem derived52151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3346) ∨ (¬ p 3461) ∨ (¬ p 3905) ∨ (¬ p 4425) ∨ (¬ p 4604) ∨ (¬ p 4786) :=
  ElevenRUP.step52151 (p 2027) (p 2946) (p 3146) (p 3156) (p 3346) (p 3461) (p 3905) (p 4425) (p 4604) (p 4786) (derived40810 p h) (h 25361)

theorem derived52152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2579) ∨ (¬ p 2807) ∨ (¬ p 3905) ∨ (¬ p 3941) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 4786) ∨ (¬ p 5119) :=
  ElevenRUP.step52152 (p 2027) (p 2264) (p 2579) (p 2807) (p 3905) (p 3941) (p 4137) (p 4191) (p 4786) (p 5119) (derived40810 p h) (h 25362)

theorem derived52153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2946) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3422) ∨ (¬ p 3905) ∨ (¬ p 4697) ∨ (¬ p 4786) ∨ (¬ p 5160) :=
  ElevenRUP.step52153 (p 2027) (p 2579) (p 2946) (p 3146) (p 3156) (p 3422) (p 3905) (p 4697) (p 4786) (p 5160) (derived40810 p h) (h 25363)

theorem derived52155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2780) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3822) ∨ (¬ p 4786) ∨ (¬ p 4902) :=
  ElevenRUP.step52155 (p 2027) (p 2299) (p 2780) (p 3166) (p 3256) (p 3692) (p 3822) (p 4786) (p 4902) (derived40810 p h) (h 25366)

theorem derived52156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2743) ∨ (¬ p 3452) ∨ (¬ p 3589) ∨ (¬ p 4376) :=
  ElevenRUP.step52156 (p 2027) (p 2696) (p 2743) (p 3452) (p 3589) (p 4376) (derived40810 p h) (h 25367)

theorem derived52157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2373) ∨ (¬ p 2996) ∨ (¬ p 3146) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 5190) :=
  ElevenRUP.step52157 (p 2027) (p 2230) (p 2247) (p 2373) (p 2996) (p 3146) (p 3947) (p 4669) (p 5190) (derived40810 p h) (h 25368)

theorem derived52160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 3941) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 4786) ∨ (¬ p 5119) :=
  ElevenRUP.step52160 (p 2027) (p 2138) (p 2264) (p 2807) (p 3941) (p 4322) (p 4385) (p 4786) (p 5119) (derived40810 p h) (h 25372)

theorem derived52161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2406) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 2996) ∨ (¬ p 4281) :=
  ElevenRUP.step52161 (p 1994) (p 2027) (p 2253) (p 2406) (p 2440) (p 2699) (p 2807) (p 2996) (p 4281) (h 2154) (derived40810 p h) (derived40881 p h) (h 25373)

theorem derived52162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2727) ∨ (¬ p 3083) ∨ (¬ p 3692) ∨ (¬ p 4120) ∨ (¬ p 4420) ∨ (¬ p 4524) :=
  ElevenRUP.step52162 (p 2027) (p 2241) (p 2459) (p 2727) (p 3083) (p 3692) (p 4120) (p 4420) (p 4524) (derived40810 p h) (h 25374)

theorem derived52163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2299) ∨ (¬ p 2727) ∨ (¬ p 3083) ∨ (¬ p 3097) ∨ (¬ p 3646) ∨ (¬ p 4420) ∨ (¬ p 4524) :=
  ElevenRUP.step52163 (p 2027) (p 2241) (p 2299) (p 2727) (p 3083) (p 3097) (p 3646) (p 4420) (p 4524) (derived40810 p h) (h 25375)

theorem derived52165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4669) ∨ (¬ p 4786) :=
  ElevenRUP.step52165 (p 2027) (p 2138) (p 2528) (p 2651) (p 3083) (p 3690) (p 4244) (p 4669) (p 4786) (derived40810 p h) (h 25377)

theorem derived52166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2870) ∨ (¬ p 3323) ∨ (¬ p 3556) ∨ (¬ p 4368) ∨ (¬ p 4385) ∨ (¬ p 4524) :=
  ElevenRUP.step52166 (p 2027) (p 2241) (p 2641) (p 2870) (p 3323) (p 3556) (p 4368) (p 4385) (p 4524) (derived40810 p h) (h 25378)

theorem derived52167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 2761) ∨ (¬ p 4032) ∨ (¬ p 4322) ∨ (¬ p 4669) ∨ (¬ p 4786) :=
  ElevenRUP.step52167 (p 2027) (p 2136) (p 2331) (p 2363) (p 2668) (p 2761) (p 4032) (p 4322) (p 4669) (p 4786) (derived40810 p h) (h 25379)

theorem derived52169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2860) ∨ (¬ p 3166) ∨ (¬ p 3506) ∨ (¬ p 3646) ∨ (¬ p 4033) ∨ (¬ p 4385) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 4786) ∨ (¬ p 5111) :=
  ElevenRUP.step52169 (p 2027) (p 2136) (p 2860) (p 3166) (p 3506) (p 3646) (p 4033) (p 4385) (p 4444) (p 4604) (p 4786) (p 5111) (derived40810 p h) (h 25381)

theorem derived52170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2663) ∨ (¬ p 2780) ∨ (¬ p 3343) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4256) ∨ (¬ p 4638) ∨ (¬ p 4786) :=
  ElevenRUP.step52170 (p 2027) (p 2470) (p 2663) (p 2780) (p 3343) (p 3822) (p 4107) (p 4256) (p 4638) (p 4786) (derived40810 p h) (h 25382)

theorem derived52171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2534) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3570) ∨ (¬ p 4244) ∨ (¬ p 4420) ∨ (¬ p 4786) :=
  ElevenRUP.step52171 (p 2027) (p 2138) (p 2534) (p 3166) (p 3256) (p 3570) (p 4244) (p 4420) (p 4786) (derived40810 p h) (h 25383)

theorem derived52172 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2651) ∨ (¬ p 3276) ∨ (¬ p 3343) ∨ (¬ p 4244) ∨ (¬ p 4786) ∨ (¬ p 4831) ∨ (¬ p 5660) :=
  ElevenRUP.step52172 (p 2027) (p 2138) (p 2651) (p 3276) (p 3343) (p 4244) (p 4786) (p 4831) (p 5660) (derived40810 p h) (h 25384)

theorem derived52173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 3744) ∨ (¬ p 3758) ∨ (¬ p 4604) ∨ (¬ p 4786) :=
  ElevenRUP.step52173 (p 2027) (p 2138) (p 2528) (p 2651) (p 3083) (p 3744) (p 3758) (p 4604) (p 4786) (derived40810 p h) (h 25385)

theorem derived52174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 2860) ∨ (¬ p 3083) ∨ (¬ p 3646) ∨ (¬ p 4385) ∨ (¬ p 4786) ∨ (¬ p 5059) :=
  ElevenRUP.step52174 (p 2027) (p 2136) (p 2528) (p 2651) (p 2860) (p 3083) (p 3646) (p 4385) (p 4786) (p 5059) (derived40810 p h) (h 25386)

theorem derived52176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 4149) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 4786) ∨ (¬ p 5119) :=
  ElevenRUP.step52176 (p 2027) (p 2138) (p 2651) (p 3083) (p 4149) (p 4322) (p 4385) (p 4786) (p 5119) (derived40810 p h) (h 25388)

theorem derived52178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2588) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3646) ∨ (¬ p 4118) ∨ (¬ p 4203) ∨ (¬ p 4524) ∨ (¬ p 4550) :=
  ElevenRUP.step52178 (p 2027) (p 2299) (p 2588) (p 3073) (p 3449) (p 3646) (p 4118) (p 4203) (p 4524) (p 4550) (derived40810 p h) (h 25392)

theorem derived52179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3347) ∨ (¬ p 3365) ∨ (¬ p 3540) ∨ (¬ p 4019) ∨ (¬ p 4030) ∨ (¬ p 4278) ∨ (¬ p 4381) ∨ (¬ p 4752) ∨ (¬ p 5119) :=
  ElevenRUP.step52179 (p 2027) (p 2098) (p 3347) (p 3365) (p 3540) (p 4019) (p 4030) (p 4278) (p 4381) (p 4752) (p 5119) (derived40810 p h) (h 25393)

theorem derived52182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4324) ∨ (¬ p 4669) ∨ (¬ p 5190) :=
  ElevenRUP.step52182 (p 2027) (p 2230) (p 2373) (p 3146) (p 3588) (p 3954) (p 4324) (p 4669) (p 5190) (derived40810 p h) (h 25396)

theorem derived52183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3584) ∨ (¬ p 3609) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4354) :=
  ElevenRUP.step52183 (p 1984) (p 2027) (p 3008) (p 3584) (p 3609) (p 3860) (p 4261) (p 4354) (h 2144) (derived40810 p h) (derived40891 p h) (h 25397)

theorem derived52184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4324) ∨ (¬ p 4669) ∨ (¬ p 5190) :=
  ElevenRUP.step52184 (p 2027) (p 2352) (p 2363) (p 2573) (p 3588) (p 3954) (p 4324) (p 4669) (p 5190) (derived40810 p h) (h 25398)

theorem derived52189 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3690) ∨ (¬ p 4669) :=
  ElevenRUP.step52189 (p 2027) (p 2248) (p 2331) (p 2363) (p 2668) (p 3486) (p 3555) (p 3690) (p 4669) (derived40810 p h) (h 25404)

theorem derived52193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3204) ∨ (¬ p 3471) ∨ (¬ p 3692) ∨ (¬ p 4253) ∨ (¬ p 4441) ∨ (¬ p 4444) ∨ (¬ p 4512) ∨ (¬ p 4877) ∨ (¬ p 5503) :=
  ElevenRUP.step52193 (p 1998) (p 2027) (p 2387) (p 2753) (p 2764) (p 2911) (p 3204) (p 3471) (p 3692) (p 4253) (p 4441) (p 4444) (p 4512) (p 4877) (p 5503) (h 2158) (derived40810 p h) (derived40882 p h) (h 25408)

theorem derived52194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3309) ∨ (¬ p 3690) ∨ (¬ p 4204) ∨ (¬ p 4518) :=
  ElevenRUP.step52194 (p 2027) (p 2396) (p 3309) (p 3690) (p 4204) (p 4518) (derived40810 p h) (h 25409)

theorem derived52195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2542) ∨ (¬ p 2630) ∨ (¬ p 2696) :=
  ElevenRUP.step52195 (p 1985) (p 2027) (p 2427) (p 2542) (p 2611) (p 2630) (p 2696) (h 2145) (derived40810 p h) (derived40877 p h) (h 25410)

theorem derived52198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2528) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4432) ∨ (¬ p 4564) :=
  ElevenRUP.step52198 (p 2027) (p 2187) (p 2528) (p 4118) (p 4196) (p 4432) (p 4564) (derived40810 p h) (h 25413)

theorem derived52199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2922) ∨ (¬ p 3541) ∨ (¬ p 3876) ∨ (¬ p 4752) :=
  ElevenRUP.step52199 (p 2027) (p 2743) (p 2922) (p 3541) (p 3876) (p 4752) (derived40810 p h) (h 25414)

theorem derived52200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2573) ∨ (¬ p 2589) ∨ (¬ p 2743) ∨ (¬ p 3541) :=
  ElevenRUP.step52200 (p 2005) (p 2027) (p 2406) (p 2573) (p 2589) (p 2622) (p 2743) (p 3541) (h 2165) (derived40810 p h) (derived40878 p h) (h 25415)

theorem derived52202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2299) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 4733) ∨ (¬ p 4902) :=
  ElevenRUP.step52202 (p 2027) (p 2098) (p 2299) (p 3549) (p 3591) (p 3609) (p 3692) (p 4733) (p 4902) (derived40810 p h) (h 25417)

theorem derived52203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52203 (p 2027) (p 2696) (p 3005) (p 3256) (p 3549) (p 3591) (p 4107) (p 4669) (p 4733) (derived40810 p h) (h 25419)

theorem derived52204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 3146) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52204 (p 2027) (p 2132) (p 2619) (p 3146) (p 3549) (p 3591) (p 4107) (p 4669) (p 4733) (derived40810 p h) (h 25420)

theorem derived52205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2797) ∨ (¬ p 2807) ∨ (¬ p 3572) ∨ (¬ p 4117) ∨ (¬ p 4564) ∨ (¬ p 4729) :=
  ElevenRUP.step52205 (p 2027) (p 2274) (p 2579) (p 2588) (p 2797) (p 2807) (p 3572) (p 4117) (p 4564) (p 4729) (derived40810 p h) (h 25421)

theorem derived52206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3347) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52206 (p 2027) (p 2579) (p 2588) (p 2696) (p 2753) (p 3005) (p 3256) (p 3347) (p 4107) (p 4669) (p 5216) (derived40810 p h) (h 25422)

theorem derived52208 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2589) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3347) ∨ (¬ p 3880) ∨ (¬ p 5118) ∨ (¬ p 5216) ∨ (¬ p 5568) :=
  ElevenRUP.step52208 (p 2027) (p 2363) (p 2589) (p 2753) (p 2774) (p 2819) (p 3347) (p 3880) (p 5118) (p 5216) (p 5568) (derived40810 p h) (h 25425)

theorem derived52210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2542) ∨ (¬ p 3947) ∨ (¬ p 4112) ∨ (¬ p 4644) :=
  ElevenRUP.step52210 (p 2027) (p 2417) (p 2542) (p 3947) (p 4112) (p 4644) (derived40810 p h) (h 25427)

theorem derived52220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3767) ∨ (¬ p 3960) ∨ (¬ p 4110) ∨ (¬ p 4321) ∨ (¬ p 4430) ∨ (¬ p 4461) ∨ (¬ p 4516) :=
  ElevenRUP.step52220 (p 1997) (p 2027) (p 2177) (p 2997) (p 3767) (p 3960) (p 4110) (p 4321) (p 4430) (p 4461) (p 4516) (h 2157) (derived40810 p h) (derived40890 p h) (h 25441)

theorem derived52223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 3212) ∨ (¬ p 3365) ∨ (¬ p 4030) ∨ (¬ p 4202) ∨ (¬ p 4363) ∨ (¬ p 4752) :=
  ElevenRUP.step52223 (p 2027) (p 2144) (p 3212) (p 3365) (p 4030) (p 4202) (p 4363) (p 4752) (derived40810 p h) (h 25445)

theorem derived52225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2727) ∨ (¬ p 3343) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4332) ∨ (¬ p 4347) ∨ (¬ p 4524) :=
  ElevenRUP.step52225 (p 2027) (p 2241) (p 2727) (p 3343) (p 3646) (p 3989) (p 4332) (p 4347) (p 4524) (derived40810 p h) (h 25449)

theorem derived52226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2449) ∨ (¬ p 2761) ∨ (¬ p 2807) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4786) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step52226 (p 2027) (p 2136) (p 2449) (p 2761) (p 2807) (p 3646) (p 3989) (p 4786) (p 5123) (p 5580) (derived40810 p h) (h 25450)

theorem derived52227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3286) ∨ (¬ p 3506) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4381) ∨ (¬ p 4786) :=
  ElevenRUP.step52227 (p 2027) (p 2138) (p 3286) (p 3506) (p 3692) (p 3694) (p 3950) (p 4381) (p 4786) (derived40810 p h) (h 25451)

theorem derived52228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2960) ∨ (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3051) ∨ (¬ p 3699) :=
  ElevenRUP.step52228 (p 2027) (p 2960) (p 2992) (p 2996) (p 3051) (p 3699) (derived40810 p h) (h 25453)

theorem derived52229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (p 4376) :=
  ElevenRUP.step52229 (p 1992) (p 2699) (p 3379) (p 4376) (h 2152) (derived40881 p h) (h 25454)

theorem derived52230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 5193) :=
  ElevenRUP.step52230 (p 2027) (p 2241) (p 2579) (p 2588) (p 3189) (p 3256) (p 4107) (p 4669) (p 5193) (derived40810 p h) (h 25455)

theorem derived52231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 3246) ∨ (¬ p 3874) ∨ (¬ p 3950) ∨ (¬ p 4786) :=
  ElevenRUP.step52231 (p 2027) (p 2534) (p 2901) (p 2946) (p 3055) (p 3246) (p 3874) (p 3950) (p 4786) (derived40810 p h) (h 25456)

theorem derived52232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2534) ∨ (¬ p 2778) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 4149) ∨ (¬ p 4786) ∨ (¬ p 5580) :=
  ElevenRUP.step52232 (p 1998) (p 2027) (p 2387) (p 2534) (p 2766) (p 2778) (p 2881) (p 2901) (p 2946) (p 4149) (p 4786) (p 5580) (h 2158) (derived40810 p h) (derived40884 p h) (h 25457)

theorem derived52233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 3115) ∨ (¬ p 3680) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4786) ∨ (¬ p 5123) :=
  ElevenRUP.step52233 (p 2027) (p 2946) (p 3055) (p 3115) (p 3680) (p 3874) (p 4286) (p 4786) (p 5123) (derived40810 p h) (h 25458)

theorem derived52234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3905) ∨ (¬ p 3950) ∨ (¬ p 4425) ∨ (¬ p 4786) :=
  ElevenRUP.step52234 (p 2027) (p 2901) (p 2946) (p 3246) (p 3266) (p 3346) (p 3905) (p 3950) (p 4425) (p 4786) (derived40810 p h) (h 25459)

theorem derived52235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3506) ∨ (¬ p 3646) ∨ (¬ p 3842) ∨ (¬ p 3989) ∨ (¬ p 4524) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step52235 (p 2027) (p 2241) (p 3506) (p 3646) (p 3842) (p 3989) (p 4524) (p 5123) (p 5580) (derived40810 p h) (h 25460)

theorem derived52238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3506) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 3842) ∨ (¬ p 4524) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step52238 (p 2027) (p 2241) (p 3506) (p 3556) (p 3570) (p 3842) (p 4524) (p 5123) (p 5558) (derived40810 p h) (h 25463)

theorem derived52239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 3125) ∨ (¬ p 3359) ∨ (¬ p 3958) ∨ (¬ p 4022) :=
  ElevenRUP.step52239 (p 2027) (p 3016) (p 3125) (p 3359) (p 3958) (p 4022) (derived40810 p h) (h 25464)

theorem derived52241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2619) ∨ (¬ p 2651) ∨ (¬ p 3951) ∨ (¬ p 4120) ∨ (¬ p 4385) ∨ (¬ p 4786) :=
  ElevenRUP.step52241 (p 2027) (p 2136) (p 2417) (p 2437) (p 2619) (p 2651) (p 3951) (p 4120) (p 4385) (p 4786) (derived40810 p h) (h 25466)

theorem derived52242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3568) ∨ (¬ p 3872) ∨ (¬ p 4107) ∨ (¬ p 4564) :=
  ElevenRUP.step52242 (p 2027) (p 3246) (p 3568) (p 3872) (p 4107) (p 4564) (derived40810 p h) (h 25470)

theorem derived52243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2608) ∨ (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 3556) ∨ (¬ p 3880) ∨ (¬ p 4134) ∨ (¬ p 4524) :=
  ElevenRUP.step52243 (p 2027) (p 2427) (p 2608) (p 2819) (p 2829) (p 3556) (p 3880) (p 4134) (p 4524) (derived40810 p h) (h 25471)

theorem derived52244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2641) ∨ (¬ p 4360) ∨ (¬ p 4564) ∨ (¬ p 4769) :=
  ElevenRUP.step52244 (p 2027) (p 2187) (p 2641) (p 4360) (p 4564) (p 4769) (derived40810 p h) (h 25472)

theorem derived52245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 4278) ∨ (¬ p 4521) ∨ (¬ p 4669) :=
  ElevenRUP.step52245 (p 2027) (p 2156) (p 2187) (p 2363) (p 2928) (p 3452) (p 4278) (p 4521) (p 4669) (derived40810 p h) (h 25473)

theorem derived52246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2748) ∨ (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 2996) ∨ (¬ p 3365) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4734) :=
  ElevenRUP.step52246 (p 2027) (p 2363) (p 2748) (p 2819) (p 2829) (p 2996) (p 3365) (p 3947) (p 4669) (p 4734) (derived40810 p h) (h 25475)

theorem derived52247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 3055) ∨ (¬ p 3791) ∨ (¬ p 4425) ∨ (¬ p 4786) ∨ (¬ p 4826) ∨ (¬ p 5160) :=
  ElevenRUP.step52247 (p 2027) (p 2295) (p 2331) (p 3055) (p 3791) (p 4425) (p 4786) (p 4826) (p 5160) (derived40810 p h) (h 25476)

theorem derived52249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3905) ∨ (¬ p 3950) ∨ (¬ p 5164) ∨ (¬ p 5387) :=
  ElevenRUP.step52249 (p 2027) (p 2139) (p 2156) (p 2274) (p 2396) (p 3266) (p 3346) (p 3905) (p 3950) (p 5164) (p 5387) (derived40810 p h) (h 25478)

theorem derived52250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 3055) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4666) ∨ (¬ p 4786) :=
  ElevenRUP.step52250 (p 2027) (p 2177) (p 2295) (p 2331) (p 3055) (p 3876) (p 4278) (p 4666) (p 4786) (derived40810 p h) (h 25479)

theorem derived52251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3379) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52251 (p 2027) (p 2132) (p 2619) (p 2753) (p 3146) (p 3379) (p 3817) (p 4366) (p 4669) (p 5216) (derived40810 p h) (h 25480)

theorem derived52252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3146) ∨ (¬ p 3346) ∨ (¬ p 3347) ∨ (¬ p 4425) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52252 (p 2027) (p 2132) (p 2619) (p 2753) (p 2761) (p 3146) (p 3346) (p 3347) (p 4425) (p 4669) (p 5216) (derived40810 p h) (h 25481)

theorem derived52253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 2619) ∨ (¬ p 2749) ∨ (¬ p 2946) ∨ (¬ p 3146) ∨ (¬ p 3347) ∨ (¬ p 4137) ∨ (¬ p 4316) ∨ (¬ p 4396) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52253 (p 2027) (p 2246) (p 2313) (p 2553) (p 2577) (p 2619) (p 2749) (p 2946) (p 3146) (p 3347) (p 4137) (p 4316) (p 4396) (p 4669) (p 5216) (derived40810 p h) (h 25482)

theorem derived52254 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3346) ∨ (¬ p 3347) ∨ (¬ p 4425) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52254 (p 2027) (p 2696) (p 2753) (p 2761) (p 3005) (p 3256) (p 3346) (p 3347) (p 4425) (p 4669) (p 5216) (derived40810 p h) (h 25484)

theorem derived52255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3347) ∨ (¬ p 4137) ∨ (¬ p 4604) ∨ (¬ p 5216) :=
  ElevenRUP.step52255 (p 2027) (p 2313) (p 2553) (p 2577) (p 2696) (p 2753) (p 3005) (p 3256) (p 3347) (p 4137) (p 4604) (p 5216) (derived40810 p h) (h 25485)

theorem derived52256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3641) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52256 (p 2027) (p 2528) (p 2598) (p 3549) (p 3591) (p 3641) (p 4107) (p 4669) (p 4733) (derived40810 p h) (h 25487)

theorem derived52257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2387) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3983) :=
  ElevenRUP.step52257 (p 2027) (p 2249) (p 2387) (p 2641) (p 2668) (p 3983) (derived40810 p h) (h 25488)

theorem derived52258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2249) ∨ (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2657) ∨ (¬ p 3027) ∨ (¬ p 3487) ∨ (¬ p 4202) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step52258 (p 2027) (p 2191) (p 2249) (p 2264) (p 2459) (p 2657) (p 3027) (p 3487) (p 4202) (p 5118) (p 5568) (derived40810 p h) (h 25489)

theorem derived52259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2727) ∨ (¬ p 3016) :=
  ElevenRUP.step52259 (p 2027) (p 2249) (p 2579) (p 2655) (p 2727) (p 3016) (derived40810 p h) (h 25490)

theorem derived52262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2928) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3452) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52262 (p 2027) (p 2696) (p 2928) (p 3005) (p 3256) (p 3452) (p 4278) (p 4669) (p 4733) (derived40810 p h) (h 25493)

theorem derived52263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2387) ∨ (¬ p 2667) ∨ (¬ p 3136) ∨ (¬ p 4195) :=
  ElevenRUP.step52263 (p 1979) (p 2027) (p 2187) (p 2387) (p 2667) (p 2765) (p 3136) (p 4195) (h 2139) (derived40810 p h) (derived40883 p h) (h 25494)

theorem derived52264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2641) ∨ (¬ p 2657) ∨ (¬ p 3125) ∨ (¬ p 3193) ∨ (¬ p 3487) ∨ (¬ p 4228) ∨ (¬ p 4393) ∨ (¬ p 4425) :=
  ElevenRUP.step52264 (p 1999) (p 2027) (p 2249) (p 2641) (p 2657) (p 2764) (p 3125) (p 3193) (p 3487) (p 4228) (p 4393) (p 4425) (h 2159) (derived40810 p h) (derived40882 p h) (h 25495)

theorem derived52265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2249) ∨ (¬ p 2459) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3172) ∨ (¬ p 4133) ∨ (¬ p 4261) ∨ (¬ p 4288) :=
  ElevenRUP.step52265 (p 2027) (p 2156) (p 2187) (p 2249) (p 2459) (p 2951) (p 2992) (p 3172) (p 4133) (p 4261) (p 4288) (derived40810 p h) (h 25496)

theorem derived52266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2996) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52266 (p 2027) (p 2247) (p 2363) (p 2774) (p 2819) (p 2996) (p 3947) (p 4669) (p 4733) (derived40810 p h) (h 25497)

theorem derived52269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (p 4438) :=
  ElevenRUP.step52269 (p 1975) (p 2299) (p 3498) (p 4438) (h 2135) (derived40899 p h) (h 25501)

theorem derived52270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2928) ∨ (¬ p 3146) ∨ (¬ p 3452) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52270 (p 2027) (p 2132) (p 2619) (p 2928) (p 3146) (p 3452) (p 4278) (p 4669) (p 4733) (derived40810 p h) (h 25502)

theorem derived52272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2249) ∨ (¬ p 2307) ∨ (¬ p 2641) ∨ (¬ p 2657) ∨ (¬ p 2928) ∨ (¬ p 3487) ∨ (¬ p 3567) ∨ (¬ p 4278) ∨ (¬ p 4666) :=
  ElevenRUP.step52272 (p 2027) (p 2177) (p 2249) (p 2307) (p 2641) (p 2657) (p 2928) (p 3487) (p 3567) (p 4278) (p 4666) (derived40810 p h) (h 25508)

theorem derived52273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2249) ∨ (¬ p 2641) ∨ (¬ p 2952) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 4282) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step52273 (p 2027) (p 2191) (p 2249) (p 2641) (p 2952) (p 3323) (p 3461) (p 4282) (p 5123) (p 5568) (derived40810 p h) (h 25509)

theorem derived52276 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 2963) ∨ (¬ p 3471) ∨ (¬ p 4037) ∨ (¬ p 4191) ∨ (¬ p 4253) ∨ (¬ p 4789) ∨ (¬ p 5660) :=
  ElevenRUP.step52276 (p 1998) (p 2027) (p 2764) (p 2881) (p 2963) (p 3471) (p 4037) (p 4191) (p 4253) (p 4789) (p 5660) (h 2158) (derived40810 p h) (derived40882 p h) (h 25513)

theorem derived52277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3568) ∨ (¬ p 3591) ∨ (¬ p 3876) ∨ (¬ p 4228) ∨ (¬ p 4435) ∨ (¬ p 4733) :=
  ElevenRUP.step52277 (p 1997) (p 2027) (p 2850) (p 2997) (p 3362) (p 3389) (p 3568) (p 3591) (p 3876) (p 4228) (p 4435) (p 4733) (h 2157) (derived40810 p h) (derived40890 p h) (h 25514)

theorem derived52279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 3073) ∨ (¬ p 3172) ∨ (¬ p 3859) ∨ (¬ p 4118) :=
  ElevenRUP.step52279 (p 2027) (p 2249) (p 3073) (p 3172) (p 3859) (p 4118) (derived40810 p h) (h 25516)

theorem derived52280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 3588) ∨ (¬ p 4777) :=
  ElevenRUP.step52280 (p 1976) (p 2027) (p 2633) (p 2737) (p 3365) (p 3553) (p 3588) (p 4777) (h 2136) (derived40810 p h) (derived40879 p h) (h 25517)

theorem derived52281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3641) ∨ (¬ p 3690) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52281 (p 2027) (p 2528) (p 2598) (p 3486) (p 3555) (p 3641) (p 3690) (p 4669) (p 4733) (derived40810 p h) (h 25518)

theorem derived52282 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2341) ∨ (¬ p 2657) ∨ (¬ p 3027) ∨ (¬ p 3193) ∨ (¬ p 3487) ∨ (¬ p 3941) ∨ (¬ p 4066) ∨ (¬ p 4425) ∨ (¬ p 5119) :=
  ElevenRUP.step52282 (p 2027) (p 2249) (p 2341) (p 2657) (p 3027) (p 3193) (p 3487) (p 3941) (p 4066) (p 4425) (p 5119) (derived40810 p h) (h 25519)

theorem derived52285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3690) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step52285 (p 2027) (p 2363) (p 2774) (p 2819) (p 3486) (p 3555) (p 3690) (p 4669) (p 4733) (derived40810 p h) (h 25523)

theorem derived52286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2963) ∨ (¬ p 3027) ∨ (¬ p 3097) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3686) ∨ (¬ p 3737) ∨ (¬ p 3922) ∨ (p 4325) ∨ (¬ p 4435) :=
  ElevenRUP.step52286 (p 1988) (p 2027) (p 2249) (p 2963) (p 2997) (p 3027) (p 3097) (p 3276) (p 3333) (p 3686) (p 3737) (p 3922) (p 4325) (p 4435) (h 2148) (derived40810 p h) (derived40890 p h) (h 25525)

theorem derived52288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2474) ∨ (¬ p 2657) ∨ (¬ p 3189) ∨ (¬ p 3193) ∨ (¬ p 3256) ∨ (¬ p 3363) ∨ (¬ p 3422) ∨ (¬ p 3487) ∨ (¬ p 3857) ∨ (¬ p 4022) ∨ (¬ p 4191) :=
  ElevenRUP.step52288 (p 2005) (p 2027) (p 2249) (p 2474) (p 2657) (p 2764) (p 3189) (p 3193) (p 3256) (p 3363) (p 3422) (p 3487) (p 3857) (p 4022) (p 4191) (h 2165) (derived40810 p h) (derived40882 p h) (h 25527)

theorem derived52289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2881) ∨ (¬ p 2951) ∨ (¬ p 2963) ∨ (¬ p 2992) ∨ (¬ p 3051) ∨ (¬ p 3549) ∨ (¬ p 3922) ∨ (¬ p 4107) ∨ (¬ p 4666) :=
  ElevenRUP.step52289 (p 2027) (p 2249) (p 2881) (p 2951) (p 2963) (p 2992) (p 3051) (p 3549) (p 3922) (p 4107) (p 4666) (derived40810 p h) (h 25528)

theorem derived52291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2284) ∨ (¬ p 2387) ∨ (¬ p 2954) ∨ (¬ p 4198) :=
  ElevenRUP.step52291 (p 2027) (p 2187) (p 2284) (p 2387) (p 2954) (p 4198) (derived40810 p h) (h 25530)

theorem derived52292 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3422) ∨ (¬ p 3874) ∨ (¬ p 3958) ∨ (¬ p 4432) :=
  ElevenRUP.step52292 (p 2027) (p 2187) (p 3422) (p 3874) (p 3958) (p 4432) (derived40810 p h) (h 25531)

theorem derived52293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2363) ∨ (¬ p 2563) ∨ (¬ p 3646) ∨ (¬ p 4441) :=
  ElevenRUP.step52293 (p 1982) (p 2027) (p 2202) (p 2220) (p 2363) (p 2563) (p 3646) (p 4441) (h 2142) (derived40810 p h) (derived40867 p h) (h 25532)

theorem derived52294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2811) ∨ (p 4790) :=
  ElevenRUP.step52294 (p 1984) (p 2247) (p 2688) (p 2811) (p 4790) (h 2144) (derived40880 p h) (h 25533)

theorem derived52297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2608) ∨ (¬ p 2641) ∨ (¬ p 2744) ∨ (¬ p 2963) :=
  ElevenRUP.step52297 (p 2027) (p 2245) (p 2608) (p 2641) (p 2744) (p 2963) (derived40810 p h) (h 25536)

theorem derived52298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3367) ∨ (¬ p 3555) ∨ (¬ p 4418) ∨ (¬ p 4881) :=
  ElevenRUP.step52298 (p 2027) (p 2608) (p 3367) (p 3555) (p 4418) (p 4881) (derived40810 p h) (h 25537)

theorem derived52300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3192) ∨ (¬ p 3276) ∨ (¬ p 4107) ∨ (¬ p 4381) ∨ (¬ p 4712) :=
  ElevenRUP.step52300 (p 2027) (p 3192) (p 3276) (p 4107) (p 4381) (p 4712) (derived40810 p h) (h 25539)

theorem derived52301 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3325) ∨ (¬ p 3570) ∨ (¬ p 4348) ∨ (¬ p 4556) :=
  ElevenRUP.step52301 (p 2027) (p 2363) (p 3325) (p 3570) (p 4348) (p 4556) (derived40810 p h) (h 25541)

theorem derived52302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 4811) :=
  ElevenRUP.step52302 (p 2010) (p 2545) (p 2922) (p 4811) (h 2170) (derived40876 p h) (h 25544)

theorem derived52304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 4135) ∨ (¬ p 4277) ∨ (¬ p 4278) ∨ (¬ p 4320) :=
  ElevenRUP.step52304 (p 2027) (p 3115) (p 4135) (p 4277) (p 4278) (p 4320) (derived40810 p h) (h 25546)

theorem derived52305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 2922) ∨ (¬ p 3365) ∨ (¬ p 4079) ∨ (¬ p 4277) ∨ (¬ p 4315) ∨ (¬ p 4320) ∨ (¬ p 4736) :=
  ElevenRUP.step52305 (p 2027) (p 2499) (p 2573) (p 2922) (p 3365) (p 4079) (p 4277) (p 4315) (p 4320) (p 4736) (derived40810 p h) (h 25547)

theorem derived52306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 3585) ∨ (¬ p 4737) :=
  ElevenRUP.step52306 (p 2027) (p 2573) (p 3362) (p 3584) (p 3585) (p 4737) (derived40810 p h) (h 25548)

theorem derived52310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2406) ∨ (¬ p 2589) ∨ (¬ p 2750) ∨ (¬ p 3541) ∨ (¬ p 4108) :=
  ElevenRUP.step52310 (p 2027) (p 2241) (p 2406) (p 2589) (p 2750) (p 3541) (p 4108) (derived40810 p h) (h 25554)

theorem derived52311 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3583) ∨ (¬ p 3589) :=
  ElevenRUP.step52311 (p 2027) (p 2132) (p 2247) (p 2744) (p 3583) (p 3589) (derived40810 p h) (h 25555)

theorem derived52313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 4026) ∨ (¬ p 4512) ∨ (¬ p 4875) :=
  ElevenRUP.step52313 (p 2027) (p 2860) (p 3125) (p 4026) (p 4512) (p 4875) (derived40810 p h) (h 25557)

theorem derived52314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3136) ∨ (¬ p 3572) ∨ (¬ p 3699) ∨ (¬ p 4555) :=
  ElevenRUP.step52314 (p 2027) (p 2284) (p 3136) (p 3572) (p 3699) (p 4555) (derived40810 p h) (h 25558)

theorem derived52318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2341) ∨ (¬ p 2744) ∨ (¬ p 3545) ∨ (¬ p 3548) ∨ (¬ p 4400) :=
  ElevenRUP.step52318 (p 2027) (p 2247) (p 2341) (p 2744) (p 3545) (p 3548) (p 4400) (derived40810 p h) (h 25564)

theorem derived52320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2779) ∨ (¬ p 3550) ∨ (¬ p 3553) ∨ (¬ p 3822) ∨ (¬ p 4333) ∨ (¬ p 4556) :=
  ElevenRUP.step52320 (p 2027) (p 2383) (p 2779) (p 3550) (p 3553) (p 3822) (p 4333) (p 4556) (derived40810 p h) (h 25566)

theorem derived52321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2383) ∨ (¬ p 3550) ∨ (¬ p 3553) ∨ (¬ p 4333) ∨ (¬ p 4556) :=
  ElevenRUP.step52321 (p 2027) (p 2313) (p 2383) (p 3550) (p 3553) (p 4333) (p 4556) (derived40810 p h) (h 25567)

theorem derived52322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3238) ∨ (¬ p 4079) ∨ (¬ p 4257) :=
  ElevenRUP.step52322 (p 2027) (p 2230) (p 2247) (p 2744) (p 3238) (p 4079) (p 4257) (derived40810 p h) (h 25568)

theorem derived52332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3545) ∨ (¬ p 3548) ∨ (¬ p 3555) ∨ (¬ p 4377) ∨ (¬ p 4400) :=
  ElevenRUP.step52332 (p 2027) (p 2341) (p 3545) (p 3548) (p 3555) (p 4377) (p 4400) (derived40810 p h) (h 25580)

theorem derived52334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2743) ∨ (¬ p 3256) ∨ (¬ p 3537) ∨ (¬ p 3589) ∨ (¬ p 4967) :=
  ElevenRUP.step52334 (p 1982) (p 2027) (p 2696) (p 2699) (p 2743) (p 3256) (p 3537) (p 3589) (p 4967) (h 2142) (derived40810 p h) (derived40881 p h) (h 25586)

theorem derived52337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 3549) ∨ (¬ p 4512) ∨ (¬ p 4525) :=
  ElevenRUP.step52337 (p 2027) (p 2156) (p 2274) (p 3549) (p 4512) (p 4525) (derived40810 p h) (h 25590)

theorem derived52342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2459) ∨ (¬ p 3324) ∨ (¬ p 4347) :=
  ElevenRUP.step52342 (p 1975) (p 2027) (p 2295) (p 2459) (p 2633) (p 3324) (p 4347) (h 2135) (derived40810 p h) (derived40879 p h) (h 25595)

theorem derived52349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 3324) :=
  ElevenRUP.step52349 (p 1975) (p 2027) (p 2233) (p 2295) (p 2352) (p 2573) (p 3324) (h 2135) (derived40810 p h) (derived40868 p h) (h 25604)

theorem derived52351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2741) ∨ (¬ p 3005) ∨ (¬ p 4360) ∨ (¬ p 4737) :=
  ElevenRUP.step52351 (p 2027) (p 2696) (p 2741) (p 3005) (p 4360) (p 4737) (derived40810 p h) (h 25607)

theorem derived52354 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2220) ∨ (¬ p 2247) ∨ (¬ p 4172) ∨ (¬ p 4959) :=
  ElevenRUP.step52354 (p 2027) (p 2191) (p 2220) (p 2247) (p 4172) (p 4959) (derived40810 p h) (h 25612)

theorem derived52355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 3365) ∨ (¬ p 3952) ∨ (¬ p 4385) ∨ (¬ p 4392) :=
  ElevenRUP.step52355 (p 1976) (p 2027) (p 2765) (p 3115) (p 3365) (p 3952) (p 4385) (p 4392) (h 2136) (derived40810 p h) (derived40883 p h) (h 25613)

theorem derived52356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2307) ∨ (¬ p 2744) ∨ (¬ p 3549) ∨ (¬ p 4512) ∨ (¬ p 4874) ∨ (¬ p 5020) :=
  ElevenRUP.step52356 (p 2027) (p 2247) (p 2307) (p 2744) (p 3549) (p 4512) (p 4874) (p 5020) (derived40810 p h) (h 25614)

theorem derived52358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2499) ∨ (¬ p 2901) ∨ (¬ p 2962) ∨ (¬ p 3413) ∨ (¬ p 3556) ∨ (¬ p 4811) :=
  ElevenRUP.step52358 (p 2027) (p 2386) (p 2499) (p 2901) (p 2962) (p 3413) (p 3556) (p 4811) (derived40810 p h) (h 25617)

theorem derived52360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3568) ∨ (¬ p 3570) ∨ (¬ p 4195) ∨ (¬ p 4556) ∨ (¬ p 4736) :=
  ElevenRUP.step52360 (p 2027) (p 3365) (p 3399) (p 3527) (p 3568) (p 3570) (p 4195) (p 4556) (p 4736) (derived40810 p h) (h 25619)

theorem derived52368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2299) ∨ (¬ p 2881) ∨ (¬ p 3872) :=
  ElevenRUP.step52368 (p 1975) (p 2027) (p 2192) (p 2210) (p 2299) (p 2699) (p 2881) (p 3872) (h 2135) (derived40810 p h) (derived40881 p h) (h 25627)

theorem derived52369 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2952) ∨ (¬ p 2992) :=
  ElevenRUP.step52369 (p 2027) (p 2245) (p 2608) (p 2744) (p 2952) (p 2992) (derived40810 p h) (h 25628)

theorem derived52370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2589) ∨ (¬ p 4108) :=
  ElevenRUP.step52370 (p 1984) (p 2027) (p 2406) (p 2509) (p 2534) (p 2589) (p 2766) (p 4108) (h 2144) (derived40810 p h) (derived40884 p h) (h 25629)

theorem derived52371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2962) ∨ (¬ p 3097) ∨ (¬ p 4173) ∨ (¬ p 4525) :=
  ElevenRUP.step52371 (p 2027) (p 2307) (p 2962) (p 3097) (p 4173) (p 4525) (derived40810 p h) (h 25630)

theorem derived52374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3055) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3684) ∨ (¬ p 3880) ∨ (¬ p 4736) ∨ (¬ p 4905) :=
  ElevenRUP.step52374 (p 2027) (p 2177) (p 3055) (p 3093) (p 3309) (p 3684) (p 3880) (p 4736) (p 4905) (derived40810 p h) (h 25634)

theorem derived52375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2274) ∨ (¬ p 3063) ∨ (¬ p 3989) ∨ (¬ p 4338) :=
  ElevenRUP.step52375 (p 1975) (p 2027) (p 2210) (p 2274) (p 2699) (p 3063) (p 3989) (p 4338) (h 2135) (derived40810 p h) (derived40881 p h) (h 25635)

theorem derived52376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2996) ∨ (¬ p 3644) ∨ (¬ p 3947) :=
  ElevenRUP.step52376 (p 1977) (p 2027) (p 2417) (p 2633) (p 2996) (p 3644) (p 3947) (h 2137) (derived40810 p h) (derived40879 p h) (h 25636)

theorem derived52379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3346) ∨ (¬ p 3389) ∨ (¬ p 4425) :=
  ElevenRUP.step52379 (p 1995) (p 2027) (p 2764) (p 2928) (p 3346) (p 3389) (p 4425) (h 2155) (derived40810 p h) (derived40882 p h) (h 25639)

theorem derived52380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2533) ∨ (¬ p 3680) ∨ (¬ p 4444) :=
  ElevenRUP.step52380 (p 1982) (p 2027) (p 2166) (p 2210) (p 2533) (p 2699) (p 3680) (p 4444) (h 2142) (derived40810 p h) (derived40881 p h) (h 25641)

theorem derived52381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2881) ∨ (¬ p 2928) ∨ (¬ p 3644) :=
  ElevenRUP.step52381 (p 1997) (p 2027) (p 2406) (p 2881) (p 2928) (p 2938) (p 3644) (h 2157) (derived40810 p h) (derived40888 p h) (h 25643)

theorem derived52382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3212) ∨ (¬ p 3551) ∨ (¬ p 3872) ∨ (¬ p 4984) ∨ (¬ p 5046) :=
  ElevenRUP.step52382 (p 2027) (p 2881) (p 3212) (p 3551) (p 3872) (p 4984) (p 5046) (derived40810 p h) (h 25644)

theorem derived52383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3553) ∨ (¬ p 4112) ∨ (¬ p 4814) :=
  ElevenRUP.step52383 (p 2027) (p 2911) (p 2922) (p 3553) (p 4112) (p 4814) (derived40810 p h) (h 25645)

theorem derived52389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (¬ p 3564) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4330) ∨ (¬ p 4786) :=
  ElevenRUP.step52389 (p 2027) (p 2138) (p 2651) (p 3016) (p 3564) (p 3692) (p 3694) (p 4330) (p 4786) (derived40810 p h) (h 25654)

theorem derived52392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2255) ∨ (¬ p 2553) ∨ (¬ p 2651) ∨ (¬ p 2881) ∨ (¬ p 2996) ∨ (¬ p 3016) ∨ (¬ p 3551) ∨ (¬ p 4155) ∨ (¬ p 4559) :=
  ElevenRUP.step52392 (p 2027) (p 2255) (p 2553) (p 2651) (p 2881) (p 2996) (p 3016) (p 3551) (p 4155) (p 4559) (derived40810 p h) (h 25657)

theorem derived52398 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2255) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 2667) ∨ (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 3946) ∨ (¬ p 4116) ∨ (¬ p 4154) :=
  ElevenRUP.step52398 (p 1982) (p 2027) (p 2255) (p 2518) (p 2528) (p 2651) (p 2667) (p 2997) (p 3097) (p 3125) (p 3946) (p 4116) (p 4154) (h 2142) (derived40810 p h) (derived40890 p h) (h 25665)

theorem derived52399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2299) ∨ (¬ p 2534) ∨ (¬ p 2651) ∨ (¬ p 3097) ∨ (¬ p 3256) ∨ (¬ p 3646) ∨ (¬ p 4121) ∨ (¬ p 4420) ∨ (¬ p 4524) :=
  ElevenRUP.step52399 (p 2027) (p 2253) (p 2299) (p 2534) (p 2651) (p 3097) (p 3256) (p 3646) (p 4121) (p 4420) (p 4524) (derived40810 p h) (h 25666)

theorem derived52403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2608) ∨ (¬ p 2619) ∨ (¬ p 2839) ∨ (¬ p 4902) ∨ (¬ p 5193) :=
  ElevenRUP.step52403 (p 2027) (p 2299) (p 2579) (p 2588) (p 2608) (p 2619) (p 2839) (p 4902) (p 5193) (derived40810 p h) (h 25670)

theorem derived52406 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2963) ∨ (¬ p 2996) ∨ (¬ p 3553) :=
  ElevenRUP.step52406 (p 1991) (p 2027) (p 2633) (p 2641) (p 2963) (p 2996) (p 3553) (h 2151) (derived40810 p h) (derived40879 p h) (h 25673)

theorem derived52409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2264) ∨ (¬ p 2744) ∨ (¬ p 3037) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3684) ∨ (¬ p 3880) ∨ (¬ p 4905) :=
  ElevenRUP.step52409 (p 2027) (p 2247) (p 2264) (p 2744) (p 3037) (p 3055) (p 3366) (p 3399) (p 3684) (p 3880) (p 4905) (derived40810 p h) (h 25679)

theorem derived52410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3324) ∨ (¬ p 4110) ∨ (¬ p 4441) ∨ (¬ p 4564) :=
  ElevenRUP.step52410 (p 2027) (p 2373) (p 3324) (p 4110) (p 4441) (p 4564) (derived40810 p h) (h 25680)

theorem derived52411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2534) ∨ (¬ p 2744) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3874) ∨ (¬ p 3950) :=
  ElevenRUP.step52411 (p 2027) (p 2247) (p 2534) (p 2744) (p 3055) (p 3366) (p 3399) (p 3631) (p 3874) (p 3950) (derived40810 p h) (h 25681)

theorem derived52413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 3367) ∨ (¬ p 3425) ∨ (¬ p 3688) :=
  ElevenRUP.step52413 (p 1986) (p 2027) (p 2774) (p 3367) (p 3425) (p 3437) (p 3688) (h 2146) (derived40810 p h) (derived40896 p h) (h 25683)

theorem derived52414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3172) ∨ (¬ p 4118) :=
  ElevenRUP.step52414 (p 1994) (p 2027) (p 2510) (p 2528) (p 2651) (p 3008) (p 3172) (p 4118) (h 2154) (derived40810 p h) (derived40891 p h) (h 25684)

theorem derived52415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3266) ∨ (¬ p 3449) ∨ (¬ p 3954) :=
  ElevenRUP.step52415 (p 1988) (p 2027) (p 2114) (p 3073) (p 3266) (p 3449) (p 3954) (h 2148) (derived40810 p h) (derived40864 p h) (h 25685)

theorem derived52416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2881) ∨ (¬ p 3872) ∨ (¬ p 4486) :=
  ElevenRUP.step52416 (p 2027) (p 2299) (p 2313) (p 2881) (p 3872) (p 4486) (derived40810 p h) (h 25686)

theorem derived52417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2743) ∨ (¬ p 2839) ∨ (¬ p 3051) ∨ (¬ p 4320) :=
  ElevenRUP.step52417 (p 1979) (p 2027) (p 2137) (p 2622) (p 2743) (p 2839) (p 3051) (p 4320) (h 2139) (derived40810 p h) (derived40878 p h) (h 25688)

theorem derived52418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 3579) ∨ (¬ p 4111) ∨ (¬ p 4646) :=
  ElevenRUP.step52418 (p 2027) (p 2246) (p 2440) (p 2807) (p 3579) (p 4111) (p 4646) (derived40810 p h) (h 25690)

theorem derived52420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2891) ∨ (¬ p 4173) ∨ (¬ p 4244) :=
  ElevenRUP.step52420 (p 1976) (p 2027) (p 2138) (p 2765) (p 2891) (p 4173) (p 4244) (h 2136) (derived40810 p h) (derived40883 p h) (h 25693)

theorem derived52421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2651) ∨ (¬ p 2963) ∨ (¬ p 3324) :=
  ElevenRUP.step52421 (p 1994) (p 2027) (p 2352) (p 2651) (p 2963) (p 3008) (p 3324) (h 2154) (derived40810 p h) (derived40891 p h) (h 25695)

theorem derived52422 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2641) ∨ (¬ p 3365) ∨ (¬ p 4195) :=
  ElevenRUP.step52422 (p 1986) (p 2027) (p 2598) (p 2641) (p 2688) (p 3365) (p 4195) (h 2146) (derived40810 p h) (derived40880 p h) (h 25696)

theorem derived52428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2761) ∨ (¬ p 3654) ∨ (¬ p 4623) :=
  ElevenRUP.step52428 (p 1988) (p 2027) (p 2313) (p 2553) (p 2761) (p 3008) (p 3654) (p 4623) (h 2148) (derived40810 p h) (derived40891 p h) (h 25702)

theorem derived52432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2952) ∨ (¬ p 2992) ∨ (¬ p 2996) :=
  ElevenRUP.step52432 (p 1994) (p 2027) (p 2355) (p 2651) (p 2952) (p 2992) (p 2996) (h 2154) (derived40810 p h) (derived40872 p h) (h 25706)

theorem derived52434 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3055) ∨ (¬ p 3541) ∨ (¬ p 3684) ∨ (¬ p 4734) :=
  ElevenRUP.step52434 (p 2027) (p 2406) (p 3055) (p 3541) (p 3684) (p 4734) (derived40810 p h) (h 25709)

theorem derived52438 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2498) ∨ (¬ p 2588) ∨ (¬ p 3319) ∨ (¬ p 3690) ∨ (¬ p 4556) ∨ (¬ p 5299) ∨ (¬ p 5379) :=
  ElevenRUP.step52438 (p 2027) (p 2498) (p 2588) (p 3319) (p 3690) (p 4556) (p 5299) (p 5379) (derived40810 p h) (h 25713)

theorem derived52439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3319) ∨ (¬ p 3923) ∨ (¬ p 4444) ∨ (¬ p 4623) :=
  ElevenRUP.step52439 (p 1982) (p 2027) (p 2169) (p 2761) (p 3319) (p 3923) (p 4444) (p 4623) (h 2142) (derived40810 p h) (derived40866 p h) (h 25715)

theorem derived52442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2751) ∨ (¬ p 3171) ∨ (¬ p 3189) ∨ (¬ p 4340) ∨ (¬ p 4364) :=
  ElevenRUP.step52442 (p 2027) (p 2088) (p 2751) (p 3171) (p 3189) (p 4340) (p 4364) (derived40810 p h) (h 25719)

theorem derived52446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2737) ∨ (¬ p 3016) ∨ (¬ p 3365) ∨ (¬ p 3683) :=
  ElevenRUP.step52446 (p 2005) (p 2027) (p 2114) (p 2598) (p 2737) (p 3016) (p 3365) (p 3683) (h 2165) (derived40810 p h) (derived40864 p h) (h 25723)

theorem derived52456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3367) ∨ (¬ p 3471) ∨ (¬ p 3588) ∨ (¬ p 4752) :=
  ElevenRUP.step52456 (p 2027) (p 3365) (p 3367) (p 3471) (p 3588) (p 4752) (derived40810 p h) (h 25735)

theorem derived52460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 3564) ∨ (¬ p 3742) ∨ (¬ p 3921) ∨ (¬ p 4624) :=
  ElevenRUP.step52460 (p 2027) (p 3016) (p 3564) (p 3742) (p 3921) (p 4624) (derived40810 p h) (h 25742)

theorem derived52466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2298) ∨ (¬ p 2331) ∨ (¬ p 2553) ∨ (¬ p 3414) ∨ (¬ p 4973) :=
  ElevenRUP.step52466 (p 2027) (p 2298) (p 2331) (p 2553) (p 3414) (p 4973) (derived40810 p h) (h 25754)

theorem derived52468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2499) ∨ (¬ p 2761) ∨ (¬ p 3452) ∨ (¬ p 3945) ∨ (¬ p 4137) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 5207) :=
  ElevenRUP.step52468 (p 2027) (p 2341) (p 2499) (p 2761) (p 3452) (p 3945) (p 4137) (p 4444) (p 4604) (p 5207) (derived40810 p h) (h 25756)

theorem derived52469 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3051) ∨ (¬ p 3486) ∨ (¬ p 4172) ∨ (¬ p 4202) ∨ (¬ p 4257) :=
  ElevenRUP.step52469 (p 2027) (p 2247) (p 2744) (p 3051) (p 3486) (p 4172) (p 4202) (p 4257) (derived40810 p h) (h 25757)

theorem derived52473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3038) ∨ (¬ p 3527) ∨ (¬ p 3553) ∨ (¬ p 4111) ∨ (¬ p 4652) :=
  ElevenRUP.step52473 (p 2027) (p 3038) (p 3527) (p 3553) (p 4111) (p 4652) (derived40810 p h) (h 25764)

theorem derived52477 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 3193) ∨ (¬ p 4149) ∨ (¬ p 4440) ∨ (¬ p 5122) :=
  ElevenRUP.step52477 (p 2027) (p 2518) (p 3193) (p 4149) (p 4440) (p 5122) (derived40810 p h) (h 25770)

theorem derived52480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2743) ∨ (¬ p 2891) ∨ (¬ p 2963) ∨ (¬ p 3246) ∨ (¬ p 3361) ∨ (¬ p 4037) ∨ (¬ p 4418) ∨ (¬ p 4625) ∨ (¬ p 4737) :=
  ElevenRUP.step52480 (p 2027) (p 2132) (p 2743) (p 2891) (p 2963) (p 3246) (p 3361) (p 4037) (p 4418) (p 4625) (p 4737) (derived40810 p h) (h 25774)

theorem derived52483 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3343) ∨ (¬ p 3742) ∨ (¬ p 3921) ∨ (¬ p 4381) :=
  ElevenRUP.step52483 (p 1983) (p 2027) (p 2997) (p 3276) (p 3343) (p 3742) (p 3921) (p 4381) (h 2143) (derived40810 p h) (derived40890 p h) (h 25778)

theorem derived52484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2230) ∨ (¬ p 2579) ∨ (¬ p 3581) ∨ (¬ p 3644) :=
  ElevenRUP.step52484 (p 1997) (p 2027) (p 2177) (p 2230) (p 2579) (p 2997) (p 3581) (p 3644) (h 2157) (derived40810 p h) (derived40890 p h) (h 25783)

theorem derived52487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3680) ∨ (¬ p 4037) ∨ (¬ p 4191) :=
  ElevenRUP.step52487 (p 1981) (p 2027) (p 2668) (p 3043) (p 3680) (p 4037) (p 4191) (h 2141) (derived40810 p h) (derived40893 p h) (h 25788)

theorem derived52493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2459) ∨ (¬ p 2707) ∨ (¬ p 3577) ∨ (¬ p 3583) :=
  ElevenRUP.step52493 (p 1982) (p 2027) (p 2341) (p 2459) (p 2707) (p 3474) (p 3577) (p 3583) (h 2142) (derived40810 p h) (derived40898 p h) (h 25795)

theorem derived52498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2951) ∨ (¬ p 2963) ∨ (¬ p 2992) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3266) ∨ (¬ p 3922) ∨ (¬ p 3950) ∨ (¬ p 4321) ∨ (¬ p 4430) :=
  ElevenRUP.step52498 (p 2027) (p 2249) (p 2951) (p 2963) (p 2992) (p 3051) (p 3246) (p 3266) (p 3922) (p 3950) (p 4321) (p 4430) (derived40810 p h) (h 25801)

theorem derived52499 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2952) ∨ (¬ p 2992) ∨ (¬ p 3379) ∨ (¬ p 4813) :=
  ElevenRUP.step52499 (p 2027) (p 2245) (p 2952) (p 2992) (p 3379) (p 4813) (derived40810 p h) (h 25802)

theorem derived52500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2312) ∨ (¬ p 2553) ∨ (¬ p 3486) ∨ (¬ p 4283) ∨ (¬ p 4718) :=
  ElevenRUP.step52500 (p 2027) (p 2192) (p 2312) (p 2553) (p 3486) (p 4283) (p 4718) (derived40810 p h) (h 25803)

theorem derived52502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2881) ∨ (¬ p 3644) ∨ (¬ p 3742) :=
  ElevenRUP.step52502 (p 1991) (p 2027) (p 2657) (p 2881) (p 2938) (p 3644) (p 3742) (h 2151) (derived40810 p h) (derived40888 p h) (h 25806)

theorem derived52505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 3956) ∨ (¬ p 4389) ∨ (¬ p 4444) :=
  ElevenRUP.step52505 (p 1982) (p 2027) (p 2169) (p 3323) (p 3461) (p 3956) (p 4389) (p 4444) (h 2142) (derived40810 p h) (derived40866 p h) (h 25814)

theorem derived52510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2245) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 4959) :=
  ElevenRUP.step52510 (p 2027) (p 2210) (p 2245) (p 2657) (p 2727) (p 4959) (derived40810 p h) (h 25824)

theorem derived52511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2563) ∨ (¬ p 2651) ∨ (¬ p 3952) :=
  ElevenRUP.step52511 (p 1979) (p 2027) (p 2323) (p 2542) (p 2563) (p 2651) (p 3952) (h 2139) (derived40810 p h) (derived40870 p h) (h 25825)

theorem derived52512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2744) ∨ (¬ p 2780) ∨ (¬ p 2946) ∨ (¬ p 3156) ∨ (¬ p 3366) ∨ (¬ p 3917) ∨ (¬ p 3969) ∨ (¬ p 4191) ∨ (¬ p 5119) :=
  ElevenRUP.step52512 (p 2027) (p 2246) (p 2744) (p 2780) (p 2946) (p 3156) (p 3366) (p 3917) (p 3969) (p 4191) (p 5119) (derived40810 p h) (h 25827)

theorem derived52514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 3585) ∨ (¬ p 3695) ∨ (¬ p 3874) ∨ (¬ p 4608) :=
  ElevenRUP.step52514 (p 2027) (p 2839) (p 3585) (p 3695) (p 3874) (p 4608) (derived40810 p h) (h 25829)

theorem derived52517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2608) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2744) :=
  ElevenRUP.step52517 (p 2027) (p 2245) (p 2608) (p 2657) (p 2727) (p 2744) (derived40810 p h) (h 25834)

theorem derived52518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3051) ∨ (¬ p 3414) ∨ (¬ p 3699) ∨ (¬ p 4399) :=
  ElevenRUP.step52518 (p 2027) (p 2249) (p 2656) (p 2727) (p 3051) (p 3414) (p 3699) (p 4399) (derived40810 p h) (h 25835)

theorem derived52521 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 3516) ∨ (¬ p 4278) ∨ (¬ p 4922) ∨ (¬ p 5201) :=
  ElevenRUP.step52521 (p 2027) (p 2476) (p 3516) (p 4278) (p 4922) (p 5201) (derived40810 p h) (h 25838)

theorem derived52522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 2534) ∨ (¬ p 3573) ∨ (¬ p 3958) :=
  ElevenRUP.step52522 (p 2027) (p 2187) (p 2363) (p 2534) (p 3573) (p 3958) (derived40810 p h) (h 25839)

theorem derived52525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3051) ∨ (¬ p 3873) ∨ (¬ p 4244) ∨ (¬ p 4521) :=
  ElevenRUP.step52525 (p 2027) (p 2138) (p 3051) (p 3873) (p 4244) (p 4521) (derived40810 p h) (h 25842)

theorem derived52528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2245) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2749) ∨ (¬ p 4877) :=
  ElevenRUP.step52528 (p 2027) (p 2210) (p 2245) (p 2657) (p 2727) (p 2749) (p 4877) (derived40810 p h) (h 25845)

theorem derived52532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3027) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3644) ∨ (¬ p 4276) :=
  ElevenRUP.step52532 (p 2027) (p 2264) (p 2608) (p 2744) (p 3027) (p 3549) (p 3591) (p 3644) (p 4276) (derived40810 p h) (h 25849)

theorem derived52536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3051) ∨ (¬ p 3486) ∨ (¬ p 4172) ∨ (¬ p 4874) :=
  ElevenRUP.step52536 (p 2027) (p 2247) (p 2744) (p 3051) (p 3486) (p 4172) (p 4874) (derived40810 p h) (h 25853)

theorem derived52541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2387) ∨ (¬ p 2778) ∨ (¬ p 3063) ∨ (¬ p 3097) ∨ (¬ p 3957) :=
  ElevenRUP.step52541 (p 2006) (p 2027) (p 2132) (p 2387) (p 2778) (p 2997) (p 3063) (p 3097) (p 3957) (h 2166) (derived40810 p h) (derived40890 p h) (h 25858)

theorem derived52542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2839) ∨ (¬ p 3097) ∨ (¬ p 3688) ∨ (¬ p 4428) :=
  ElevenRUP.step52542 (p 1976) (p 2027) (p 2138) (p 2839) (p 2997) (p 3097) (p 3688) (p 4428) (h 2136) (derived40810 p h) (derived40890 p h) (h 25859)

theorem derived52545 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4181) ∨ (¬ p 4347) ∨ (¬ p 5122) :=
  ElevenRUP.step52545 (p 2027) (p 2136) (p 2247) (p 2744) (p 3366) (p 3449) (p 3646) (p 3989) (p 4181) (p 4347) (p 5122) (derived40810 p h) (h 25862)

theorem derived52547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3449) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4181) ∨ (¬ p 4347) ∨ (¬ p 4959) ∨ (¬ p 5122) :=
  ElevenRUP.step52547 (p 2027) (p 2247) (p 3449) (p 3645) (p 3646) (p 3989) (p 4181) (p 4347) (p 4959) (p 5122) (derived40810 p h) (h 25864)

theorem derived52548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2440) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4281) :=
  ElevenRUP.step52548 (p 1994) (p 2027) (p 2230) (p 2440) (p 2688) (p 2922) (p 3540) (p 4281) (h 2154) (derived40810 p h) (derived40880 p h) (h 25867)

theorem derived52549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2311) ∨ (¬ p 2707) ∨ (¬ p 2778) ∨ (¬ p 3434) ∨ (¬ p 3821) ∨ (¬ p 4734) :=
  ElevenRUP.step52549 (p 2027) (p 2311) (p 2707) (p 2778) (p 3434) (p 3821) (p 4734) (derived40810 p h) (h 25868)

theorem derived52550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2829) ∨ (¬ p 3483) ∨ (¬ p 4137) :=
  ElevenRUP.step52550 (p 2005) (p 2027) (p 2622) (p 2743) (p 2829) (p 3483) (p 4137) (h 2165) (derived40810 p h) (derived40878 p h) (h 25869)

theorem derived52551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3688) ∨ (¬ p 4358) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step52551 (p 2027) (p 2247) (p 2744) (p 3073) (p 3449) (p 3688) (p 4358) (p 5118) (p 5580) (derived40810 p h) (h 25870)

theorem derived52552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3998) ∨ (¬ p 4436) ∨ (¬ p 5242) ∨ (¬ p 5693) :=
  ElevenRUP.step52552 (p 2027) (p 2247) (p 2744) (p 3998) (p 4436) (p 5242) (p 5693) (derived40810 p h) (h 25871)

theorem derived52553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3449) ∨ (¬ p 3688) ∨ (¬ p 3917) ∨ (¬ p 4181) ∨ (¬ p 4191) ∨ (¬ p 5119) :=
  ElevenRUP.step52553 (p 2027) (p 2247) (p 2744) (p 3449) (p 3688) (p 3917) (p 4181) (p 4191) (p 5119) (derived40810 p h) (h 25872)

theorem derived52554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3038) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 5206) :=
  ElevenRUP.step52554 (p 2027) (p 2608) (p 2744) (p 3038) (p 3631) (p 3821) (p 5206) (derived40810 p h) (h 25873)

theorem derived52555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3449) ∨ (¬ p 3688) ∨ (¬ p 4009) ∨ (¬ p 4288) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 5122) :=
  ElevenRUP.step52555 (p 2027) (p 2247) (p 2744) (p 3449) (p 3688) (p 4009) (p 4288) (p 4347) (p 4358) (p 5122) (derived40810 p h) (h 25874)

theorem derived52556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3688) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4358) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step52556 (p 2027) (p 2247) (p 2744) (p 3688) (p 3707) (p 3830) (p 4358) (p 5123) (p 5580) (derived40810 p h) (h 25875)

theorem derived52557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2247) ∨ (¬ p 2387) ∨ (¬ p 2744) ∨ (¬ p 2819) ∨ (¬ p 2891) ∨ (¬ p 3204) ∨ (¬ p 3822) ∨ (¬ p 3953) ∨ (¬ p 4556) :=
  ElevenRUP.step52557 (p 2027) (p 2210) (p 2247) (p 2387) (p 2744) (p 2819) (p 2891) (p 3204) (p 3822) (p 3953) (p 4556) (derived40810 p h) (h 25876)

theorem derived52559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3038) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4959) ∨ (¬ p 5206) :=
  ElevenRUP.step52559 (p 2027) (p 2210) (p 3038) (p 3631) (p 3821) (p 4959) (p 5206) (derived40810 p h) (h 25878)

theorem derived52561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2470) ∨ (¬ p 2509) ∨ (¬ p 2744) ∨ (¬ p 4079) ∨ (¬ p 4257) :=
  ElevenRUP.step52561 (p 2027) (p 2247) (p 2470) (p 2509) (p 2744) (p 4079) (p 4257) (derived40810 p h) (h 25880)

theorem derived52563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2934) ∨ (¬ p 3238) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4279) ∨ (¬ p 4646) :=
  ElevenRUP.step52563 (p 2027) (p 2934) (p 3238) (p 3631) (p 3821) (p 4279) (p 4646) (derived40810 p h) (h 25882)

theorem derived52564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2383) ∨ (¬ p 3550) ∨ (¬ p 3570) ∨ (¬ p 4556) :=
  ElevenRUP.step52564 (p 2027) (p 2313) (p 2383) (p 3550) (p 3570) (p 4556) (derived40810 p h) (h 25884)

theorem derived52565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3570) ∨ (¬ p 3646) ∨ (¬ p 4558) ∨ (¬ p 4988) :=
  ElevenRUP.step52565 (p 2027) (p 2341) (p 3570) (p 3646) (p 4558) (p 4988) (derived40810 p h) (h 25885)

theorem derived52566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3570) ∨ (¬ p 4032) ∨ (¬ p 4988) ∨ (¬ p 5102) :=
  ElevenRUP.step52566 (p 2027) (p 2341) (p 3570) (p 4032) (p 4988) (p 5102) (derived40810 p h) (h 25886)

theorem derived52568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2493) ∨ (¬ p 2928) ∨ (¬ p 3574) ∨ (¬ p 3921) :=
  ElevenRUP.step52568 (p 1994) (p 2027) (p 2299) (p 2493) (p 2633) (p 2928) (p 3574) (p 3921) (h 2154) (derived40810 p h) (derived40879 p h) (h 25888)

theorem derived52571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3954) :=
  ElevenRUP.step52571 (p 1998) (p 2027) (p 2114) (p 2177) (p 3093) (p 3309) (p 3954) (h 2158) (derived40810 p h) (derived40864 p h) (h 25894)

theorem derived52572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4236) :=
  ElevenRUP.step52572 (p 1976) (p 2027) (p 2633) (p 2952) (p 3136) (p 3553) (p 3572) (p 4236) (h 2136) (derived40810 p h) (derived40879 p h) (h 25896)

theorem derived52574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4973) :=
  ElevenRUP.step52574 (p 2027) (p 2352) (p 2363) (p 4118) (p 4196) (p 4973) (derived40810 p h) (h 25898)

theorem derived52575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 2668) ∨ (¬ p 3767) ∨ (¬ p 4405) ∨ (¬ p 5274) ∨ (¬ p 5284) ∨ (¬ p 5300) :=
  ElevenRUP.step52575 (p 2027) (p 2312) (p 2668) (p 3767) (p 4405) (p 5274) (p 5284) (p 5300) (derived40810 p h) (h 25900)

theorem derived52576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 3051) ∨ (¬ p 3367) ∨ (¬ p 3486) ∨ (¬ p 4874) ∨ (¬ p 4881) :=
  ElevenRUP.step52576 (p 2027) (p 2137) (p 3051) (p 3367) (p 3486) (p 4874) (p 4881) (derived40810 p h) (h 25901)

theorem derived52577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 5214) :=
  ElevenRUP.step52577 (p 1995) (p 2114) (p 3367) (p 5214) (h 2155) (derived40864 p h) (h 25902)

theorem derived52580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 2928) ∨ (¬ p 3201) ∨ (¬ p 3475) ∨ (¬ p 4257) ∨ (¬ p 5052) :=
  ElevenRUP.step52580 (p 2027) (p 2839) (p 2928) (p 3201) (p 3475) (p 4257) (p 5052) (derived40810 p h) (h 25906)

theorem derived52581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2598) ∨ (¬ p 2780) ∨ (¬ p 3590) ∨ (¬ p 4342) ∨ (¬ p 4715) :=
  ElevenRUP.step52581 (p 2027) (p 2406) (p 2598) (p 2780) (p 3590) (p 4342) (p 4715) (derived40810 p h) (h 25907)

theorem derived52582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 3156) ∨ (¬ p 4042) ∨ (¬ p 4320) ∨ (¬ p 4559) :=
  ElevenRUP.step52582 (p 2027) (p 2299) (p 3156) (p 4042) (p 4320) (p 4559) (derived40810 p h) (h 25910)

theorem derived52583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2958) ∨ (¬ p 2963) ∨ (¬ p 3497) ∨ (¬ p 4700) ∨ (¬ p 4972) :=
  ElevenRUP.step52583 (p 2027) (p 2220) (p 2958) (p 2963) (p 3497) (p 4700) (p 4972) (derived40810 p h) (h 25911)

theorem derived52588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2579) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3905) ∨ (¬ p 3950) ∨ (¬ p 3956) ∨ (¬ p 4347) :=
  ElevenRUP.step52588 (p 2027) (p 2247) (p 2579) (p 2744) (p 3366) (p 3399) (p 3631) (p 3905) (p 3950) (p 3956) (p 4347) (derived40810 p h) (h 25917)

theorem derived52589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2668) ∨ (¬ p 3452) ∨ (¬ p 3979) ∨ (¬ p 5122) :=
  ElevenRUP.step52589 (p 2027) (p 2248) (p 2331) (p 2509) (p 2534) (p 2668) (p 3452) (p 3979) (p 5122) (derived40810 p h) (h 25918)

theorem derived52591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3222) ∨ (¬ p 3366) ∨ (¬ p 3379) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4332) :=
  ElevenRUP.step52591 (p 2027) (p 2138) (p 2247) (p 2744) (p 3222) (p 3366) (p 3379) (p 3692) (p 3694) (p 4332) (derived40810 p h) (h 25920)

theorem derived52593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2743) ∨ (¬ p 2819) ∨ (¬ p 2829) :=
  ElevenRUP.step52593 (p 1982) (p 2027) (p 2363) (p 2622) (p 2743) (p 2819) (p 2829) (h 2142) (derived40810 p h) (derived40878 p h) (h 25924)

theorem derived52594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 2737) ∨ (¬ p 2797) :=
  ElevenRUP.step52594 (p 1982) (p 2027) (p 2114) (p 2363) (p 2668) (p 2737) (p 2797) (h 2142) (derived40810 p h) (derived40864 p h) (h 25925)

theorem derived52598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3644) ∨ (¬ p 3979) ∨ (¬ p 4347) ∨ (¬ p 5558) :=
  ElevenRUP.step52598 (p 2010) (p 2027) (p 2766) (p 3644) (p 3979) (p 4347) (p 5558) (h 2170) (derived40810 p h) (derived40884 p h) (h 25929)

theorem derived52604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2274) ∨ (¬ p 2476) ∨ (¬ p 3641) ∨ (¬ p 3876) ∨ (¬ p 3905) ∨ (¬ p 4712) ∨ (¬ p 4736) :=
  ElevenRUP.step52604 (p 2027) (p 2192) (p 2210) (p 2274) (p 2476) (p 3641) (p 3876) (p 3905) (p 4712) (p 4736) (derived40810 p h) (h 25937)

theorem derived52606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (p 4976) :=
  ElevenRUP.step52606 (p 1995) (p 2287) (p 2499) (p 4976) (h 2155) (derived40869 p h) (h 25939)

theorem derived52608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2192) ∨ (¬ p 3365) ∨ (¬ p 3952) ∨ (¬ p 4418) :=
  ElevenRUP.step52608 (p 1979) (p 2027) (p 2132) (p 2192) (p 2622) (p 3365) (p 3952) (p 4418) (h 2139) (derived40810 p h) (derived40878 p h) (h 25942)

theorem derived52609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2437) ∨ (¬ p 3952) ∨ (¬ p 4109) ∨ (¬ p 4646) ∨ (¬ p 4700) :=
  ElevenRUP.step52609 (p 2027) (p 2156) (p 2437) (p 3952) (p 4109) (p 4646) (p 4700) (derived40810 p h) (h 25943)

theorem derived52611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2928) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3452) ∨ (¬ p 3644) ∨ (¬ p 4133) ∨ (¬ p 4347) :=
  ElevenRUP.step52611 (p 2027) (p 2248) (p 2928) (p 3166) (p 3256) (p 3452) (p 3644) (p 4133) (p 4347) (derived40810 p h) (h 25946)

theorem derived52612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3471) ∨ (¬ p 4320) ∨ (¬ p 4344) ∨ (¬ p 5053) :=
  ElevenRUP.step52612 (p 2027) (p 2138) (p 3471) (p 4320) (p 4344) (p 5053) (derived40810 p h) (h 25947)

theorem derived52613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2958) ∨ (¬ p 2963) ∨ (¬ p 3051) ∨ (¬ p 4320) ∨ (¬ p 4700) ∨ (¬ p 4972) :=
  ElevenRUP.step52613 (p 2027) (p 2958) (p 2963) (p 3051) (p 4320) (p 4700) (p 4972) (derived40810 p h) (h 25948)

theorem derived52614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3246) ∨ (¬ p 3471) ∨ (¬ p 3570) :=
  ElevenRUP.step52614 (p 1983) (p 2027) (p 2611) (p 2717) (p 3246) (p 3471) (p 3570) (h 2143) (derived40810 p h) (derived40877 p h) (h 25949)

theorem derived52615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3193) ∨ (¬ p 3574) ∨ (¬ p 4022) ∨ (¬ p 4191) :=
  ElevenRUP.step52615 (p 1994) (p 2027) (p 2493) (p 2764) (p 3193) (p 3574) (p 4022) (p 4191) (h 2154) (derived40810 p h) (derived40882 p h) (h 25950)

theorem derived52616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2839) ∨ (¬ p 3471) ∨ (¬ p 3588) ∨ (¬ p 3589) :=
  ElevenRUP.step52616 (p 2001) (p 2027) (p 2619) (p 2699) (p 2839) (p 3471) (p 3588) (p 3589) (h 2161) (derived40810 p h) (derived40881 p h) (h 25951)

theorem derived52618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 5193) :=
  ElevenRUP.step52618 (p 2027) (p 2210) (p 2579) (p 2588) (p 2881) (p 2891) (p 4107) (p 4666) (p 5193) (derived40810 p h) (h 25957)

theorem derived52619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3555) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4377) ∨ (¬ p 4666) :=
  ElevenRUP.step52619 (p 2027) (p 3365) (p 3366) (p 3399) (p 3527) (p 3555) (p 3572) (p 3947) (p 4377) (p 4666) (derived40810 p h) (h 25958)

theorem derived52620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3097) ∨ (¬ p 3920) ∨ (¬ p 4107) ∨ (¬ p 4718) :=
  ElevenRUP.step52620 (p 2027) (p 2417) (p 3097) (p 3920) (p 4107) (p 4718) (derived40810 p h) (h 25959)

theorem derived52621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2440) ∨ (¬ p 2476) ∨ (¬ p 3083) ∨ (¬ p 4108) :=
  ElevenRUP.step52621 (p 1977) (p 2027) (p 2202) (p 2241) (p 2440) (p 2476) (p 3083) (p 4108) (h 2137) (derived40810 p h) (derived40867 p h) (h 25960)

theorem derived52622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3097) ∨ (¬ p 3758) ∨ (¬ p 4405) ∨ (¬ p 4441) :=
  ElevenRUP.step52622 (p 2027) (p 2619) (p 3097) (p 3758) (p 4405) (p 4441) (derived40810 p h) (h 25963)

theorem derived52624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3005) ∨ (¬ p 3180) ∨ (¬ p 4035) ∨ (¬ p 5107) :=
  ElevenRUP.step52624 (p 2027) (p 2088) (p 3005) (p 3180) (p 4035) (p 5107) (derived40810 p h) (h 25968)

theorem derived52625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2307) ∨ (¬ p 2509) ∨ (¬ p 2608) ∨ (¬ p 2962) ∨ (¬ p 3097) ∨ (¬ p 3370) ∨ (¬ p 3452) ∨ (¬ p 4377) ∨ (¬ p 4384) :=
  ElevenRUP.step52625 (p 2027) (p 2187) (p 2307) (p 2509) (p 2608) (p 2962) (p 3097) (p 3370) (p 3452) (p 4377) (p 4384) (derived40810 p h) (h 25969)

theorem derived52626 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4129) ∨ (¬ p 4425) ∨ (¬ p 4733) ∨ (¬ p 4826) :=
  ElevenRUP.step52626 (p 2027) (p 2132) (p 2870) (p 3193) (p 3452) (p 4129) (p 4425) (p 4733) (p 4826) (derived40810 p h) (h 25970)

theorem derived52627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2685) ∨ (¬ p 2745) ∨ (¬ p 3414) ∨ (¬ p 4111) :=
  ElevenRUP.step52627 (p 2027) (p 2651) (p 2685) (p 2745) (p 3414) (p 4111) (derived40810 p h) (h 25971)

theorem derived52628 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2387) ∨ (¬ p 2577) ∨ (¬ p 2588) ∨ (¬ p 2662) ∨ (¬ p 4111) :=
  ElevenRUP.step52628 (p 1977) (p 2027) (p 2352) (p 2387) (p 2577) (p 2588) (p 2662) (p 2997) (p 4111) (h 2137) (derived40810 p h) (derived40890 p h) (h 25972)

theorem derived52635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3791) ∨ (¬ p 4067) ∨ (¬ p 4391) ∨ (¬ p 4405) :=
  ElevenRUP.step52635 (p 2027) (p 2668) (p 3791) (p 4067) (p 4391) (p 4405) (derived40810 p h) (h 25979)

theorem derived52640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2542) ∨ (¬ p 2962) ∨ (¬ p 3654) ∨ (¬ p 3744) ∨ (¬ p 4109) :=
  ElevenRUP.step52640 (p 1975) (p 2027) (p 2274) (p 2542) (p 2545) (p 2962) (p 3654) (p 3744) (p 4109) (h 2135) (derived40810 p h) (derived40876 p h) (h 25984)

theorem derived52645 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2341) ∨ (¬ p 3097) ∨ (¬ p 3367) ∨ (¬ p 3644) ∨ (¬ p 3759) ∨ (¬ p 4173) ∨ (¬ p 4243) ∨ (¬ p 4276) ∨ (¬ p 4734) ∨ (¬ p 5201) :=
  ElevenRUP.step52645 (p 2027) (p 2138) (p 2341) (p 3097) (p 3367) (p 3644) (p 3759) (p 4173) (p 4243) (p 4276) (p 4734) (p 5201) (derived40810 p h) (h 25989)

theorem derived52649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3857) ∨ (¬ p 3859) ∨ (¬ p 3961) ∨ (¬ p 4111) ∨ (¬ p 4155) ∨ (¬ p 4652) :=
  ElevenRUP.step52649 (p 2027) (p 3073) (p 3857) (p 3859) (p 3961) (p 4111) (p 4155) (p 4652) (derived40810 p h) (h 25993)

theorem derived52651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2387) ∨ (¬ p 2819) ∨ (¬ p 3822) ∨ (¬ p 4581) :=
  ElevenRUP.step52651 (p 2027) (p 2295) (p 2387) (p 2819) (p 3822) (p 4581) (derived40810 p h) (h 25995)

theorem derived52653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3346) ∨ (¬ p 3644) ∨ (¬ p 4637) ∨ (¬ p 5201) :=
  ElevenRUP.step52653 (p 2027) (p 2341) (p 3346) (p 3644) (p 4637) (p 5201) (derived40810 p h) (h 25997)

theorem derived52656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2774) ∨ (¬ p 3758) ∨ (¬ p 3958) ∨ (¬ p 4390) :=
  ElevenRUP.step52656 (p 2027) (p 2138) (p 2774) (p 3758) (p 3958) (p 4390) (derived40810 p h) (h 26001)

theorem derived52658 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 2992) ∨ (¬ p 3742) ∨ (¬ p 4111) :=
  ElevenRUP.step52658 (p 1991) (p 2027) (p 2914) (p 2952) (p 2992) (p 3742) (p 4111) (h 2151) (derived40810 p h) (derived40887 p h) (h 26003)

theorem derived52662 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3027) ∨ (¬ p 3414) :=
  ElevenRUP.step52662 (p 2027) (p 2245) (p 2608) (p 2744) (p 3027) (p 3414) (derived40810 p h) (h 26008)

theorem derived52665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3644) ∨ (¬ p 4019) ∨ (¬ p 4324) ∨ (¬ p 4805) ∨ (¬ p 5558) :=
  ElevenRUP.step52665 (p 2010) (p 2027) (p 2462) (p 3644) (p 4019) (p 4324) (p 4805) (p 5558) (h 2170) (derived40810 p h) (derived40875 p h) (h 26011)

theorem derived52669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2396) ∨ (¬ p 2578) ∨ (¬ p 2761) ∨ (¬ p 3422) :=
  ElevenRUP.step52669 (p 1988) (p 2027) (p 2307) (p 2396) (p 2578) (p 2761) (p 2842) (p 3422) (h 2148) (derived40810 p h) (derived40885 p h) (h 26015)

theorem derived52672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2396) ∨ (¬ p 2761) ∨ (¬ p 2797) ∨ (¬ p 3567) :=
  ElevenRUP.step52672 (p 1988) (p 2027) (p 2307) (p 2396) (p 2622) (p 2761) (p 2797) (p 3567) (h 2148) (derived40810 p h) (derived40878 p h) (h 26018)

theorem derived52674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2363) ∨ (¬ p 2383) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3555) ∨ (¬ p 3694) ∨ (¬ p 3987) ∨ (¬ p 4348) ∨ (¬ p 4418) ∨ (¬ p 4905) :=
  ElevenRUP.step52674 (p 2027) (p 2246) (p 2363) (p 2383) (p 2608) (p 2744) (p 3555) (p 3694) (p 3987) (p 4348) (p 4418) (p 4905) (derived40810 p h) (h 26020)

theorem derived52677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2630) ∨ (¬ p 2881) ∨ (¬ p 3519) ∨ (¬ p 4116) :=
  ElevenRUP.step52677 (p 1998) (p 2027) (p 2230) (p 2427) (p 2622) (p 2630) (p 2881) (p 3519) (p 4116) (h 2158) (derived40810 p h) (derived40878 p h) (h 26023)

theorem derived52680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3859) ∨ (¬ p 4111) ∨ (¬ p 4118) ∨ (¬ p 4195) ∨ (¬ p 4196) :=
  ElevenRUP.step52680 (p 1987) (p 2027) (p 2545) (p 3073) (p 3859) (p 4111) (p 4118) (p 4195) (p 4196) (h 2147) (derived40810 p h) (derived40876 p h) (h 26027)

theorem derived52682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 2573) ∨ (¬ p 2589) ∨ (¬ p 4347) :=
  ElevenRUP.step52682 (p 1981) (p 2027) (p 2202) (p 2510) (p 2528) (p 2573) (p 2589) (p 4347) (h 2141) (derived40810 p h) (derived40867 p h) (h 26029)

theorem derived52684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2534) ∨ (¬ p 2850) ∨ (¬ p 3874) :=
  ElevenRUP.step52684 (p 1997) (p 2027) (p 2169) (p 2363) (p 2534) (p 2850) (p 3874) (h 2157) (derived40810 p h) (derived40866 p h) (h 26031)

theorem derived52685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2481) ∨ (¬ p 2850) ∨ (¬ p 3857) ∨ (¬ p 3874) :=
  ElevenRUP.step52685 (p 1997) (p 2027) (p 2169) (p 2363) (p 2481) (p 2850) (p 3857) (p 3874) (h 2157) (derived40810 p h) (derived40866 p h) (h 26032)

theorem derived52686 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3266) ∨ (¬ p 3690) ∨ (¬ p 4191) ∨ (¬ p 4623) :=
  ElevenRUP.step52686 (p 1998) (p 2027) (p 2766) (p 2881) (p 3266) (p 3690) (p 4191) (p 4623) (h 2158) (derived40810 p h) (derived40884 p h) (h 26033)

theorem derived52689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2696) ∨ (¬ p 2995) ∨ (¬ p 3136) ∨ (¬ p 3570) :=
  ElevenRUP.step52689 (p 1985) (p 2027) (p 2264) (p 2611) (p 2696) (p 2995) (p 3136) (p 3570) (h 2145) (derived40810 p h) (derived40877 p h) (h 26036)

theorem derived52691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2427) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3556) ∨ (¬ p 3904) ∨ (¬ p 4382) ∨ (¬ p 4669) ∨ (¬ p 4729) ∨ (¬ p 4948) :=
  ElevenRUP.step52691 (p 2027) (p 2363) (p 2427) (p 2774) (p 2819) (p 3556) (p 3904) (p 4382) (p 4669) (p 4729) (p 4948) (derived40810 p h) (h 26039)

theorem derived52692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2807) ∨ (¬ p 2963) ∨ (¬ p 3572) ∨ (¬ p 4972) :=
  ElevenRUP.step52692 (p 2027) (p 2630) (p 2807) (p 2963) (p 3572) (p 4972) (derived40810 p h) (h 26040)

theorem derived52693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2668) ∨ (¬ p 4358) ∨ (¬ p 4841) ∨ (¬ p 4972) :=
  ElevenRUP.step52693 (p 2027) (p 2630) (p 2668) (p 4358) (p 4841) (p 4972) (derived40810 p h) (h 26041)

theorem derived52695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3136) ∨ (¬ p 3877) ∨ (¬ p 4312) ∨ (¬ p 4702) :=
  ElevenRUP.step52695 (p 2027) (p 2373) (p 3136) (p 3877) (p 4312) (p 4702) (derived40810 p h) (h 26043)

theorem derived52696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 3347) ∨ (¬ p 3646) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 3904) ∨ (¬ p 3954) ∨ (¬ p 4203) ∨ (¬ p 4260) ∨ (¬ p 4831) ∨ (¬ p 5216) :=
  ElevenRUP.step52696 (p 2027) (p 2588) (p 3347) (p 3646) (p 3707) (p 3830) (p 3904) (p 3954) (p 4203) (p 4260) (p 4831) (p 5216) (derived40810 p h) (h 26044)

theorem derived52699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3073) ∨ (¬ p 3347) ∨ (¬ p 3449) ∨ (¬ p 3690) ∨ (¬ p 3954) ∨ (¬ p 4235) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step52699 (p 2027) (p 2589) (p 3073) (p 3347) (p 3449) (p 3690) (p 3954) (p 4235) (p 4669) (p 5216) (derived40810 p h) (h 26047)

theorem derived52700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 4181) ∨ (¬ p 4416) ∨ (¬ p 4877) ∨ (¬ p 5316) ∨ (¬ p 5590) :=
  ElevenRUP.step52700 (p 2027) (p 2210) (p 4181) (p 4416) (p 4877) (p 5316) (p 5590) (derived40810 p h) (h 26048)

theorem derived52703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3027) ∨ (¬ p 3276) ∨ (¬ p 3552) ∨ (¬ p 3585) ∨ (¬ p 4641) ∨ (¬ p 4737) ∨ (¬ p 5158) ∨ (¬ p 5387) :=
  ElevenRUP.step52703 (p 2027) (p 2396) (p 2696) (p 2742) (p 3027) (p 3276) (p 3552) (p 3585) (p 4641) (p 4737) (p 5158) (p 5387) (derived40810 p h) (h 26051)

theorem derived52705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2630) ∨ (¬ p 3019) ∨ (¬ p 3323) ∨ (¬ p 4137) :=
  ElevenRUP.step52705 (p 1981) (p 2027) (p 2352) (p 2622) (p 2630) (p 3019) (p 3323) (p 4137) (h 2141) (derived40810 p h) (derived40878 p h) (h 26053)

theorem derived52706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2387) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 2778) ∨ (¬ p 2819) ∨ (¬ p 3366) ∨ (¬ p 3917) ∨ (¬ p 4625) :=
  ElevenRUP.step52706 (p 2027) (p 2246) (p 2387) (p 2417) (p 2437) (p 2651) (p 2744) (p 2778) (p 2819) (p 3366) (p 3917) (p 4625) (derived40810 p h) (h 26054)

theorem derived52707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3654) ∨ (¬ p 3953) ∨ (¬ p 4026) ∨ (¬ p 5020) :=
  ElevenRUP.step52707 (p 2027) (p 2247) (p 2744) (p 3654) (p 3953) (p 4026) (p 5020) (derived40810 p h) (h 26055)

theorem derived52708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 3266) ∨ (¬ p 3950) ∨ (¬ p 4379) ∨ (¬ p 5387) :=
  ElevenRUP.step52708 (p 2027) (p 2246) (p 2417) (p 2437) (p 2651) (p 2744) (p 3266) (p 3950) (p 4379) (p 5387) (derived40810 p h) (h 26056)

theorem derived52711 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3365) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4972) :=
  ElevenRUP.step52711 (p 2027) (p 2651) (p 3365) (p 4117) (p 4195) (p 4972) (derived40810 p h) (h 26061)

theorem derived52712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3365) ∨ (¬ p 4235) :=
  ElevenRUP.step52712 (p 1997) (p 2027) (p 2132) (p 2622) (p 2870) (p 3365) (p 4235) (h 2157) (derived40810 p h) (derived40878 p h) (h 26062)

theorem derived52714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2437) ∨ (¬ p 2608) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 2911) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) :=
  ElevenRUP.step52714 (p 2027) (p 2246) (p 2437) (p 2608) (p 2651) (p 2744) (p 2911) (p 3817) (p 4366) (p 4666) (derived40810 p h) (h 26064)

theorem derived52715 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2383) ∨ (¬ p 2744) ∨ (¬ p 3923) ∨ (¬ p 3953) ∨ (¬ p 5020) :=
  ElevenRUP.step52715 (p 2027) (p 2247) (p 2383) (p 2744) (p 3923) (p 3953) (p 5020) (derived40810 p h) (h 26065)

theorem derived52716 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 2774) ∨ (¬ p 3589) ∨ (¬ p 3688) :=
  ElevenRUP.step52716 (p 2027) (p 2247) (p 2744) (p 2774) (p 3589) (p 3688) (derived40810 p h) (h 26066)

theorem derived52717 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2246) ∨ (¬ p 2284) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2946) ∨ (¬ p 3548) ∨ (¬ p 4133) ∨ (¬ p 4366) :=
  ElevenRUP.step52717 (p 2027) (p 2187) (p 2246) (p 2284) (p 2608) (p 2744) (p 2946) (p 3548) (p 4133) (p 4366) (derived40810 p h) (h 26067)

theorem derived52725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4244) ∨ (¬ p 4347) ∨ (¬ p 4786) :=
  ElevenRUP.step52725 (p 2027) (p 2138) (p 3166) (p 3256) (p 3570) (p 4133) (p 4244) (p 4347) (p 4786) (derived40810 p h) (h 26077)

theorem derived52726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2651) ∨ (¬ p 2668) ∨ (¬ p 3983) ∨ (¬ p 4972) :=
  ElevenRUP.step52726 (p 2027) (p 2387) (p 2651) (p 2668) (p 3983) (p 4972) (derived40810 p h) (h 26078)

theorem derived52729 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 3791) ∨ (¬ p 3834) ∨ (¬ p 3847) ∨ (¬ p 4376) ∨ (¬ p 4826) ∨ (¬ p 5284) :=
  ElevenRUP.step52729 (p 2027) (p 2553) (p 2573) (p 2608) (p 3519) (p 3791) (p 3834) (p 3847) (p 4376) (p 4826) (p 5284) (derived40810 p h) (h 26082)

theorem derived52731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2696) ∨ (¬ p 3425) ∨ (¬ p 4324) :=
  ElevenRUP.step52731 (p 1987) (p 2027) (p 2396) (p 2696) (p 2997) (p 3425) (p 4324) (h 2147) (derived40810 p h) (derived40890 p h) (h 26086)

theorem derived52732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2737) ∨ (¬ p 2785) ∨ (¬ p 3688) ∨ (¬ p 4107) :=
  ElevenRUP.step52732 (p 1987) (p 2027) (p 2313) (p 2462) (p 2737) (p 2785) (p 3688) (p 4107) (h 2147) (derived40810 p h) (derived40875 p h) (h 26087)

theorem derived52738 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3549) ∨ (¬ p 3953) ∨ (¬ p 4737) :=
  ElevenRUP.step52738 (p 2027) (p 2122) (p 2774) (p 3549) (p 3953) (p 4737) (derived40810 p h) (h 26095)

theorem derived52739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2588) ∨ (¬ p 2774) ∨ (¬ p 3055) :=
  ElevenRUP.step52739 (p 2005) (p 2027) (p 2122) (p 2588) (p 2774) (p 2842) (p 3055) (h 2165) (derived40810 p h) (derived40885 p h) (h 26096)

theorem derived52740 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2579) ∨ (¬ p 3016) ∨ (¬ p 3644) ∨ (¬ p 5201) :=
  ElevenRUP.step52740 (p 2010) (p 2027) (p 2341) (p 2545) (p 2579) (p 3016) (p 3644) (p 5201) (h 2170) (derived40810 p h) (derived40876 p h) (h 26097)

theorem derived52741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3379) ∨ (¬ p 3486) ∨ (¬ p 3555) :=
  ElevenRUP.step52741 (p 1995) (p 2027) (p 2202) (p 2427) (p 3379) (p 3486) (p 3555) (h 2155) (derived40810 p h) (derived40867 p h) (h 26098)

theorem derived52752 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2829) ∨ (¬ p 3588) ∨ (¬ p 4471) ∨ (¬ p 4843) :=
  ElevenRUP.step52752 (p 2027) (p 2295) (p 2829) (p 3588) (p 4471) (p 4843) (derived40810 p h) (h 26111)

theorem derived52753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 3556) ∨ (¬ p 3582) ∨ (¬ p 3584) ∨ (¬ p 4031) ∨ (¬ p 4715) :=
  ElevenRUP.step52753 (p 2027) (p 2870) (p 3556) (p 3582) (p 3584) (p 4031) (p 4715) (derived40810 p h) (h 26112)

theorem derived52754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3413) ∨ (¬ p 3556) ∨ (¬ p 3574) ∨ (¬ p 4031) ∨ (¬ p 4715) :=
  ElevenRUP.step52754 (p 2027) (p 2901) (p 3413) (p 3556) (p 3574) (p 4031) (p 4715) (derived40810 p h) (h 26113)

theorem derived52758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 2780) ∨ (¬ p 3379) ∨ (¬ p 3822) ∨ (¬ p 4736) ∨ (¬ p 4902) :=
  ElevenRUP.step52758 (p 2027) (p 2299) (p 2373) (p 2406) (p 2780) (p 3379) (p 3822) (p 4736) (p 4902) (derived40810 p h) (h 26118)

theorem derived52759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3979) ∨ (¬ p 4035) ∨ (¬ p 4376) ∨ (¬ p 5119) ∨ (¬ p 5284) :=
  ElevenRUP.step52759 (p 2027) (p 2352) (p 2573) (p 3365) (p 3366) (p 3519) (p 3979) (p 4035) (p 4376) (p 5119) (p 5284) (derived40810 p h) (h 26125)

theorem derived52760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 3212) ∨ (¬ p 3745) ∨ (¬ p 4195) ∨ (¬ p 5046) :=
  ElevenRUP.step52760 (p 2027) (p 2951) (p 3136) (p 3212) (p 3745) (p 4195) (p 5046) (derived40810 p h) (h 26126)

theorem derived52767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2373) ∨ (¬ p 2387) ∨ (¬ p 2459) ∨ (¬ p 2542) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 2778) ∨ (¬ p 3366) ∨ (¬ p 4347) ∨ (¬ p 4902) :=
  ElevenRUP.step52767 (p 2027) (p 2246) (p 2373) (p 2387) (p 2459) (p 2542) (p 2651) (p 2744) (p 2778) (p 3366) (p 4347) (p 4902) (derived40810 p h) (h 26135)

theorem derived52770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 4261) ∨ (¬ p 4436) ∨ (¬ p 5242) :=
  ElevenRUP.step52770 (p 2027) (p 2088) (p 2247) (p 2744) (p 4261) (p 4436) (p 5242) (derived40810 p h) (h 26138)

theorem derived52771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2247) ∨ (¬ p 2459) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 4340) ∨ (¬ p 4902) :=
  ElevenRUP.step52771 (p 2027) (p 2104) (p 2166) (p 2210) (p 2247) (p 2459) (p 2744) (p 3366) (p 4340) (p 4902) (derived40810 p h) (h 26139)

theorem derived52772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 4172) ∨ (¬ p 4173) ∨ (¬ p 4874) :=
  ElevenRUP.step52772 (p 2027) (p 2156) (p 2247) (p 2744) (p 4172) (p 4173) (p 4874) (derived40810 p h) (h 26140)

theorem derived52773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2396) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 4261) :=
  ElevenRUP.step52773 (p 2027) (p 2246) (p 2295) (p 2331) (p 2396) (p 2608) (p 2744) (p 3860) (p 3950) (p 4261) (derived40810 p h) (h 26141)

theorem derived52776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2396) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3548) ∨ (¬ p 4366) ∨ (¬ p 4668) :=
  ElevenRUP.step52776 (p 2027) (p 2246) (p 2295) (p 2331) (p 2396) (p 2608) (p 2744) (p 3548) (p 4366) (p 4668) (derived40810 p h) (h 26144)

theorem derived52777 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3256) ∨ (¬ p 3548) ∨ (¬ p 4133) ∨ (¬ p 4341) ∨ (¬ p 4347) ∨ (¬ p 4366) :=
  ElevenRUP.step52777 (p 2027) (p 2246) (p 2331) (p 2608) (p 2744) (p 3256) (p 3548) (p 4133) (p 4341) (p 4347) (p 4366) (derived40810 p h) (h 26145)

theorem derived52778 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3286) ∨ (¬ p 3506) ∨ (¬ p 3555) ∨ (¬ p 4034) ∨ (¬ p 4444) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step52778 (p 2027) (p 2246) (p 2608) (p 2744) (p 3286) (p 3506) (p 3555) (p 4034) (p 4444) (p 4948) (p 5059) (derived40810 p h) (h 26146)

theorem derived52779 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2744) ∨ (¬ p 3055) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (¬ p 3366) ∨ (¬ p 3876) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step52779 (p 2027) (p 2246) (p 2744) (p 3055) (p 3166) (p 3256) (p 3266) (p 3366) (p 3876) (p 4831) (p 5503) (derived40810 p h) (h 26147)

theorem derived52780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3547) ∨ (¬ p 3570) ∨ (¬ p 3791) ∨ (¬ p 4244) ∨ (¬ p 5564) :=
  ElevenRUP.step52780 (p 2027) (p 2138) (p 2247) (p 2744) (p 3366) (p 3399) (p 3547) (p 3570) (p 3791) (p 4244) (p 5564) (derived40810 p h) (h 26148)

theorem derived52781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3979) ∨ (¬ p 4318) ∨ (¬ p 5122) :=
  ElevenRUP.step52781 (p 2027) (p 2138) (p 2247) (p 2744) (p 3366) (p 3449) (p 3692) (p 3694) (p 3979) (p 4318) (p 5122) (derived40810 p h) (h 26149)

theorem derived52782 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2744) ∨ (¬ p 3323) ∨ (¬ p 3366) ∨ (¬ p 3461) ∨ (¬ p 4244) ∨ (¬ p 4831) ∨ (¬ p 5660) :=
  ElevenRUP.step52782 (p 2027) (p 2138) (p 2246) (p 2331) (p 2744) (p 3323) (p 3366) (p 3461) (p 4244) (p 4831) (p 5660) (derived40810 p h) (h 26150)

theorem derived52784 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3876) ∨ (¬ p 4381) :=
  ElevenRUP.step52784 (p 1983) (p 2027) (p 2914) (p 3276) (p 3333) (p 3876) (p 4381) (h 2143) (derived40810 p h) (derived40887 p h) (h 26152)

theorem derived52785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2589) ∨ (¬ p 2668) ∨ (¬ p 2850) ∨ (¬ p 3905) ∨ (¬ p 4697) ∨ (¬ p 4786) ∨ (¬ p 5160) :=
  ElevenRUP.step52785 (p 2027) (p 2331) (p 2363) (p 2589) (p 2668) (p 2850) (p 3905) (p 4697) (p 4786) (p 5160) (derived40810 p h) (h 26153)

theorem derived52787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 2744) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3684) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step52787 (p 2027) (p 2246) (p 2331) (p 2363) (p 2668) (p 2744) (p 3055) (p 3366) (p 3684) (p 4948) (p 5059) (derived40810 p h) (h 26155)

theorem derived52789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3516) ∨ (¬ p 3545) ∨ (¬ p 3554) ∨ (¬ p 3817) ∨ (¬ p 4874) :=
  ElevenRUP.step52789 (p 2027) (p 2247) (p 2744) (p 3516) (p 3545) (p 3554) (p 3817) (p 4874) (derived40810 p h) (h 26157)

theorem derived52790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2744) ∨ (¬ p 3027) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3584) ∨ (¬ p 4137) ∨ (¬ p 4604) :=
  ElevenRUP.step52790 (p 2027) (p 2264) (p 2459) (p 2744) (p 3027) (p 3055) (p 3366) (p 3584) (p 4137) (p 4604) (derived40810 p h) (h 26158)

theorem derived52791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2264) ∨ (¬ p 2744) ∨ (¬ p 2807) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3941) ∨ (¬ p 4425) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step52791 (p 2027) (p 2246) (p 2264) (p 2744) (p 2807) (p 3055) (p 3366) (p 3941) (p 4425) (p 5119) (p 5160) (derived40810 p h) (h 26159)

theorem derived52793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2264) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2807) ∨ (¬ p 3834) ∨ (¬ p 3941) ∨ (¬ p 4321) ∨ (¬ p 5119) :=
  ElevenRUP.step52793 (p 2027) (p 2246) (p 2264) (p 2608) (p 2744) (p 2807) (p 3834) (p 3941) (p 4321) (p 5119) (derived40810 p h) (h 26161)

theorem derived52798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3073) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4669) :=
  ElevenRUP.step52798 (p 2027) (p 2138) (p 2247) (p 2744) (p 3073) (p 3366) (p 3449) (p 3690) (p 4244) (p 4669) (derived40810 p h) (h 26166)

theorem derived52801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2247) ∨ (¬ p 2459) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3685) ∨ (¬ p 4340) ∨ (¬ p 4902) :=
  ElevenRUP.step52801 (p 2027) (p 2166) (p 2210) (p 2247) (p 2459) (p 2744) (p 3366) (p 3425) (p 3685) (p 4340) (p 4902) (derived40810 p h) (h 26169)

theorem derived52802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2247) ∨ (¬ p 2313) ∨ (¬ p 2518) ∨ (¬ p 2744) ∨ (¬ p 2778) ∨ (¬ p 3366) ∨ (¬ p 3379) ∨ (¬ p 4358) ∨ (¬ p 4596) :=
  ElevenRUP.step52802 (p 2027) (p 2122) (p 2247) (p 2313) (p 2518) (p 2744) (p 2778) (p 3366) (p 3379) (p 4358) (p 4596) (derived40810 p h) (h 26170)

theorem derived52807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3548) ∨ (¬ p 3692) ∨ (¬ p 4366) ∨ (¬ p 4902) :=
  ElevenRUP.step52807 (p 2027) (p 2246) (p 2608) (p 2744) (p 3166) (p 3256) (p 3548) (p 3692) (p 4366) (p 4902) (derived40810 p h) (h 26175)

theorem derived52809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2246) ∨ (¬ p 2299) ∨ (¬ p 2440) ∨ (¬ p 2663) ∨ (¬ p 2744) ∨ (¬ p 2780) ∨ (¬ p 3343) ∨ (¬ p 3366) ∨ (¬ p 3822) ∨ (¬ p 4451) ∨ (¬ p 4668) :=
  ElevenRUP.step52809 (p 2027) (p 2230) (p 2246) (p 2299) (p 2440) (p 2663) (p 2744) (p 2780) (p 3343) (p 3366) (p 3822) (p 4451) (p 4668) (derived40810 p h) (h 26177)

theorem derived52812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 3276) ∨ (¬ p 3343) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step52812 (p 2027) (p 2246) (p 2651) (p 2744) (p 3276) (p 3343) (p 3366) (p 3425) (p 3659) (p 5123) (p 5558) (derived40810 p h) (h 26180)

theorem derived52819 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2284) ∨ (¬ p 2744) ∨ (¬ p 2946) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 3551) ∨ (¬ p 3657) ∨ (¬ p 3670) ∨ (¬ p 3820) ∨ (¬ p 4381) ∨ (¬ p 5271) :=
  ElevenRUP.step52819 (p 2027) (p 2246) (p 2284) (p 2744) (p 2946) (p 3125) (p 3366) (p 3551) (p 3657) (p 3670) (p 3820) (p 4381) (p 5271) (derived40810 p h) (h 26187)

theorem derived52820 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2313) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 4138) ∨ (¬ p 4668) ∨ (¬ p 5015) :=
  ElevenRUP.step52820 (p 2027) (p 2248) (p 2313) (p 2901) (p 2946) (p 3246) (p 3309) (p 3923) (p 4138) (p 4668) (p 5015) (derived40810 p h) (h 26188)

theorem derived52821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2782) ∨ (¬ p 3609) ∨ (¬ p 3955) ∨ (¬ p 4261) ∨ (¬ p 4318) ∨ (¬ p 4861) :=
  ElevenRUP.step52821 (p 2027) (p 2313) (p 2782) (p 3609) (p 3955) (p 4261) (p 4318) (p 4861) (derived40810 p h) (h 26189)

theorem derived52823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 3237) ∨ (¬ p 3286) ∨ (¬ p 5175) :=
  ElevenRUP.step52823 (p 1990) (p 2027) (p 2563) (p 2622) (p 2630) (p 2657) (p 3237) (p 3286) (p 5175) (h 2150) (derived40810 p h) (derived40878 p h) (h 26192)

theorem derived52824 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 3286) ∨ (¬ p 3506) ∨ (¬ p 3591) ∨ (¬ p 4026) ∨ (¬ p 4396) ∨ (¬ p 4444) ∨ (¬ p 4669) :=
  ElevenRUP.step52824 (p 2027) (p 2246) (p 2608) (p 2744) (p 3286) (p 3506) (p 3591) (p 4026) (p 4396) (p 4444) (p 4669) (derived40810 p h) (h 26194)

theorem derived52825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2958) ∨ (¬ p 3156) ∨ (¬ p 3548) ∨ (¬ p 3952) ∨ (¬ p 4366) ∨ (¬ p 4902) :=
  ElevenRUP.step52825 (p 2027) (p 2156) (p 2246) (p 2608) (p 2744) (p 2958) (p 3156) (p 3548) (p 3952) (p 4366) (p 4902) (derived40810 p h) (h 26195)

theorem derived52828 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2246) ∨ (¬ p 2363) ∨ (¬ p 2608) ∨ (¬ p 2668) ∨ (¬ p 2744) ∨ (¬ p 2958) ∨ (¬ p 3745) ∨ (¬ p 3860) ∨ (¬ p 4286) ∨ (¬ p 4370) ∨ (¬ p 5118) :=
  ElevenRUP.step52828 (p 2027) (p 2156) (p 2246) (p 2363) (p 2608) (p 2668) (p 2744) (p 2958) (p 3745) (p 3860) (p 4286) (p 4370) (p 5118) (derived40810 p h) (h 26199)

end ElevenLogic
