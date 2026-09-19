import SunPrize.Certificate.Derived059
import SunPrize.Certificate.Logic060
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived110909 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2761) ∨ (¬ p 2996) ∨ (¬ p 5284) ∨ (p 2241) :=
  ElevenRUP.step110909 (p 2241) (p 2449) (p 2761) (p 2996) (p 4429) (p 5284) (derived99873 p h) (derived102487 p h)

theorem derived110910 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 5284) ∨ (¬ p 3552) ∨ (¬ p 3276) ∨ (p 2352) ∨ (¬ p 4422) :=
  ElevenRUP.step110910 (p 2352) (p 2449) (p 3276) (p 3552) (p 4422) (p 4429) (p 5284) (derived93260 p h) (derived102487 p h)

theorem derived110911 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 5284) ∨ (¬ p 2264) ∨ (p 2717) ∨ (¬ p 3266) ∨ (¬ p 4136) :=
  ElevenRUP.step110911 (p 2264) (p 2449) (p 2717) (p 3266) (p 4136) (p 4429) (p 5284) (derived93267 p h) (derived102487 p h)

theorem derived110912 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2761) ∨ (¬ p 2396) ∨ (¬ p 5284) ∨ (¬ p 3579) :=
  ElevenRUP.step110912 (p 2396) (p 2449) (p 2761) (p 3579) (p 4276) (p 4429) (p 5284) (derived105516 p h) (derived41080 p h) (derived102487 p h)

theorem derived110913 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 3767) ∨ (¬ p 3552) ∨ (¬ p 5284) ∨ (p 2383) ∨ (¬ p 4036) :=
  ElevenRUP.step110913 (p 2383) (p 2449) (p 3552) (p 3767) (p 4036) (p 4429) (p 5284) (derived93305 p h) (derived102487 p h)

theorem derived110916 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (p 2972) ∨ (¬ p 3707) ∨ (¬ p 4386) ∨ (¬ p 5284) ∨ (¬ p 2982) :=
  ElevenRUP.step110916 (p 2449) (p 2972) (p 2982) (p 3707) (p 4386) (p 4429) (p 5284) (derived110208 p h) (derived102487 p h)

theorem derived110920 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2761) ∨ (¬ p 5284) ∨ (¬ p 2192) ∨ (¬ p 3125) ∨ (¬ p 2210) ∨ (p 2807) :=
  ElevenRUP.step110920 (p 2192) (p 2210) (p 2254) (p 2449) (p 2761) (p 2807) (p 3125) (p 4429) (p 4621) (p 5284) (derived105366 p h) (derived105407 p h) (derived93298 p h) (derived102487 p h)

theorem derived110924 (p : Nat → Prop) (h : Inputs p) :
    (p 2449) ∨ (¬ p 2761) ∨ (¬ p 5284) ∨ (p 2807) ∨ (¬ p 3564) ∨ (¬ p 2656) ∨ (¬ p 2573) ∨ (¬ p 2727) :=
  ElevenRUP.step110924 (p 2249) (p 2449) (p 2573) (p 2656) (p 2727) (p 2761) (p 2807) (p 3564) (p 4429) (p 4621) (p 5284) (derived106513 p h) (derived105407 p h) (derived93276 p h) (derived102487 p h)

theorem derived110930 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3990) ∨ (¬ p 2383) :=
  ElevenRUP.step110930 (p 2383) (p 3654) (p 3990) (p 5379) (derived110546 p h) (derived102542 p h)

theorem derived110932 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 2307) ∨ (¬ p 3125) ∨ (p 2553) :=
  ElevenRUP.step110932 (p 2307) (p 2553) (p 3125) (p 3654) (p 5379) (derived110551 p h) (derived102542 p h)

theorem derived110939 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3516) ∨ (p 2122) ∨ (p 2449) ∨ (¬ p 3483) :=
  ElevenRUP.step110939 (p 2122) (p 2449) (p 3483) (p 3516) (p 3654) (p 5379) (derived109545 p h) (derived102542 p h)

theorem derived110941 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3516) ∨ (p 2295) ∨ (¬ p 3323) ∨ (p 3246) :=
  ElevenRUP.step110941 (p 2295) (p 3246) (p 3323) (p 3516) (p 3654) (p 5379) (derived109551 p h) (derived102542 p h)

theorem derived110944 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 2088) ∨ (¬ p 3483) ∨ (p 2819) ∨ (p 3146) :=
  ElevenRUP.step110944 (p 2088) (p 2819) (p 3146) (p 3483) (p 3654) (p 5379) (derived109903 p h) (derived102542 p h)

theorem derived110948 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 2797) ∨ (p 3755) ∨ (¬ p 3297) ∨ (¬ p 3125) :=
  ElevenRUP.step110948 (p 2797) (p 3125) (p 3297) (p 3654) (p 3755) (p 4564) (p 5379) (derived105401 p h) (derived92283 p h) (derived102542 p h)

theorem derived110949 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 2797) ∨ (p 3755) ∨ (¬ p 3319) ∨ (¬ p 3297) :=
  ElevenRUP.step110949 (p 2797) (p 3297) (p 3319) (p 3654) (p 3755) (p 4761) (p 5379) (derived106234 p h) (derived92300 p h) (derived102542 p h)

theorem derived110951 (p : Nat → Prop) (h : Inputs p) :
    (p 3654) ∨ (¬ p 3516) ∨ (¬ p 3319) ∨ (p 3246) ∨ (p 2553) ∨ (¬ p 2498) :=
  ElevenRUP.step110951 (p 2498) (p 2553) (p 3246) (p 3319) (p 3516) (p 3654) (p 5379) (derived109555 p h) (derived102542 p h)

theorem derived110959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3189) ∨ (¬ p 3848) :=
  ElevenRUP.step110959 (p 3189) (p 3256) (p 3848) (p 5111) (h 19858) (derived96299 p h)

theorem derived110960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3005) ∨ (p 3755) :=
  ElevenRUP.step110960 (p 3005) (p 3256) (p 3755) (p 5111) (h 21750) (derived96299 p h)

theorem derived110961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 3286) ∨ (¬ p 3166) :=
  ElevenRUP.step110961 (p 3166) (p 3256) (p 3286) (p 5111) (derived95061 p h) (derived96299 p h)

theorem derived110963 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 3146) ∨ (¬ p 4043) ∨ (p 3266) ∨ (¬ p 3506) :=
  ElevenRUP.step110963 (p 3146) (p 3256) (p 3266) (p 3506) (p 4043) (p 5111) (derived98691 p h) (derived96299 p h)

theorem derived110964 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3846) ∨ (¬ p 2727) ∨ (p 3707) ∨ (¬ p 3506) :=
  ElevenRUP.step110964 (p 2727) (p 3256) (p 3506) (p 3707) (p 3846) (p 5008) (p 5111) (derived105469 p h) (derived82323 p h) (derived96299 p h)

theorem derived110966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 3286) ∨ (¬ p 2696) ∨ (¬ p 2245) ∨ (¬ p 3005) :=
  ElevenRUP.step110966 (p 2245) (p 2696) (p 3005) (p 3256) (p 3286) (p 4733) (p 5111) (derived105430 p h) (derived93438 p h) (derived96299 p h)

theorem derived110978 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3005) ∨ (p 2417) ∨ (p 3266) ∨ (p 3201) ∨ (p 2651) ∨ (¬ p 3506) ∨ (¬ p 3683) :=
  ElevenRUP.step110978 (p 2417) (p 2651) (p 3005) (p 3201) (p 3256) (p 3266) (p 3506) (p 3683) (p 4669) (p 5111) (derived105415 p h) (derived87923 p h) (derived96299 p h)

theorem derived110984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3506) ∨ (p 3105) ∨ (¬ p 3166) ∨ (¬ p 2860) ∨ (p 3266) ∨ (¬ p 2136) ∨ (¬ p 4033) ∨ (p 2156) :=
  ElevenRUP.step110984 (p 2136) (p 2156) (p 2860) (p 3105) (p 3166) (p 3256) (p 3266) (p 3506) (p 4033) (p 4604) (p 4786) (p 5111) (derived106293 p h) (derived106425 p h) (derived84584 p h) (derived96299 p h)

theorem derived110989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (p 2122) ∨ (p 3266) ∨ (p 2573) ∨ (p 2396) ∨ (¬ p 3166) ∨ (¬ p 3366) ∨ (¬ p 3506) ∨ (¬ p 2246) ∨ (¬ p 3905) ∨ (¬ p 4390) :=
  ElevenRUP.step110989 (p 2122) (p 2246) (p 2396) (p 2573) (p 2744) (p 3166) (p 3256) (p 3266) (p 3366) (p 3506) (p 3905) (p 4390) (p 4669) (p 5111) (derived106503 p h) (derived105415 p h) (derived100954 p h) (derived96299 p h)

theorem derived110990 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (p 3848) ∨ (p 2641) :=
  ElevenRUP.step110990 (p 2641) (p 3323) (p 3848) (p 5274) (derived94417 p h) (derived102539 p h)

theorem derived110991 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3755) ∨ (p 2797) :=
  ElevenRUP.step110991 (p 2797) (p 3323) (p 3755) (p 5274) (derived94955 p h) (derived102539 p h)

theorem derived110992 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3286) ∨ (p 2331) :=
  ElevenRUP.step110992 (p 2331) (p 3286) (p 3323) (p 5274) (derived95305 p h) (derived102539 p h)

theorem derived110995 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3266) ∨ (p 2383) ∨ (¬ p 2668) ∨ (¬ p 5284) :=
  ElevenRUP.step110995 (p 2383) (p 2668) (p 3266) (p 3323) (p 5274) (p 5284) (derived79234 p h) (derived102539 p h)

theorem derived110999 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 5284) ∨ (p 2797) ∨ (¬ p 3461) ∨ (p 2737) :=
  ElevenRUP.step110999 (p 2737) (p 2797) (p 3323) (p 3461) (p 5274) (p 5284) (derived93280 p h) (derived102539 p h)

theorem derived111000 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (p 2797) ∨ (p 2696) ∨ (¬ p 3461) ∨ (¬ p 5284) :=
  ElevenRUP.step111000 (p 2696) (p 2797) (p 3323) (p 3461) (p 5274) (p 5284) (derived93281 p h) (derived102539 p h)

theorem derived111001 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 5284) :=
  ElevenRUP.step111001 (p 3125) (p 3323) (p 3461) (p 4564) (p 5274) (p 5284) (derived105401 p h) (derived41141 p h) (derived102539 p h)

theorem derived111009 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (p 5287) ∨ (¬ p 3830) ∨ (p 2608) ∨ (¬ p 3707) ∨ (¬ p 2295) :=
  ElevenRUP.step111009 (p 2295) (p 2608) (p 3323) (p 3707) (p 3830) (p 5274) (p 5287) (derived109342 p h) (derived102539 p h)

theorem derived111012 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 5300) ∨ (¬ p 3767) ∨ (¬ p 2312) ∨ (¬ p 2668) ∨ (¬ p 5284) :=
  ElevenRUP.step111012 (p 2312) (p 2668) (p 3323) (p 3767) (p 4405) (p 5274) (p 5284) (p 5300) (derived105512 p h) (derived52575 p h) (derived102539 p h)

theorem derived111016 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3631) ∨ (¬ p 5284) ∨ (¬ p 3707) ∨ (¬ p 4337) ∨ (¬ p 2427) ∨ (¬ p 4909) ∨ (¬ p 2819) :=
  ElevenRUP.step111016 (p 2427) (p 2819) (p 3323) (p 3631) (p 3707) (p 4337) (p 4909) (p 5274) (p 5284) (derived110619 p h) (derived102539 p h)

theorem derived111017 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 3461) ∨ (¬ p 2518) ∨ (p 2331) ∨ (¬ p 2528) ∨ (¬ p 5284) ∨ (¬ p 3379) :=
  ElevenRUP.step111017 (p 2254) (p 2331) (p 2518) (p 2528) (p 3323) (p 3379) (p 3461) (p 4604) (p 5274) (p 5284) (derived105366 p h) (derived106293 p h) (derived81483 p h) (derived102539 p h)

theorem derived111022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 4181) ∨ (¬ p 3941) :=
  ElevenRUP.step111022 (p 3527) (p 3941) (p 4181) (p 5307) (h 34673) (derived96266 p h)

theorem derived111023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 3073) ∨ (¬ p 2459) :=
  ElevenRUP.step111023 (p 2459) (p 3073) (p 3527) (p 5307) (h 37012) (derived96266 p h)

theorem derived111026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3449) ∨ (p 3399) ∨ (p 2881) ∨ (¬ p 4914) :=
  ElevenRUP.step111026 (p 2881) (p 3399) (p 3449) (p 3527) (p 4914) (p 5307) (derived93370 p h) (derived96266 p h)

theorem derived111027 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3449) ∨ (p 3399) ∨ (p 2264) ∨ (¬ p 3040) :=
  ElevenRUP.step111027 (p 2264) (p 3040) (p 3399) (p 3449) (p 3527) (p 5307) (derived93373 p h) (derived96266 p h)

theorem derived111028 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4442) ∨ (p 3399) ∨ (¬ p 3449) :=
  ElevenRUP.step111028 (p 3399) (p 3449) (p 3527) (p 4442) (p 5307) (p 5559) (derived106189 p h) (derived93375 p h) (derived96266 p h)

theorem derived111029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 5074) ∨ (p 2911) ∨ (p 2807) ∨ (¬ p 3166) :=
  ElevenRUP.step111029 (p 2807) (p 2911) (p 3166) (p 3527) (p 5074) (p 5307) (derived107356 p h) (derived96266 p h)

theorem derived111030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3449) ∨ (p 3399) ∨ (p 3631) :=
  ElevenRUP.step111030 (p 3399) (p 3449) (p 3527) (p 3631) (p 4666) (p 5307) (derived105658 p h) (derived101978 p h) (derived96266 p h)

theorem derived111032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2707) ∨ (¬ p 3449) ∨ (p 3399) ∨ (p 2717) :=
  ElevenRUP.step111032 (p 2707) (p 2717) (p 3399) (p 3449) (p 3527) (p 5307) (derived108320 p h) (derived96266 p h)

theorem derived111033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3309) ∨ (p 2177) ∨ (p 3399) ∨ (¬ p 3449) :=
  ElevenRUP.step111033 (p 2177) (p 3309) (p 3399) (p 3449) (p 3527) (p 5307) (derived108656 p h) (derived96266 p h)

theorem derived111034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2922) ∨ (p 3399) ∨ (¬ p 3449) ∨ (p 2911) :=
  ElevenRUP.step111034 (p 2911) (p 2922) (p 3399) (p 3449) (p 3527) (p 5307) (derived108923 p h) (derived96266 p h)

theorem derived111036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4370) ∨ (¬ p 3083) ∨ (p 2437) ∨ (p 2177) :=
  ElevenRUP.step111036 (p 2177) (p 2437) (p 3083) (p 3527) (p 4370) (p 4712) (p 5307) (derived105422 p h) (derived75136 p h) (derived96266 p h)

theorem derived111037 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4370) ∨ (p 3389) ∨ (¬ p 2470) ∨ (p 2177) :=
  ElevenRUP.step111037 (p 2177) (p 2470) (p 3389) (p 3527) (p 4370) (p 4712) (p 5307) (derived105422 p h) (derived77503 p h) (derived96266 p h)

theorem derived111038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4370) ∨ (p 2881) ∨ (¬ p 2470) ∨ (p 3389) :=
  ElevenRUP.step111038 (p 2470) (p 2881) (p 3389) (p 3527) (p 4370) (p 4647) (p 5307) (derived105412 p h) (derived77523 p h) (derived96266 p h)

theorem derived111041 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 4391) ∨ (¬ p 3032) ∨ (p 3399) ∨ (¬ p 3449) :=
  ElevenRUP.step111041 (p 3032) (p 3399) (p 3449) (p 3527) (p 4391) (p 5307) (p 5559) (derived106189 p h) (derived97768 p h) (derived96266 p h)

theorem derived111042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3449) ∨ (p 3093) ∨ (p 3319) ∨ (¬ p 3990) :=
  ElevenRUP.step111042 (p 3093) (p 3319) (p 3449) (p 3527) (p 3990) (p 4503) (p 5307) (derived106530 p h) (derived102175 p h) (derived96266 p h)

theorem derived111048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 2819) ∨ (¬ p 2187) ∨ (p 2341) ∨ (¬ p 2284) ∨ (¬ p 2946) ∨ (p 3073) ∨ (¬ p 3609) ∨ (¬ p 5206) :=
  ElevenRUP.step111048 (p 2187) (p 2284) (p 2341) (p 2819) (p 2946) (p 3073) (p 3527) (p 3609) (p 5206) (p 5307) (derived108329 p h) (derived96266 p h)

theorem derived111052 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 4032) ∨ (p 3051) :=
  ElevenRUP.step111052 (p 3051) (p 3246) (p 4032) (p 4402) (derived82985 p h) (derived100360 p h)

theorem derived111053 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2901) ∨ (¬ p 3115) :=
  ElevenRUP.step111053 (p 2901) (p 3115) (p 3246) (p 4402) (derived82986 p h) (derived100360 p h)

theorem derived111054 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2870) ∨ (¬ p 3105) :=
  ElevenRUP.step111054 (p 2870) (p 3105) (p 3246) (p 4402) (derived82994 p h) (derived100360 p h)

theorem derived111056 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2891) ∨ (¬ p 2972) :=
  ElevenRUP.step111056 (p 2891) (p 2972) (p 3246) (p 4402) (derived92707 p h) (derived100360 p h)

theorem derived111057 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 3516) ∨ (¬ p 2761) ∨ (¬ p 4322) :=
  ElevenRUP.step111057 (p 2761) (p 3246) (p 3516) (p 4322) (p 4402) (derived68259 p h) (derived100360 p h)

theorem derived111058 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 3105) ∨ (p 3051) ∨ (¬ p 2143) :=
  ElevenRUP.step111058 (p 2143) (p 3051) (p 3105) (p 3246) (p 4402) (derived82990 p h) (derived100360 p h)

theorem derived111059 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4322) ∨ (p 2427) ∨ (p 2230) ∨ (¬ p 2761) :=
  ElevenRUP.step111059 (p 2230) (p 2427) (p 2761) (p 3246) (p 4322) (p 4402) (derived75836 p h) (derived100360 p h)

theorem derived111063 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2761) ∨ (¬ p 4322) ∨ (¬ p 2881) ∨ (¬ p 3434) :=
  ElevenRUP.step111063 (p 2761) (p 2881) (p 3246) (p 3434) (p 4322) (p 4402) (derived63918 p h) (derived100360 p h)

theorem derived111065 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 3631) ∨ (¬ p 3707) ∨ (¬ p 2396) ∨ (¬ p 4322) :=
  ElevenRUP.step111065 (p 2396) (p 3246) (p 3631) (p 3707) (p 4322) (p 4402) (derived110532 p h) (derived100360 p h)

theorem derived111067 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 3767) ∨ (¬ p 4322) ∨ (p 2427) ∨ (¬ p 4207) :=
  ElevenRUP.step111067 (p 2427) (p 3246) (p 3767) (p 4207) (p 4322) (p 4402) (p 4539) (derived105395 p h) (derived82993 p h) (derived100360 p h)

theorem derived111068 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 3564) ∨ (¬ p 3461) ∨ (¬ p 4322) ∨ (¬ p 4204) :=
  ElevenRUP.step111068 (p 3246) (p 3461) (p 3564) (p 4204) (p 4322) (p 4402) (p 4718) (derived105425 p h) (derived51681 p h) (derived100360 p h)

theorem derived111070 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4132) ∨ (p 2619) ∨ (¬ p 2177) ∨ (¬ p 3105) :=
  ElevenRUP.step111070 (p 2177) (p 2619) (p 3105) (p 3246) (p 4132) (p 4402) (p 4556) (derived105399 p h) (derived84774 p h) (derived100360 p h)

theorem derived111071 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 3516) ∨ (¬ p 3631) ∨ (¬ p 3767) ∨ (¬ p 4322) ∨ (¬ p 4914) :=
  ElevenRUP.step111071 (p 3246) (p 3516) (p 3631) (p 3767) (p 4322) (p 4402) (p 4914) (derived110107 p h) (derived100360 p h)

theorem derived111087 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 3166) ∨ (¬ p 3286) :=
  ElevenRUP.step111087 (p 3166) (p 3256) (p 3286) (p 4349) (derived93212 p h) (derived102494 p h)

theorem derived111089 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 3005) ∨ (¬ p 3755) :=
  ElevenRUP.step111089 (p 3005) (p 3256) (p 3755) (p 4349) (derived94943 p h) (derived102494 p h)

theorem derived111090 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3852) ∨ (p 3189) :=
  ElevenRUP.step111090 (p 3189) (p 3256) (p 3852) (p 4349) (derived110653 p h) (derived102494 p h)

theorem derived111091 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 4196) ∨ (¬ p 3286) ∨ (p 2331) :=
  ElevenRUP.step111091 (p 2331) (p 3256) (p 3286) (p 4196) (p 4349) (derived89467 p h) (derived102494 p h)

theorem derived111094 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 3166) ∨ (¬ p 2331) ∨ (¬ p 4421) :=
  ElevenRUP.step111094 (p 2331) (p 3166) (p 3256) (p 4349) (p 4421) (derived94563 p h) (derived102494 p h)

theorem derived111095 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 5284) ∨ (¬ p 3266) ∨ (¬ p 3146) :=
  ElevenRUP.step111095 (p 3146) (p 3256) (p 3266) (p 4349) (p 5063) (p 5284) (derived105474 p h) (derived50141 p h) (derived102494 p h)

theorem derived111102 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 4378) ∨ (¬ p 2996) ∨ (¬ p 3842) ∨ (p 2911) ∨ (¬ p 4653) :=
  ElevenRUP.step111102 (p 2911) (p 2996) (p 3256) (p 3842) (p 4349) (p 4378) (p 4653) (derived94371 p h) (derived102494 p h)

theorem derived111103 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3319) ∨ (¬ p 4417) ∨ (p 3309) ∨ (¬ p 3707) ∨ (¬ p 5284) :=
  ElevenRUP.step111103 (p 3256) (p 3309) (p 3319) (p 3707) (p 4349) (p 4417) (p 5284) (derived109542 p h) (derived102494 p h)

theorem derived111104 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 4422) ∨ (¬ p 5284) ∨ (¬ p 3276) ∨ (¬ p 4417) ∨ (p 2553) :=
  ElevenRUP.step111104 (p 2553) (p 3256) (p 3276) (p 4349) (p 4405) (p 4417) (p 4422) (p 5284) (derived105512 p h) (derived93292 p h) (derived102494 p h)

theorem derived111107 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3767) ∨ (¬ p 3691) ∨ (¬ p 5284) ∨ (¬ p 2427) ∨ (¬ p 3661) ∨ (¬ p 5300) :=
  ElevenRUP.step111107 (p 2427) (p 3256) (p 3661) (p 3691) (p 3767) (p 4349) (p 4702) (p 5284) (p 5300) (derived106079 p h) (derived54207 p h) (derived102494 p h)

theorem derived111116 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 3564) ∨ (¬ p 3266) ∨ (¬ p 3379) ∨ (¬ p 2493) ∨ (p 2220) ∨ (¬ p 5284) ∨ (¬ p 2950) ∨ (¬ p 4311) :=
  ElevenRUP.step111116 (p 2220) (p 2254) (p 2493) (p 2950) (p 3256) (p 3266) (p 3379) (p 3564) (p 4311) (p 4330) (p 4349) (p 5284) (derived105366 p h) (derived106329 p h) (derived94753 p h) (derived102494 p h)

theorem derived111121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 2528) ∨ (p 3609) :=
  ElevenRUP.step111121 (p 2528) (p 3609) (p 3641) (p 5373) (derived76783 p h) (derived96246 p h)

theorem derived111122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 4804) ∨ (¬ p 4404) :=
  ElevenRUP.step111122 (p 3641) (p 4404) (p 4804) (p 5373) (h 37608) (derived96246 p h)

theorem derived111124 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3537) ∨ (p 2470) ∨ (p 3367) :=
  ElevenRUP.step111124 (p 2470) (p 3367) (p 3537) (p 3641) (p 5373) (derived76790 p h) (derived96246 p h)

theorem derived111125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 3609) ∨ (¬ p 2475) ∨ (¬ p 2088) :=
  ElevenRUP.step111125 (p 2088) (p 2475) (p 3609) (p 3641) (p 5373) (derived89922 p h) (derived96246 p h)

theorem derived111127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3537) ∨ (¬ p 4610) ∨ (p 3367) ∨ (p 2850) :=
  ElevenRUP.step111127 (p 2850) (p 3367) (p 3537) (p 3641) (p 4610) (p 5373) (derived76779 p h) (derived96246 p h)

theorem derived111128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 2098) ∨ (¬ p 2509) ∨ (p 2598) :=
  ElevenRUP.step111128 (p 2098) (p 2509) (p 2598) (p 3641) (p 5214) (p 5373) (derived105492 p h) (derived76788 p h) (derived96246 p h)

theorem derived111132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3537) ∨ (¬ p 2528) ∨ (p 3367) ∨ (¬ p 2598) ∨ (¬ p 3589) :=
  ElevenRUP.step111132 (p 2528) (p 2598) (p 3367) (p 3537) (p 3589) (p 3641) (p 5373) (derived81797 p h) (derived96246 p h)

theorem derived111134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 2098) ∨ (p 2437) ∨ (p 2440) ∨ (p 2598) ∨ (¬ p 4186) :=
  ElevenRUP.step111134 (p 2098) (p 2437) (p 2440) (p 2598) (p 3641) (p 4186) (p 5373) (derived93146 p h) (derived96246 p h)

theorem derived111139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 2470) ∨ (¬ p 2459) ∨ (¬ p 2187) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (p 3609) :=
  ElevenRUP.step111139 (p 2187) (p 2192) (p 2210) (p 2459) (p 2470) (p 3609) (p 3641) (p 4133) (p 5193) (p 5373) (derived105488 p h) (derived105712 p h) (derived76773 p h) (derived96246 p h)

theorem derived111143 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3791) ∨ (p 3266) ∨ (p 2470) ∨ (p 3609) ∨ (¬ p 3905) ∨ (¬ p 2274) ∨ (¬ p 2156) ∨ (¬ p 2139) :=
  ElevenRUP.step111143 (p 2139) (p 2156) (p 2274) (p 2470) (p 3266) (p 3609) (p 3641) (p 3791) (p 3905) (p 4826) (p 5373) (derived105444 p h) (derived88012 p h) (derived96246 p h)

theorem derived111144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3115) ∨ (¬ p 5284) ∨ (¬ p 2528) ∨ (¬ p 2761) ∨ (¬ p 2098) ∨ (p 2972) ∨ (p 2598) ∨ (¬ p 2748) ∨ (¬ p 3368) :=
  ElevenRUP.step111144 (p 2098) (p 2528) (p 2598) (p 2748) (p 2761) (p 2972) (p 3115) (p 3368) (p 3641) (p 5284) (p 5373) (derived110869 p h) (derived96246 p h)

theorem derived111153 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2839) ∨ (p 3367) :=
  ElevenRUP.step111153 (p 2839) (p 2850) (p 3054) (p 3367) (derived81223 p h) (derived102320 p h)

theorem derived111154 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2132) ∨ (p 2598) :=
  ElevenRUP.step111154 (p 2132) (p 2598) (p 2850) (p 3054) (derived90719 p h) (derived102320 p h)

theorem derived111155 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2406) ∨ (¬ p 3698) ∨ (¬ p 3590) :=
  ElevenRUP.step111155 (p 2406) (p 2850) (p 3054) (p 3590) (p 3698) (h 29207) (derived102320 p h)

theorem derived111156 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 6116) ∨ (p 3717) ∨ (¬ p 2230) :=
  ElevenRUP.step111156 (p 2230) (p 2850) (p 3054) (p 3717) (p 6116) (derived110777 p h) (derived102320 p h)

theorem derived111158 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2192) ∨ (p 2870) ∨ (¬ p 2891) ∨ (¬ p 2563) :=
  ElevenRUP.step111158 (p 2192) (p 2563) (p 2850) (p 2870) (p 2891) (p 3054) (derived79966 p h) (derived102320 p h)

theorem derived111159 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2860) ∨ (¬ p 2230) ∨ (¬ p 2563) :=
  ElevenRUP.step111159 (p 2230) (p 2563) (p 2850) (p 2860) (p 3054) (p 4730) (derived106074 p h) (derived83201 p h) (derived102320 p h)

theorem derived111160 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 3105) ∨ (¬ p 2982) ∨ (¬ p 2230) :=
  ElevenRUP.step111160 (p 2230) (p 2850) (p 2982) (p 3054) (p 3105) (p 4730) (derived106074 p h) (derived84515 p h) (derived102320 p h)

theorem derived111161 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 3105) ∨ (¬ p 2982) ∨ (¬ p 3422) :=
  ElevenRUP.step111161 (p 2850) (p 2982) (p 3054) (p 3105) (p 3422) (p 4717) (derived105424 p h) (derived84551 p h) (derived102320 p h)

theorem derived111162 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2563) ∨ (¬ p 2373) ∨ (p 2619) ∨ (p 2274) :=
  ElevenRUP.step111162 (p 2274) (p 2373) (p 2563) (p 2619) (p 2850) (p 3054) (derived84694 p h) (derived102320 p h)

theorem derived111163 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2619) ∨ (¬ p 2373) ∨ (¬ p 2230) :=
  ElevenRUP.step111163 (p 2230) (p 2373) (p 2619) (p 2850) (p 3054) (p 4730) (derived106074 p h) (derived84764 p h) (derived102320 p h)

theorem derived111165 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2870) ∨ (¬ p 3422) ∨ (¬ p 2427) :=
  ElevenRUP.step111165 (p 2427) (p 2850) (p 2870) (p 3054) (p 3422) (p 4717) (derived105424 p h) (derived86817 p h) (derived102320 p h)

theorem derived111166 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2509) ∨ (p 2870) ∨ (¬ p 2901) ∨ (¬ p 3641) ∨ (¬ p 3402) :=
  ElevenRUP.step111166 (p 2509) (p 2850) (p 2870) (p 2901) (p 3054) (p 3402) (p 3641) (derived77403 p h) (derived102320 p h)

theorem derived111167 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2192) ∨ (¬ p 2230) ∨ (¬ p 2563) ∨ (¬ p 4243) :=
  ElevenRUP.step111167 (p 2192) (p 2230) (p 2563) (p 2850) (p 3054) (p 4243) (p 4730) (derived106074 p h) (derived79918 p h) (derived102320 p h)

theorem derived111170 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2156) ∨ (p 2860) ∨ (p 2440) ∨ (¬ p 4109) :=
  ElevenRUP.step111170 (p 2156) (p 2440) (p 2850) (p 2860) (p 3054) (p 4109) (p 4750) (derived105433 p h) (derived92424 p h) (derived102320 p h)

theorem derived111181 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 4075) ∨ (¬ p 4260) ∨ (¬ p 2396) ∨ (¬ p 3399) ∨ (¬ p 2563) ∨ (p 2651) ∨ (¬ p 3683) ∨ (p 2860) :=
  ElevenRUP.step111181 (p 2254) (p 2396) (p 2563) (p 2651) (p 2850) (p 2860) (p 3054) (p 3399) (p 3683) (p 4075) (p 4260) (derived105366 p h) (derived83356 p h) (derived102320 p h)

theorem derived111187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3449) ∨ (¬ p 2210) :=
  ElevenRUP.step111187 (p 2166) (p 2210) (p 3449) (p 4496) (derived80538 p h) (derived102268 p h)

theorem derived111188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 5312) :=
  ElevenRUP.step111188 (p 2166) (p 4377) (p 4496) (p 5312) (derived106170 p h) (h 38829) (derived102268 p h)

theorem derived111194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3073) ∨ (p 3830) ∨ (¬ p 2210) :=
  ElevenRUP.step111194 (p 2166) (p 2210) (p 3073) (p 3830) (p 4496) (derived110471 p h) (derived102268 p h)

theorem derived111195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2373) ∨ (p 3146) ∨ (¬ p 3073) :=
  ElevenRUP.step111195 (p 2166) (p 2373) (p 3073) (p 3146) (p 4496) (p 4632) (derived106257 p h) (derived78970 p h) (derived102268 p h)

theorem derived111196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3146) ∨ (¬ p 3073) ∨ (p 2192) :=
  ElevenRUP.step111196 (p 2166) (p 2192) (p 3073) (p 3146) (p 4496) (p 4509) (derived105392 p h) (derived80010 p h) (derived102268 p h)

theorem derived111197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3146) ∨ (p 3156) ∨ (¬ p 3073) :=
  ElevenRUP.step111197 (p 2166) (p 3073) (p 3146) (p 3156) (p 4496) (p 4960) (derived106209 p h) (derived80173 p h) (derived102268 p h)

theorem derived111204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3146) ∨ (¬ p 3073) ∨ (¬ p 4119) ∨ (p 2901) :=
  ElevenRUP.step111204 (p 2166) (p 2901) (p 3073) (p 3146) (p 4119) (p 4496) (p 4960) (derived106209 p h) (derived80134 p h) (derived102268 p h)

theorem derived111205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2427) ∨ (p 3146) ∨ (¬ p 4034) ∨ (¬ p 3073) ∨ (¬ p 4904) :=
  ElevenRUP.step111205 (p 2166) (p 2427) (p 3073) (p 3146) (p 4034) (p 4496) (p 4904) (derived80156 p h) (derived102268 p h)

theorem derived111211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3073) ∨ (¬ p 4078) ∨ (¬ p 4185) ∨ (p 3609) ∨ (p 2891) :=
  ElevenRUP.step111211 (p 2166) (p 2891) (p 3073) (p 3609) (p 4078) (p 4185) (p 4496) (p 4555) (derived105542 p h) (derived91611 p h) (derived102268 p h)

theorem derived111212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 4283) ∨ (¬ p 3073) ∨ (p 2088) ∨ (p 2192) ∨ (¬ p 3961) :=
  ElevenRUP.step111212 (p 2088) (p 2166) (p 2192) (p 3073) (p 3961) (p 4283) (p 4496) (p 4558) (derived105400 p h) (derived93558 p h) (derived102268 p h)

theorem derived111215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2911) ∨ (p 2598) ∨ (p 3146) ∨ (p 3201) ∨ (¬ p 3073) ∨ (¬ p 2210) :=
  ElevenRUP.step111215 (p 2166) (p 2210) (p 2598) (p 2911) (p 3073) (p 3146) (p 3201) (p 4496) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived80230 p h) (derived102268 p h)

theorem derived111216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2668) ∨ (¬ p 3073) ∨ (p 3146) ∨ (¬ p 4418) ∨ (¬ p 2132) ∨ (¬ p 3361) ∨ (p 2737) ∨ (p 2331) :=
  ElevenRUP.step111216 (p 2132) (p 2166) (p 2331) (p 2668) (p 2737) (p 3073) (p 3146) (p 3361) (p 4418) (p 4433) (p 4496) (derived106150 p h) (derived80229 p h) (derived102268 p h)

theorem derived111221 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 4697) ∨ (¬ p 5059) :=
  ElevenRUP.step111221 (p 2982) (p 4697) (p 4947) (p 5059) (h 27229) (derived96342 p h)

theorem derived111224 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 3343) ∨ (¬ p 4322) ∨ (p 2230) ∨ (p 2440) :=
  ElevenRUP.step111224 (p 2230) (p 2440) (p 2982) (p 3343) (p 4322) (p 4947) (derived74543 p h) (derived96342 p h)

theorem derived111226 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 3343) ∨ (p 2440) ∨ (¬ p 2563) :=
  ElevenRUP.step111226 (p 2440) (p 2563) (p 2982) (p 3343) (p 4947) (p 5043) (derived105471 p h) (derived89551 p h) (derived96342 p h)

theorem derived111230 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (¬ p 3115) ∨ (¬ p 3346) ∨ (¬ p 2230) :=
  ElevenRUP.step111230 (p 2230) (p 2982) (p 3115) (p 3346) (p 4705) (p 4947) (derived106238 p h) (derived41921 p h) (derived96342 p h)

theorem derived111232 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 2761) ∨ (¬ p 4260) ∨ (¬ p 3276) ∨ (¬ p 2396) :=
  ElevenRUP.step111232 (p 2396) (p 2761) (p 2982) (p 3276) (p 4260) (p 4947) (derived108964 p h) (derived96342 p h)

theorem derived111236 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (p 2363) ∨ (¬ p 4695) ∨ (¬ p 3115) ∨ (p 3156) :=
  ElevenRUP.step111236 (p 2363) (p 2982) (p 3115) (p 3156) (p 4134) (p 4695) (p 4947) (derived105379 p h) (derived95992 p h) (derived96342 p h)

theorem derived111247 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (¬ p 3609) ∨ (¬ p 3537) ∨ (p 2440) ∨ (¬ p 2608) ∨ (p 2230) ∨ (p 3343) ∨ (¬ p 2655) ∨ (¬ p 5059) :=
  ElevenRUP.step111247 (p 2230) (p 2254) (p 2440) (p 2608) (p 2655) (p 2982) (p 3343) (p 3537) (p 3609) (p 4947) (p 5059) (derived105366 p h) (derived75042 p h) (derived96342 p h)

theorem derived111255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3276) ∨ (¬ p 5284) :=
  ElevenRUP.step111255 (p 3276) (p 3343) (p 5175) (p 5284) (derived107915 p h) (derived102651 p h)

theorem derived111256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3193) ∨ (¬ p 3487) ∨ (¬ p 5176) :=
  ElevenRUP.step111256 (p 3193) (p 3343) (p 3487) (p 5175) (p 5176) (h 16652) (derived102651 p h)

theorem derived111257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3842) ∨ (p 2727) ∨ (¬ p 4953) ∨ (¬ p 2440) :=
  ElevenRUP.step111257 (p 2440) (p 2727) (p 3343) (p 3842) (p 4953) (p 5175) (derived94393 p h) (derived102651 p h)

theorem derived111260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3755) ∨ (¬ p 3193) ∨ (p 3136) ∨ (¬ p 2493) :=
  ElevenRUP.step111260 (p 2493) (p 3136) (p 3193) (p 3343) (p 3755) (p 5175) (derived95023 p h) (derived102651 p h)

theorem derived111262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 5107) ∨ (¬ p 5160) ∨ (¬ p 3641) ∨ (¬ p 3146) :=
  ElevenRUP.step111262 (p 3146) (p 3343) (p 3641) (p 4158) (p 5107) (p 5160) (p 5175) (derived106187 p h) (derived55160 p h) (derived102651 p h)

theorem derived111270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 4421) ∨ (¬ p 3276) ∨ (p 3461) ∨ (p 2651) ∨ (¬ p 2331) :=
  ElevenRUP.step111270 (p 2331) (p 2651) (p 3276) (p 3343) (p 3461) (p 4421) (p 5175) (derived98157 p h) (derived102651 p h)

theorem derived111272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (p 3193) ∨ (¬ p 3707) ∨ (¬ p 5284) ∨ (¬ p 4953) ∨ (p 2406) :=
  ElevenRUP.step111272 (p 2406) (p 3193) (p 3343) (p 3707) (p 4953) (p 5175) (p 5284) (derived109389 p h) (derived102651 p h)

theorem derived111273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (p 2982) ∨ (¬ p 3286) ∨ (¬ p 2630) ∨ (p 2651) ∨ (¬ p 2563) :=
  ElevenRUP.step111273 (p 2563) (p 2630) (p 2651) (p 2982) (p 3286) (p 3343) (p 5175) (derived109970 p h) (derived102651 p h)

theorem derived111286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (p 2996) ∨ (¬ p 4623) ∨ (¬ p 3266) ∨ (p 2651) ∨ (¬ p 2727) ∨ (p 3461) ∨ (¬ p 3286) ∨ (p 3631) ∨ (¬ p 4952) ∨ (¬ p 4450) :=
  ElevenRUP.step111286 (p 2651) (p 2727) (p 2996) (p 3266) (p 3286) (p 3343) (p 3461) (p 3631) (p 4450) (p 4623) (p 4952) (p 5175) (derived107836 p h) (derived102651 p h)

theorem derived111287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3755) ∨ (¬ p 3645) ∨ (p 2156) ∨ (p 2630) ∨ (p 2396) ∨ (p 2274) ∨ (¬ p 2651) ∨ (¬ p 2246) ∨ (¬ p 2749) :=
  ElevenRUP.step111287 (p 2156) (p 2246) (p 2274) (p 2396) (p 2630) (p 2651) (p 2749) (p 3343) (p 3645) (p 3755) (p 4638) (p 4877) (p 5175) (derived105451 p h) (derived105409 p h) (derived94993 p h) (derived102651 p h)

theorem derived111289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3193) ∨ (¬ p 3487) :=
  ElevenRUP.step111289 (p 3193) (p 3343) (p 3487) (p 5176) (derived111256 p h) (derived102376 p h)

theorem derived111292 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (p 4053) :=
  ElevenRUP.step111292 (p 4053) (p 4435) (p 6164) (h 14706) (derived108107 p h)

theorem derived111297 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 4393) ∨ (¬ p 3093) ∨ (¬ p 2274) :=
  ElevenRUP.step111297 (p 2274) (p 3093) (p 4053) (p 4393) (p 4435) (derived43431 p h) (derived111292 p h)

theorem derived111299 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (p 4228) ∨ (¬ p 4759) ∨ (p 2797) :=
  ElevenRUP.step111299 (p 2797) (p 4053) (p 4228) (p 4435) (p 4759) (derived110221 p h) (derived111292 p h)

theorem derived111300 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 4393) ∨ (p 2860) ∨ (¬ p 4338) :=
  ElevenRUP.step111300 (p 2860) (p 4053) (p 4338) (p 4393) (p 4435) (p 4878) (derived105452 p h) (derived96127 p h) (derived111292 p h)

theorem derived111302 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 4329) ∨ (¬ p 4193) ∨ (¬ p 3093) ∨ (¬ p 2619) :=
  ElevenRUP.step111302 (p 2619) (p 3093) (p 4053) (p 4193) (p 4329) (p 4435) (derived46922 p h) (derived111292 p h)

theorem derived111303 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 5477) ∨ (p 3399) ∨ (¬ p 4427) ∨ (¬ p 3093) :=
  ElevenRUP.step111303 (p 3093) (p 3399) (p 4053) (p 4427) (p 4435) (p 5477) (derived100636 p h) (derived111292 p h)

theorem derived111306 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 5514) ∨ (¬ p 2505) ∨ (p 2406) :=
  ElevenRUP.step111306 (p 2406) (p 2505) (p 4053) (p 4435) (p 4717) (p 5514) (derived105424 p h) (derived102502 p h) (derived111292 p h)

theorem derived111308 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 5477) ∨ (¬ p 3325) ∨ (¬ p 2363) ∨ (p 3073) ∨ (¬ p 4371) :=
  ElevenRUP.step111308 (p 2363) (p 3073) (p 3325) (p 4053) (p 4371) (p 4435) (p 5477) (derived96548 p h) (derived111292 p h)

theorem derived111312 (p : Nat → Prop) (h : Inputs p) :
    (p 4435) ∨ (¬ p 5514) ∨ (¬ p 3019) ∨ (¬ p 4337) ∨ (¬ p 3918) ∨ (¬ p 2440) :=
  ElevenRUP.step111312 (p 2440) (p 3019) (p 3918) (p 4053) (p 4337) (p 4435) (p 4717) (p 5514) (derived105424 p h) (derived61181 p h) (derived111292 p h)

theorem derived111318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5092) ∨ (¬ p 6008) ∨ (¬ p 4209) ∨ (¬ p 3212) :=
  ElevenRUP.step111318 (p 3212) (p 4207) (p 4209) (p 5092) (p 6008) (derived108401 p h) (h 8576)

theorem derived111319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2707) ∨ (¬ p 2829) :=
  ElevenRUP.step111319 (p 2122) (p 2707) (p 2829) (p 3426) (derived88279 p h) (derived96484 p h)

theorem derived111320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3425) ∨ (¬ p 2774) :=
  ElevenRUP.step111320 (p 2122) (p 2774) (p 3425) (p 3426) (h 4943) (derived96484 p h)

theorem derived111321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3587) ∨ (¬ p 3985) :=
  ElevenRUP.step111321 (p 2122) (p 3426) (p 3587) (p 3985) (h 37269) (derived96484 p h)

theorem derived111322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 4781) ∨ (¬ p 4426) :=
  ElevenRUP.step111322 (p 2122) (p 3426) (p 4426) (p 4781) (h 19546) (derived96484 p h)

theorem derived111323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3434) ∨ (p 2819) ∨ (p 2396) :=
  ElevenRUP.step111323 (p 2122) (p 2396) (p 2819) (p 3426) (p 3434) (derived89628 p h) (derived96484 p h)

theorem derived111324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 4253) ∨ (¬ p 4260) ∨ (p 2295) :=
  ElevenRUP.step111324 (p 2122) (p 2295) (p 3426) (p 4253) (p 4260) (derived107196 p h) (derived96484 p h)

theorem derived111326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (p 2177) ∨ (p 2307) ∨ (¬ p 2782) :=
  ElevenRUP.step111326 (p 2122) (p 2177) (p 2307) (p 2717) (p 2782) (p 3426) (derived89191 p h) (derived96484 p h)

theorem derived111327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (¬ p 2829) ∨ (¬ p 2608) ∨ (p 2177) :=
  ElevenRUP.step111327 (p 2122) (p 2177) (p 2608) (p 2717) (p 2829) (p 3426) (derived89193 p h) (derived96484 p h)

theorem derived111328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (¬ p 3917) ∨ (p 2177) ∨ (¬ p 3654) :=
  ElevenRUP.step111328 (p 2122) (p 2177) (p 2717) (p 3426) (p 3654) (p 3917) (derived89198 p h) (derived96484 p h)

theorem derived111329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (¬ p 3917) ∨ (p 2881) ∨ (¬ p 3323) :=
  ElevenRUP.step111329 (p 2122) (p 2717) (p 2881) (p 3323) (p 3426) (p 3917) (derived89215 p h) (derived96484 p h)

theorem derived111332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3425) ∨ (¬ p 2132) ∨ (¬ p 4428) ∨ (¬ p 2284) :=
  ElevenRUP.step111332 (p 2122) (p 2132) (p 2284) (p 3425) (p 3426) (p 4428) (p 4906) (derived105632 p h) (derived62414 p h) (derived96484 p h)

theorem derived111334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (p 2341) ∨ (p 3309) ∨ (¬ p 2318) :=
  ElevenRUP.step111334 (p 2122) (p 2318) (p 2341) (p 2717) (p 3309) (p 3426) (p 4867) (derived106410 p h) (derived89225 p h) (derived96484 p h)

theorem derived111337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3631) ∨ (p 3389) ∨ (¬ p 2933) ∨ (¬ p 4375) ∨ (¬ p 3434) :=
  ElevenRUP.step111337 (p 2122) (p 2933) (p 3389) (p 3426) (p 3434) (p 3631) (p 4375) (derived95733 p h) (derived96484 p h)

theorem derived111341 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (p 2341) ∨ (¬ p 4401) ∨ (p 2274) ∨ (¬ p 3552) ∨ (¬ p 4155) :=
  ElevenRUP.step111341 (p 2122) (p 2274) (p 2341) (p 2717) (p 3426) (p 3552) (p 4155) (p 4401) (derived89226 p h) (derived96484 p h)

theorem derived111342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3434) ∨ (¬ p 4428) ∨ (p 2417) ∨ (¬ p 2441) ∨ (¬ p 2373) :=
  ElevenRUP.step111342 (p 2122) (p 2373) (p 2417) (p 2441) (p 3426) (p 3434) (p 4428) (p 4509) (derived105392 p h) (derived89575 p h) (derived96484 p h)

theorem derived111343 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3434) ∨ (¬ p 4428) ∨ (¬ p 3156) ∨ (p 2449) ∨ (¬ p 4386) :=
  ElevenRUP.step111343 (p 2122) (p 2449) (p 3156) (p 3426) (p 3434) (p 4386) (p 4428) (p 4509) (derived105392 p h) (derived91249 p h) (derived96484 p h)

theorem derived111345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2717) ∨ (p 3527) ∨ (¬ p 2318) ∨ (¬ p 3543) ∨ (p 2553) :=
  ElevenRUP.step111345 (p 2122) (p 2318) (p 2553) (p 2717) (p 3426) (p 3527) (p 3543) (p 5225) (derived105495 p h) (derived95699 p h) (derived96484 p h)

theorem derived111351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (p 2427) ∨ (p 3367) ∨ (p 2177) ∨ (p 2850) ∨ (¬ p 3527) ∨ (¬ p 4424) :=
  ElevenRUP.step111351 (p 2122) (p 2177) (p 2427) (p 2774) (p 2850) (p 3367) (p 3426) (p 3527) (p 4424) (p 4559) (derived105701 p h) (derived93504 p h) (derived96484 p h)

theorem derived111352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3564) ∨ (¬ p 2717) ∨ (¬ p 2192) ∨ (p 2341) ∨ (¬ p 2274) ∨ (¬ p 2210) ∨ (¬ p 4342) ∨ (¬ p 4620) ∨ (¬ p 5210) :=
  ElevenRUP.step111352 (p 2122) (p 2192) (p 2210) (p 2274) (p 2341) (p 2717) (p 3426) (p 3564) (p 4342) (p 4620) (p 5210) (derived89258 p h) (derived96484 p h)

theorem derived111356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 3609) ∨ (¬ p 3256) :=
  ElevenRUP.step111356 (p 3005) (p 3256) (p 3609) (p 4967) (derived95182 p h) (derived95976 p h)

theorem derived111358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3537) ∨ (p 4288) :=
  ElevenRUP.step111358 (p 3005) (p 3537) (p 4288) (p 4967) (derived109685 p h) (derived95976 p h)

theorem derived111360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 3166) ∨ (¬ p 4236) ∨ (¬ p 2098) :=
  ElevenRUP.step111360 (p 2098) (p 3005) (p 3166) (p 4236) (p 4967) (derived95174 p h) (derived95976 p h)

theorem derived111362 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (p 2696) ∨ (¬ p 2098) :=
  ElevenRUP.step111362 (p 2098) (p 2696) (p 3005) (p 3256) (p 3266) (p 4967) (derived82895 p h) (derived95976 p h)

theorem derived111363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 3146) ∨ (¬ p 3256) ∨ (p 2696) ∨ (¬ p 2098) :=
  ElevenRUP.step111363 (p 2098) (p 2696) (p 3005) (p 3146) (p 3256) (p 4967) (derived82897 p h) (derived95976 p h)

theorem derived111366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3537) ∨ (p 2630) ∨ (p 2737) ∨ (¬ p 5011) :=
  ElevenRUP.step111366 (p 2630) (p 2737) (p 3005) (p 3537) (p 4967) (p 5011) (derived89795 p h) (derived95976 p h)

theorem derived111367 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3537) ∨ (¬ p 5590) ∨ (p 5600) ∨ (¬ p 3858) :=
  ElevenRUP.step111367 (p 3005) (p 3537) (p 3858) (p 4967) (p 5590) (p 5600) (derived109692 p h) (derived95976 p h)

theorem derived111370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3537) ∨ (¬ p 2245) ∨ (p 3166) ∨ (p 2737) ∨ (p 2630) :=
  ElevenRUP.step111370 (p 2245) (p 2630) (p 2737) (p 3005) (p 3166) (p 3537) (p 4967) (derived95173 p h) (derived95976 p h)

theorem derived111371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3537) ∨ (¬ p 3256) ∨ (p 2737) ∨ (¬ p 2696) ∨ (¬ p 3589) :=
  ElevenRUP.step111371 (p 2696) (p 2737) (p 3005) (p 3256) (p 3537) (p 3589) (p 4967) (derived95181 p h) (derived95976 p h)

theorem derived111375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 5564) ∨ (¬ p 4383) ∨ (¬ p 3931) ∨ (¬ p 3919) ∨ (¬ p 2528) ∨ (p 3609) :=
  ElevenRUP.step111375 (p 2528) (p 3005) (p 3609) (p 3919) (p 3931) (p 4383) (p 4967) (p 5564) (derived93657 p h) (derived95976 p h)

theorem derived111377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3564) ∨ (p 2553) ∨ (¬ p 2295) ∨ (¬ p 2797) ∨ (p 3189) ∨ (p 2241) ∨ (p 3609) :=
  ElevenRUP.step111377 (p 2241) (p 2295) (p 2553) (p 2797) (p 3005) (p 3189) (p 3564) (p 3609) (p 4330) (p 4967) (derived106329 p h) (derived79417 p h) (derived95976 p h)

theorem derived111387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (p 3166) ∨ (p 3609) ∨ (p 3266) ∨ (¬ p 4236) ∨ (¬ p 4075) ∨ (p 3379) :=
  ElevenRUP.step111387 (p 3005) (p 3166) (p 3266) (p 3366) (p 3379) (p 3399) (p 3609) (p 4075) (p 4236) (p 4376) (p 4826) (p 4967) (derived106320 p h) (derived105444 p h) (derived101613 p h) (derived95976 p h)

theorem derived111390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3256) ∨ (p 2982) ∨ (¬ p 2563) ∨ (p 2696) ∨ (p 2156) ∨ (¬ p 3366) ∨ (¬ p 3537) ∨ (¬ p 3645) ∨ (¬ p 4030) ∨ (¬ p 4202) ∨ (¬ p 5059) :=
  ElevenRUP.step111390 (p 2156) (p 2563) (p 2696) (p 2982) (p 3005) (p 3256) (p 3366) (p 3537) (p 3645) (p 4030) (p 4202) (p 4752) (p 4967) (p 5059) (derived105434 p h) (derived85649 p h) (derived95976 p h)

theorem derived111391 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 3425) ∨ (p 2598) :=
  ElevenRUP.step111391 (p 2598) (p 3201) (p 3425) (p 3686) (derived88882 p h) (derived101932 p h)

theorem derived111393 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 4782) :=
  ElevenRUP.step111393 (p 3201) (p 3686) (p 4752) (p 4782) (derived105434 p h) (h 31255) (derived101932 p h)

theorem derived111394 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2922) ∨ (¬ p 4106) ∨ (¬ p 3590) :=
  ElevenRUP.step111394 (p 2922) (p 3201) (p 3590) (p 3686) (p 4106) (h 19124) (derived101932 p h)

theorem derived111395 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3576) ∨ (p 3367) ∨ (¬ p 3687) :=
  ElevenRUP.step111395 (p 3201) (p 3367) (p 3576) (p 3686) (p 3687) (derived88086 p h) (derived101932 p h)

theorem derived111396 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 3425) ∨ (¬ p 2753) ∨ (p 3367) :=
  ElevenRUP.step111396 (p 2753) (p 3201) (p 3367) (p 3425) (p 3686) (derived88889 p h) (derived101932 p h)

theorem derived111398 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2717) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 3422) :=
  ElevenRUP.step111398 (p 2264) (p 2717) (p 2807) (p 3201) (p 3422) (p 3686) (derived88880 p h) (derived101932 p h)

theorem derived111399 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2417) ∨ (p 3434) ∨ (¬ p 2850) :=
  ElevenRUP.step111399 (p 2417) (p 2850) (p 3201) (p 3434) (p 3686) (p 4644) (derived105411 p h) (derived88891 p h) (derived101932 p h)

theorem derived111400 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2717) ∨ (¬ p 2911) ∨ (¬ p 2437) :=
  ElevenRUP.step111400 (p 2437) (p 2717) (p 2911) (p 3201) (p 3686) (p 4750) (derived105433 p h) (derived97041 p h) (derived101932 p h)

theorem derived111401 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 3434) ∨ (¬ p 2437) ∨ (¬ p 2417) :=
  ElevenRUP.step111401 (p 2417) (p 2437) (p 3201) (p 3434) (p 3686) (p 4750) (derived105433 p h) (derived98033 p h) (derived101932 p h)

theorem derived111403 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3527) ∨ (¬ p 3389) ∨ (p 2717) ∨ (¬ p 2927) :=
  ElevenRUP.step111403 (p 2717) (p 2927) (p 3201) (p 3389) (p 3527) (p 3686) (p 4730) (derived106074 p h) (derived85135 p h) (derived101932 p h)

theorem derived111404 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3575) ∨ (p 2717) ∨ (¬ p 2341) ∨ (¬ p 2922) :=
  ElevenRUP.step111404 (p 2341) (p 2717) (p 2922) (p 3201) (p 3575) (p 3686) (p 5217) (derived105493 p h) (derived88888 p h) (derived101932 p h)

theorem derived111406 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2264) ∨ (p 2996) ∨ (p 2717) ∨ (¬ p 3364) :=
  ElevenRUP.step111406 (p 2264) (p 2717) (p 2751) (p 2996) (p 3201) (p 3364) (p 3686) (derived106343 p h) (derived97089 p h) (derived101932 p h)

theorem derived111409 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3516) ∨ (¬ p 2927) ∨ (p 3434) ∨ (¬ p 2850) ∨ (¬ p 3543) :=
  ElevenRUP.step111409 (p 2850) (p 2927) (p 3201) (p 3434) (p 3516) (p 3543) (p 3686) (p 4644) (derived105411 p h) (derived87841 p h) (derived101932 p h)

theorem derived111417 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 4781) ∨ (p 2528) ∨ (¬ p 3422) ∨ (¬ p 2509) ∨ (p 2651) ∨ (¬ p 3487) ∨ (¬ p 3361) :=
  ElevenRUP.step111417 (p 2509) (p 2528) (p 2651) (p 3201) (p 3361) (p 3422) (p 3487) (p 3686) (p 4781) (derived88524 p h) (derived101932 p h)

theorem derived111421 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2911) ∨ (p 2598) ∨ (p 2717) ∨ (¬ p 2274) :=
  ElevenRUP.step111421 (p 2192) (p 2210) (p 2274) (p 2598) (p 2717) (p 2911) (p 3201) (p 3686) (p 4712) (p 4736) (derived105431 p h) (derived105422 p h) (derived81022 p h) (derived101932 p h)

theorem derived111423 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 4423) ∨ (p 3461) ∨ (¬ p 3868) ∨ (p 3323) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (p 2331) ∨ (¬ p 3389) :=
  ElevenRUP.step111423 (p 2331) (p 3201) (p 3323) (p 3333) (p 3362) (p 3389) (p 3461) (p 3686) (p 3868) (p 4423) (p 4789) (derived105646 p h) (derived75071 p h) (derived101932 p h)

theorem derived111426 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 4435) ∨ (p 4325) ∨ (p 2996) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3922) ∨ (¬ p 3737) ∨ (p 2274) ∨ (p 2331) :=
  ElevenRUP.step111426 (p 2249) (p 2274) (p 2331) (p 2996) (p 3201) (p 3276) (p 3333) (p 3686) (p 3737) (p 3922) (p 4325) (p 4435) (derived106513 p h) (derived96713 p h) (derived101932 p h)

theorem derived111428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 2192) ∨ (p 2972) :=
  ElevenRUP.step111428 (p 2192) (p 2972) (p 3125) (p 4334) (h 17454) (derived96319 p h)

theorem derived111429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 4032) ∨ (¬ p 2156) :=
  ElevenRUP.step111429 (p 2156) (p 3125) (p 4032) (p 4334) (h 20722) (derived96319 p h)

theorem derived111430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3105) ∨ (¬ p 2860) :=
  ElevenRUP.step111430 (p 2860) (p 3105) (p 3125) (p 4334) (derived84498 p h) (derived96319 p h)

theorem derived111431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2982) ∨ (¬ p 2563) :=
  ElevenRUP.step111431 (p 2563) (p 2982) (p 3125) (p 4334) (derived92060 p h) (derived96319 p h)

theorem derived111432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3115) ∨ (¬ p 2284) :=
  ElevenRUP.step111432 (p 2284) (p 3115) (p 3125) (p 4334) (derived93027 p h) (derived96319 p h)

theorem derived111433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2972) ∨ (¬ p 3370) ∨ (¬ p 2156) :=
  ElevenRUP.step111433 (p 2156) (p 2972) (p 3125) (p 3370) (p 4334) (h 37562) (derived96319 p h)

theorem derived111441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2274) ∨ (¬ p 3680) ∨ (p 3461) :=
  ElevenRUP.step111441 (p 2274) (p 3125) (p 3461) (p 3680) (p 4334) (p 4624) (derived105408 p h) (derived82511 p h) (derived96319 p h)

theorem derived111442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3461) ∨ (¬ p 3680) ∨ (p 3564) :=
  ElevenRUP.step111442 (p 3125) (p 3461) (p 3564) (p 3680) (p 3958) (p 4334) (derived105378 p h) (derived82512 p h) (derived96319 p h)

theorem derived111446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 2982) ∨ (¬ p 3680) ∨ (p 3276) ∨ (¬ p 2427) :=
  ElevenRUP.step111446 (p 2427) (p 2982) (p 3125) (p 3276) (p 3680) (p 4334) (derived109967 p h) (derived96319 p h)

theorem derived111447 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 3322) ∨ (p 3461) ∨ (¬ p 3680) ∨ (¬ p 2946) ∨ (¬ p 2284) :=
  ElevenRUP.step111447 (p 2284) (p 2946) (p 3125) (p 3322) (p 3461) (p 3680) (p 4334) (derived82513 p h) (derived96319 p h)

theorem derived111460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 3680) ∨ (p 2707) ∨ (¬ p 2156) ∨ (¬ p 4521) ∨ (p 3461) ∨ (p 2417) ∨ (¬ p 4106) ∨ (p 2608) :=
  ElevenRUP.step111460 (p 2156) (p 2417) (p 2608) (p 2707) (p 3125) (p 3461) (p 3680) (p 4106) (p 4334) (p 4521) (p 4621) (derived105407 p h) (derived93103 p h) (derived96319 p h)

theorem derived111465 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2098) ∨ (p 2598) :=
  ElevenRUP.step111465 (p 2098) (p 2598) (p 3641) (p 5368) (derived77783 p h) (derived97919 p h)

theorem derived111468 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (p 3609) :=
  ElevenRUP.step111468 (p 2470) (p 2528) (p 3609) (p 3641) (p 4730) (p 5368) (derived106074 p h) (derived77792 p h) (derived97919 p h)

theorem derived111469 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 3193) ∨ (p 3609) ∨ (¬ p 3590) ∨ (¬ p 4695) :=
  ElevenRUP.step111469 (p 3193) (p 3590) (p 3609) (p 3641) (p 4695) (p 5368) (derived77793 p h) (derived97919 p h)

theorem derived111472 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2510) ∨ (p 2553) ∨ (¬ p 2528) ∨ (p 3609) ∨ (p 3367) :=
  ElevenRUP.step111472 (p 2510) (p 2528) (p 2553) (p 3367) (p 3609) (p 3641) (p 5368) (derived75601 p h) (derived97919 p h)

theorem derived111473 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 2573) ∨ (¬ p 3422) ∨ (¬ p 3905) ∨ (¬ p 2528) ∨ (p 3609) :=
  ElevenRUP.step111473 (p 2528) (p 2573) (p 3422) (p 3609) (p 3641) (p 3905) (p 5368) (derived77787 p h) (derived97919 p h)

theorem derived111476 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 3609) ∨ (¬ p 2088) ∨ (¬ p 2475) ∨ (¬ p 3083) :=
  ElevenRUP.step111476 (p 2088) (p 2475) (p 3083) (p 3609) (p 3641) (p 4750) (p 5368) (derived105433 p h) (derived90092 p h) (derived97919 p h)

theorem derived111477 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 4355) ∨ (p 3609) ∨ (¬ p 2528) ∨ (p 2440) :=
  ElevenRUP.step111477 (p 2440) (p 2528) (p 3609) (p 3641) (p 4355) (p 4750) (p 5368) (derived105433 p h) (derived97098 p h) (derived97919 p h)

theorem derived111491 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2187) ∨ (p 3609) ∨ (p 2598) ∨ (¬ p 2528) ∨ (¬ p 2307) ∨ (p 2274) ∨ (¬ p 2781) :=
  ElevenRUP.step111491 (p 2187) (p 2274) (p 2307) (p 2528) (p 2598) (p 2781) (p 3609) (p 3641) (p 4384) (p 5368) (derived106167 p h) (derived96916 p h) (derived97919 p h)

theorem derived111492 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2881) ∨ (p 3609) ∨ (p 2598) ∨ (¬ p 2528) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 4438) :=
  ElevenRUP.step111492 (p 2210) (p 2528) (p 2598) (p 2881) (p 2891) (p 3609) (p 3641) (p 4438) (p 4736) (p 5368) (derived105431 p h) (derived97169 p h) (derived97919 p h)

theorem derived111494 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 3609) ∨ (¬ p 3370) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2528) ∨ (p 3367) ∨ (¬ p 2177) ∨ (¬ p 4438) :=
  ElevenRUP.step111494 (p 2156) (p 2177) (p 2274) (p 2528) (p 3367) (p 3370) (p 3609) (p 3641) (p 4377) (p 4438) (p 5368) (derived106170 p h) (derived75594 p h) (derived97919 p h)

theorem derived111495 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2187) ∨ (p 3609) ∨ (¬ p 2528) ∨ (p 2210) ∨ (¬ p 3093) ∨ (¬ p 4516) ∨ (p 3367) :=
  ElevenRUP.step111495 (p 2187) (p 2210) (p 2528) (p 3093) (p 3367) (p 3609) (p 3641) (p 4377) (p 4384) (p 4516) (p 5368) (derived106170 p h) (derived106167 p h) (derived77789 p h) (derived97919 p h)

theorem derived111503 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3461) ∨ (¬ p 3276) :=
  ElevenRUP.step111503 (p 3276) (p 3461) (p 3564) (p 4022) (derived98814 p h) (derived90153 p h)

theorem derived111504 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3654) ∨ (p 3355) ∨ (¬ p 2584) :=
  ElevenRUP.step111504 (p 2584) (p 3355) (p 3564) (p 3654) (p 4022) (h 22173) (derived90153 p h)

theorem derived111505 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3746) ∨ (¬ p 2352) ∨ (¬ p 3990) :=
  ElevenRUP.step111505 (p 2352) (p 3564) (p 3746) (p 3990) (p 4022) (h 5990) (derived90153 p h)

theorem derived111506 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 5160) ∨ (¬ p 3125) ∨ (¬ p 3422) :=
  ElevenRUP.step111506 (p 3125) (p 3422) (p 3564) (p 3958) (p 4022) (p 5160) (derived105378 p h) (derived51970 p h) (derived90153 p h)

theorem derived111507 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3461) ∨ (¬ p 3193) ∨ (p 3016) ∨ (¬ p 2493) :=
  ElevenRUP.step111507 (p 2493) (p 3016) (p 3193) (p 3461) (p 3564) (p 4022) (derived85727 p h) (derived90153 p h)

theorem derived111508 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3323) ∨ (p 2295) ∨ (¬ p 3193) ∨ (¬ p 2493) :=
  ElevenRUP.step111508 (p 2295) (p 2493) (p 3193) (p 3323) (p 3564) (p 4022) (derived85800 p h) (derived90153 p h)

theorem derived111511 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3343) ∨ (¬ p 3483) ∨ (¬ p 3016) :=
  ElevenRUP.step111511 (p 3016) (p 3343) (p 3483) (p 3564) (p 4022) (p 5225) (derived105495 p h) (derived90258 p h) (derived90153 p h)

theorem derived111513 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 2573) ∨ (¬ p 3346) ∨ (p 2493) ∨ (p 3461) :=
  ElevenRUP.step111513 (p 2493) (p 2573) (p 3346) (p 3461) (p 3564) (p 4022) (derived99324 p h) (derived90153 p h)

theorem derived111515 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3343) ∨ (¬ p 3125) ∨ (¬ p 3016) :=
  ElevenRUP.step111515 (p 3016) (p 3125) (p 3343) (p 3564) (p 3958) (p 4022) (derived105378 p h) (derived101274 p h) (derived90153 p h)

theorem derived111516 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3343) ∨ (¬ p 2553) ∨ (¬ p 3016) ∨ (¬ p 4620) :=
  ElevenRUP.step111516 (p 2553) (p 3016) (p 3343) (p 3564) (p 4022) (p 4620) (derived101279 p h) (derived90153 p h)

theorem derived111521 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3125) ∨ (¬ p 3193) ∨ (¬ p 2406) ∨ (p 2187) ∨ (¬ p 4138) :=
  ElevenRUP.step111521 (p 2187) (p 2406) (p 3125) (p 3193) (p 3564) (p 4022) (p 4138) (derived90969 p h) (derived90153 p h)

theorem derived111522 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3422) ∨ (¬ p 3519) ∨ (p 3461) ∨ (¬ p 2573) ∨ (¬ p 3193) :=
  ElevenRUP.step111522 (p 2573) (p 3193) (p 3422) (p 3461) (p 3519) (p 3564) (p 4022) (derived101462 p h) (derived90153 p h)

theorem derived111523 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3343) ∨ (p 2573) ∨ (p 3461) ∨ (¬ p 2655) ∨ (¬ p 3016) :=
  ElevenRUP.step111523 (p 2573) (p 2655) (p 3016) (p 3343) (p 3461) (p 3564) (p 4022) (derived101853 p h) (derived90153 p h)

theorem derived111524 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3346) ∨ (¬ p 3990) ∨ (¬ p 2668) ∨ (¬ p 2573) :=
  ElevenRUP.step111524 (p 2573) (p 2668) (p 3346) (p 3564) (p 3990) (p 4022) (p 4976) (derived105465 p h) (derived61180 p h) (derived90153 p h)

theorem derived111531 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3276) ∨ (¬ p 2383) ∨ (p 3246) ∨ (¬ p 2781) ∨ (p 2870) ∨ (p 3266) ∨ (¬ p 3990) ∨ (p 2132) :=
  ElevenRUP.step111531 (p 2132) (p 2383) (p 2781) (p 2870) (p 3246) (p 3266) (p 3276) (p 3564) (p 3990) (p 4022) (p 4669) (derived105415 p h) (derived86672 p h) (derived90153 p h)

theorem derived111534 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 3461) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (p 2651) ∨ (¬ p 3422) ∨ (p 2088) ∨ (¬ p 3193) ∨ (¬ p 3487) ∨ (¬ p 3363) ∨ (¬ p 2474) :=
  ElevenRUP.step111534 (p 2088) (p 2249) (p 2474) (p 2651) (p 3189) (p 3193) (p 3256) (p 3363) (p 3422) (p 3461) (p 3487) (p 3564) (p 4022) (derived106513 p h) (derived87667 p h) (derived90153 p h)

theorem derived111535 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (p 2573) ∨ (¬ p 2252) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 3016) ∨ (¬ p 2870) ∨ (¬ p 2655) ∨ (¬ p 2753) ∨ (p 3343) :=
  ElevenRUP.step111535 (p 2132) (p 2252) (p 2573) (p 2655) (p 2750) (p 2753) (p 2870) (p 3016) (p 3246) (p 3343) (p 3564) (p 4022) (p 4625) (derived106345 p h) (derived106455 p h) (derived90707 p h) (derived90153 p h)

theorem derived111537 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 5160) ∨ (¬ p 3422) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 3905) ∨ (¬ p 2459) ∨ (p 2573) :=
  ElevenRUP.step111537 (p 2246) (p 2264) (p 2459) (p 2573) (p 2744) (p 2807) (p 3366) (p 3422) (p 3564) (p 3905) (p 4022) (p 4604) (p 5160) (derived106503 p h) (derived106293 p h) (derived99799 p h) (derived90153 p h)

theorem derived111538 (p : Nat → Prop) (h : Inputs p) :
    (p 3564) ∨ (¬ p 3246) ∨ (¬ p 5160) ∨ (¬ p 2901) ∨ (¬ p 3422) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 3905) ∨ (¬ p 2946) ∨ (p 2573) :=
  ElevenRUP.step111538 (p 2246) (p 2573) (p 2744) (p 2901) (p 2946) (p 3246) (p 3366) (p 3422) (p 3564) (p 3905) (p 4022) (p 4625) (p 5160) (derived106503 p h) (derived106455 p h) (derived101636 p h) (derived90153 p h)

theorem derived111540 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2098) ∨ (p 2774) :=
  ElevenRUP.step111540 (p 2098) (p 2774) (p 2819) (p 4078) (derived89711 p h) (derived102447 p h)

theorem derived111541 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 3537) ∨ (p 2829) :=
  ElevenRUP.step111541 (p 2819) (p 2829) (p 3537) (p 4078) (derived89756 p h) (derived102447 p h)

theorem derived111543 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2383) ∨ (p 3609) ∨ (¬ p 2363) :=
  ElevenRUP.step111543 (p 2363) (p 2383) (p 2788) (p 2819) (p 3609) (p 4078) (derived105375 p h) (derived83966 p h) (derived102447 p h)

theorem derived111544 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 3609) ∨ (¬ p 4170) ∨ (¬ p 2122) ∨ (¬ p 2088) :=
  ElevenRUP.step111544 (p 2088) (p 2122) (p 2819) (p 3609) (p 4078) (p 4170) (derived90369 p h) (derived102447 p h)

theorem derived111545 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 3609) ∨ (¬ p 2363) ∨ (p 2829) ∨ (¬ p 2737) :=
  ElevenRUP.step111545 (p 2363) (p 2737) (p 2819) (p 2829) (p 3609) (p 4078) (derived90511 p h) (derived102447 p h)

theorem derived111546 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 3609) ∨ (p 2829) ∨ (p 2608) ∨ (¬ p 2363) :=
  ElevenRUP.step111546 (p 2363) (p 2608) (p 2819) (p 2829) (p 3609) (p 4078) (derived97095 p h) (derived102447 p h)

theorem derived111547 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 3609) ∨ (¬ p 2363) ∨ (p 2774) ∨ (¬ p 2598) :=
  ElevenRUP.step111547 (p 2363) (p 2598) (p 2774) (p 2819) (p 3609) (p 4078) (derived97099 p h) (derived102447 p h)

theorem derived111549 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2829) ∨ (¬ p 3063) ∨ (p 3609) ∨ (¬ p 2363) :=
  ElevenRUP.step111549 (p 2363) (p 2819) (p 2829) (p 3063) (p 3609) (p 4078) (derived109331 p h) (derived102447 p h)

theorem derived111551 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 2641) ∨ (p 2696) ∨ (¬ p 4328) ∨ (¬ p 2098) :=
  ElevenRUP.step111551 (p 2098) (p 2641) (p 2696) (p 2745) (p 2819) (p 4078) (p 4328) (derived105523 p h) (derived93179 p h) (derived102447 p h)

theorem derived111552 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 4170) ∨ (¬ p 2187) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 4889) :=
  ElevenRUP.step111552 (p 2088) (p 2187) (p 2819) (p 3609) (p 4078) (p 4170) (p 4889) (derived93424 p h) (derived102447 p h)

theorem derived111556 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2166) ∨ (¬ p 3073) ∨ (¬ p 4185) ∨ (p 3609) ∨ (p 2891) :=
  ElevenRUP.step111556 (p 2166) (p 2819) (p 2891) (p 3073) (p 3609) (p 4078) (p 4185) (derived111211 p h) (derived102447 p h)

theorem derived111565 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2373) ∨ (¬ p 3379) ∨ (¬ p 2406) ∨ (p 2774) ∨ (p 3609) ∨ (¬ p 2363) :=
  ElevenRUP.step111565 (p 2363) (p 2373) (p 2406) (p 2774) (p 2819) (p 3379) (p 3609) (p 4078) (p 4433) (p 4736) (derived105431 p h) (derived106150 p h) (derived86320 p h) (derived102447 p h)

theorem derived111570 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2363) ∨ (¬ p 2696) ∨ (¬ p 2264) ∨ (p 2996) ∨ (p 2829) ∨ (p 3609) ∨ (¬ p 2742) :=
  ElevenRUP.step111570 (p 2264) (p 2363) (p 2696) (p 2742) (p 2819) (p 2829) (p 2996) (p 3609) (p 4078) (p 4503) (derived106530 p h) (derived97100 p h) (derived102447 p h)

theorem derived111571 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (p 3609) ∨ (¬ p 2992) ∨ (¬ p 2363) ∨ (p 2774) ∨ (¬ p 2241) ∨ (¬ p 3156) :=
  ElevenRUP.step111571 (p 2241) (p 2363) (p 2774) (p 2819) (p 2992) (p 3156) (p 3609) (p 4078) (p 4433) (p 4736) (derived105431 p h) (derived106150 p h) (derived97118 p h) (derived102447 p h)

theorem derived111572 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 2166) ∨ (p 2241) ∨ (¬ p 3366) ∨ (¬ p 2210) ∨ (p 2774) ∨ (¬ p 2363) ∨ (p 3609) :=
  ElevenRUP.step111572 (p 2166) (p 2210) (p 2241) (p 2363) (p 2744) (p 2774) (p 2819) (p 3366) (p 3609) (p 4078) (p 4433) (derived106503 p h) (derived106150 p h) (derived93841 p h) (derived102447 p h)

theorem derived111578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3276) ∨ (¬ p 3266) :=
  ElevenRUP.step111578 (p 2528) (p 3266) (p 3276) (p 4695) (derived79534 p h) (derived96004 p h)

theorem derived111580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2459) ∨ (p 3083) ∨ (¬ p 3343) :=
  ElevenRUP.step111580 (p 2459) (p 2528) (p 3083) (p 3343) (p 4695) (derived107100 p h) (derived96004 p h)

theorem derived111581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 4149) ∨ (p 3083) ∨ (¬ p 3343) :=
  ElevenRUP.step111581 (p 2528) (p 3083) (p 3343) (p 4149) (p 4695) (p 5118) (derived105482 p h) (derived74650 p h) (derived96004 p h)

theorem derived111582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3193) ∨ (¬ p 2509) ∨ (p 2088) ∨ (¬ p 2478) :=
  ElevenRUP.step111582 (p 2088) (p 2478) (p 2509) (p 2528) (p 3193) (p 4695) (derived81702 p h) (derived96004 p h)

theorem derived111583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2363) ∨ (p 2470) ∨ (¬ p 3355) :=
  ElevenRUP.step111583 (p 2363) (p 2470) (p 2528) (p 3355) (p 4384) (p 4695) (derived106167 p h) (derived85004 p h) (derived96004 p h)

theorem derived111584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3146) ∨ (¬ p 3355) ∨ (p 2470) :=
  ElevenRUP.step111584 (p 2470) (p 2528) (p 3146) (p 3355) (p 4434) (p 4695) (derived106144 p h) (derived85006 p h) (derived96004 p h)

theorem derived111585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2459) ∨ (¬ p 4438) ∨ (p 2470) ∨ (¬ p 3355) :=
  ElevenRUP.step111585 (p 2459) (p 2470) (p 2528) (p 3355) (p 4438) (p 4695) (derived85041 p h) (derived96004 p h)

theorem derived111586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2459) ∨ (p 3641) ∨ (¬ p 4438) ∨ (¬ p 3333) :=
  ElevenRUP.step111586 (p 2459) (p 2528) (p 3333) (p 3641) (p 4438) (p 4695) (derived95591 p h) (derived96004 p h)

theorem derived111587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 4149) ∨ (p 3641) ∨ (¬ p 3333) :=
  ElevenRUP.step111587 (p 2528) (p 3333) (p 3641) (p 4149) (p 4695) (p 5118) (derived105482 p h) (derived95598 p h) (derived96004 p h)

theorem derived111589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3073) ∨ (p 2470) ∨ (¬ p 3355) ∨ (¬ p 4685) :=
  ElevenRUP.step111589 (p 2470) (p 2528) (p 3073) (p 3355) (p 4685) (p 4695) (derived96679 p h) (derived96004 p h)

theorem derived111590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3146) ∨ (p 3083) ∨ (¬ p 3343) :=
  ElevenRUP.step111590 (p 2528) (p 3083) (p 3146) (p 3343) (p 4434) (p 4695) (derived106144 p h) (derived98672 p h) (derived96004 p h)

theorem derived111593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2982) ∨ (p 2363) ∨ (¬ p 3115) ∨ (p 3156) :=
  ElevenRUP.step111593 (p 2363) (p 2528) (p 2982) (p 3115) (p 3156) (p 4695) (derived111236 p h) (derived96004 p h)

theorem derived111594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3641) ∨ (p 3193) ∨ (p 3609) ∨ (¬ p 3590) :=
  ElevenRUP.step111594 (p 2528) (p 3193) (p 3590) (p 3609) (p 3641) (p 4695) (derived111469 p h) (derived96004 p h)

theorem derived111595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2363) ∨ (p 3083) ∨ (¬ p 2656) ∨ (¬ p 3355) :=
  ElevenRUP.step111595 (p 2363) (p 2528) (p 2656) (p 3083) (p 3355) (p 4384) (p 4695) (derived106167 p h) (derived74644 p h) (derived96004 p h)

theorem derived111599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 3631) ∨ (p 3527) ∨ (p 2363) ∨ (¬ p 4636) :=
  ElevenRUP.step111599 (p 2363) (p 2528) (p 3527) (p 3631) (p 4133) (p 4636) (p 4695) (derived105712 p h) (derived96042 p h) (derived96004 p h)

theorem derived111600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 4685) ∨ (p 3083) ∨ (¬ p 3343) ∨ (¬ p 3858) ∨ (p 2088) :=
  ElevenRUP.step111600 (p 2088) (p 2528) (p 3083) (p 3343) (p 3858) (p 4685) (p 4695) (derived98451 p h) (derived96004 p h)

theorem derived111602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 2363) ∨ (¬ p 4383) ∨ (p 3083) ∨ (¬ p 3343) :=
  ElevenRUP.step111602 (p 2363) (p 2528) (p 3083) (p 3343) (p 4133) (p 4383) (p 4695) (derived105712 p h) (derived101288 p h) (derived96004 p h)

theorem derived111616 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2829) ∨ (p 3367) :=
  ElevenRUP.step111616 (p 2829) (p 3367) (p 3422) (p 5220) (derived77760 p h) (derived97817 p h)

theorem derived111617 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2774) ∨ (p 2598) :=
  ElevenRUP.step111617 (p 2598) (p 2774) (p 3422) (p 5220) (derived77767 p h) (derived97817 p h)

theorem derived111619 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2819) ∨ (¬ p 4157) ∨ (¬ p 3641) :=
  ElevenRUP.step111619 (p 2819) (p 3422) (p 3641) (p 4157) (p 5220) (h 40808) (derived97817 p h)

theorem derived111620 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2122) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 2850) :=
  ElevenRUP.step111620 (p 2122) (p 2850) (p 3093) (p 3309) (p 3422) (p 5220) (derived77749 p h) (derived97817 p h)

theorem derived111621 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2819) ∨ (¬ p 3016) ∨ (¬ p 2352) :=
  ElevenRUP.step111621 (p 2352) (p 2819) (p 3016) (p 3422) (p 4750) (p 5220) (derived105433 p h) (derived77753 p h) (derived97817 p h)

theorem derived111631 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2553) ∨ (p 2122) ∨ (¬ p 3660) ∨ (¬ p 3641) ∨ (¬ p 4610) :=
  ElevenRUP.step111631 (p 2122) (p 2553) (p 3422) (p 3641) (p 3660) (p 4610) (p 5220) (derived77766 p h) (derived97817 p h)

theorem derived111639 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2307) ∨ (p 2122) ∨ (¬ p 2498) ∨ (¬ p 5016) ∨ (¬ p 2850) :=
  ElevenRUP.step111639 (p 2122) (p 2307) (p 2498) (p 2850) (p 3422) (p 4715) (p 5016) (p 5220) (derived105423 p h) (derived77763 p h) (derived97817 p h)

theorem derived111648 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2553) ∨ (p 2122) ∨ (¬ p 2284) ∨ (¬ p 2742) ∨ (p 3367) ∨ (¬ p 2992) ∨ (¬ p 2696) :=
  ElevenRUP.step111648 (p 2122) (p 2284) (p 2553) (p 2696) (p 2742) (p 2992) (p 3367) (p 3422) (p 4718) (p 5220) (derived105425 p h) (derived97829 p h) (derived97817 p h)

theorem derived111652 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 3917) ∨ (p 2946) ∨ (¬ p 2850) ∨ (¬ p 2573) ∨ (p 3156) ∨ (¬ p 3564) ∨ (¬ p 3362) ∨ (p 3146) :=
  ElevenRUP.step111652 (p 2573) (p 2850) (p 2946) (p 3146) (p 3156) (p 3362) (p 3422) (p 3564) (p 3917) (p 4789) (p 5220) (derived105646 p h) (derived88476 p h) (derived97817 p h)

theorem derived111654 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3461) ∨ (p 3266) :=
  ElevenRUP.step111654 (p 2363) (p 3266) (p 3461) (p 4171) (derived79610 p h) (derived96436 p h)

theorem derived111655 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 4397) ∨ (¬ p 4450) :=
  ElevenRUP.step111655 (p 2363) (p 4171) (p 4397) (p 4450) (h 6924) (derived96436 p h)

theorem derived111657 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4170) ∨ (¬ p 3322) ∨ (¬ p 2088) :=
  ElevenRUP.step111657 (p 2088) (p 2363) (p 3322) (p 4170) (p 4171) (h 6235) (derived96436 p h)

theorem derived111660 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4774) ∨ (¬ p 3256) ∨ (¬ p 2187) ∨ (p 3125) :=
  ElevenRUP.step111660 (p 2187) (p 2363) (p 3125) (p 3256) (p 4171) (p 4774) (derived75291 p h) (derived96436 p h)

theorem derived111661 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3564) ∨ (¬ p 2352) ∨ (¬ p 3146) :=
  ElevenRUP.step111661 (p 2352) (p 2363) (p 3146) (p 3564) (p 4134) (p 4171) (derived105379 p h) (derived78777 p h) (derived96436 p h)

theorem derived111663 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3323) ∨ (¬ p 2668) ∨ (¬ p 2528) :=
  ElevenRUP.step111663 (p 2363) (p 2528) (p 2668) (p 3323) (p 4171) (p 4384) (derived106167 p h) (derived79230 p h) (derived96436 p h)

theorem derived111664 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3979) ∨ (p 3323) ∨ (¬ p 2668) ∨ (¬ p 5568) :=
  ElevenRUP.step111664 (p 2363) (p 2668) (p 3323) (p 3979) (p 4171) (p 5568) (derived79243 p h) (derived96436 p h)

theorem derived111665 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3063) ∨ (p 3319) ∨ (¬ p 2528) :=
  ElevenRUP.step111665 (p 2363) (p 2528) (p 3063) (p 3319) (p 4171) (p 4384) (derived106167 p h) (derived83538 p h) (derived96436 p h)

theorem derived111666 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3063) ∨ (p 3319) ∨ (¬ p 3146) :=
  ElevenRUP.step111666 (p 2363) (p 3063) (p 3146) (p 3319) (p 4134) (p 4171) (derived105379 p h) (derived83539 p h) (derived96436 p h)

theorem derived111668 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3564) ∨ (¬ p 2459) ∨ (¬ p 2352) :=
  ElevenRUP.step111668 (p 2352) (p 2363) (p 2459) (p 3564) (p 4133) (p 4171) (derived105712 p h) (derived95241 p h) (derived96436 p h)

theorem derived111671 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2459) ∨ (¬ p 2187) ∨ (p 3125) :=
  ElevenRUP.step111671 (p 2187) (p 2363) (p 2459) (p 3125) (p 4133) (p 4171) (derived105712 p h) (derived100333 p h) (derived96436 p h)

theorem derived111674 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3461) ∨ (¬ p 4045) ∨ (¬ p 2459) ∨ (p 3276) :=
  ElevenRUP.step111674 (p 2363) (p 2459) (p 3276) (p 3461) (p 4045) (p 4171) (p 4420) (derived105707 p h) (derived79533 p h) (derived96436 p h)

theorem derived111675 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3073) ∨ (¬ p 2383) ∨ (p 3654) ∨ (¬ p 4370) :=
  ElevenRUP.step111675 (p 2363) (p 2383) (p 3073) (p 3654) (p 4171) (p 4370) (p 4384) (derived106167 p h) (derived80252 p h) (derived96436 p h)

theorem derived111678 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2528) ∨ (¬ p 3693) ∨ (p 3654) ∨ (¬ p 2383) :=
  ElevenRUP.step111678 (p 2363) (p 2383) (p 2528) (p 3654) (p 3693) (p 4134) (p 4171) (derived105379 p h) (derived83101 p h) (derived96436 p h)

theorem derived111683 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3979) ∨ (p 3125) ∨ (¬ p 2383) ∨ (¬ p 3743) :=
  ElevenRUP.step111683 (p 2363) (p 2383) (p 3125) (p 3743) (p 3979) (p 4171) (p 5122) (derived105483 p h) (derived94125 p h) (derived96436 p h)

theorem derived111684 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3979) ∨ (¬ p 3917) ∨ (¬ p 2383) ∨ (¬ p 2779) :=
  ElevenRUP.step111684 (p 2363) (p 2383) (p 2779) (p 3917) (p 3979) (p 4171) (p 5122) (derived105483 p h) (derived41866 p h) (derived96436 p h)

theorem derived111685 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 4328) ∨ (¬ p 2668) ∨ (¬ p 3917) ∨ (¬ p 2459) :=
  ElevenRUP.step111685 (p 2363) (p 2459) (p 2668) (p 3917) (p 4133) (p 4171) (p 4328) (derived105712 p h) (derived42018 p h) (derived96436 p h)

theorem derived111686 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3323) ∨ (¬ p 2459) ∨ (¬ p 2187) ∨ (¬ p 3986) :=
  ElevenRUP.step111686 (p 2187) (p 2363) (p 2459) (p 3323) (p 3986) (p 4133) (p 4171) (derived105712 p h) (derived101687 p h) (derived96436 p h)

theorem derived111692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3276) ∨ (¬ p 2761) :=
  ElevenRUP.step111692 (p 2417) (p 2761) (p 3276) (p 4451) (derived79545 p h) (derived96424 p h)

theorem derived111696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3193) ∨ (p 2922) ∨ (p 2911) :=
  ElevenRUP.step111696 (p 2417) (p 2911) (p 2922) (p 3193) (p 4451) (p 4668) (derived105414 p h) (derived81641 p h) (derived96424 p h)

theorem derived111697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2922) ∨ (p 3193) ∨ (¬ p 2761) ∨ (¬ p 2437) :=
  ElevenRUP.step111697 (p 2417) (p 2437) (p 2761) (p 2922) (p 3193) (p 4451) (derived81651 p h) (derived96424 p h)

theorem derived111699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3193) ∨ (p 3246) ∨ (p 2922) :=
  ElevenRUP.step111699 (p 2417) (p 2922) (p 3193) (p 3246) (p 4451) (p 4647) (derived105412 p h) (derived81656 p h) (derived96424 p h)

theorem derived111700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3193) ∨ (p 2922) ∨ (p 2396) :=
  ElevenRUP.step111700 (p 2396) (p 2417) (p 2922) (p 3193) (p 4451) (p 4712) (derived105422 p h) (derived81657 p h) (derived96424 p h)

theorem derived111701 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3389) ∨ (p 2449) ∨ (¬ p 3355) :=
  ElevenRUP.step111701 (p 2417) (p 2449) (p 3355) (p 3389) (p 4327) (p 4451) (derived105381 p h) (derived85011 p h) (derived96424 p h)

theorem derived111702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3246) ∨ (p 3389) ∨ (¬ p 3355) :=
  ElevenRUP.step111702 (p 2417) (p 3246) (p 3355) (p 3389) (p 4451) (p 4647) (derived105412 p h) (derived85012 p h) (derived96424 p h)

theorem derived111703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3389) ∨ (¬ p 2437) ∨ (¬ p 3355) ∨ (¬ p 2761) :=
  ElevenRUP.step111703 (p 2417) (p 2437) (p 2761) (p 3355) (p 3389) (p 4451) (derived85026 p h) (derived96424 p h)

theorem derived111704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3631) ∨ (p 3389) ∨ (¬ p 3355) :=
  ElevenRUP.step111704 (p 2417) (p 2930) (p 3355) (p 3389) (p 3631) (p 4451) (derived105376 p h) (derived85042 p h) (derived96424 p h)

theorem derived111705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 2761) ∨ (¬ p 3355) ∨ (p 3389) :=
  ElevenRUP.step111705 (p 2417) (p 2761) (p 2922) (p 3355) (p 3389) (p 4451) (derived85047 p h) (derived96424 p h)

theorem derived111708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2396) ∨ (¬ p 3333) ∨ (p 3201) :=
  ElevenRUP.step111708 (p 2396) (p 2417) (p 3201) (p 3333) (p 4451) (p 4712) (derived105422 p h) (derived95623 p h) (derived96424 p h)

theorem derived111709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3192) ∨ (¬ p 2177) ∨ (p 2911) ∨ (p 2449) :=
  ElevenRUP.step111709 (p 2177) (p 2417) (p 2449) (p 2911) (p 3192) (p 4451) (derived100129 p h) (derived96424 p h)

theorem derived111710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3631) ∨ (p 2437) ∨ (¬ p 3343) :=
  ElevenRUP.step111710 (p 2417) (p 2437) (p 2930) (p 3343) (p 3631) (p 4451) (derived105376 p h) (derived101965 p h) (derived96424 p h)

theorem derived111711 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2449) ∨ (p 3276) ∨ (¬ p 3506) ∨ (p 2396) :=
  ElevenRUP.step111711 (p 2396) (p 2417) (p 2449) (p 3276) (p 3506) (p 4451) (derived110274 p h) (derived96424 p h)

theorem derived111726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3193) ∨ (p 3609) ∨ (p 2922) ∨ (¬ p 3389) ∨ (¬ p 2363) ∨ (p 2098) ∨ (¬ p 4079) ∨ (¬ p 3657) :=
  ElevenRUP.step111726 (p 2098) (p 2363) (p 2417) (p 2922) (p 3193) (p 3389) (p 3609) (p 3657) (p 4079) (p 4451) (p 4503) (p 4736) (derived105431 p h) (derived106530 p h) (derived81672 p h) (derived96424 p h)

theorem derived111731 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2717) ∨ (p 2177) :=
  ElevenRUP.step111731 (p 2122) (p 2177) (p 2717) (p 4471) (derived89184 p h) (derived102189 p h)

theorem derived111732 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3434) ∨ (p 2396) :=
  ElevenRUP.step111732 (p 2122) (p 2396) (p 3434) (p 4471) (derived90119 p h) (derived102189 p h)

theorem derived111736 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2707) ∨ (¬ p 2295) ∨ (¬ p 2829) :=
  ElevenRUP.step111736 (p 2122) (p 2295) (p 2707) (p 2829) (p 4471) (p 4843) (derived105449 p h) (derived88275 p h) (derived102189 p h)

theorem derived111737 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2707) ∨ (¬ p 2829) ∨ (¬ p 2553) :=
  ElevenRUP.step111737 (p 2122) (p 2553) (p 2707) (p 2829) (p 4471) (p 5222) (derived105793 p h) (derived88342 p h) (derived102189 p h)

theorem derived111738 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2707) ∨ (¬ p 2819) ∨ (¬ p 2829) :=
  ElevenRUP.step111738 (p 2122) (p 2707) (p 2819) (p 2829) (p 4405) (p 4471) (derived105512 p h) (derived88375 p h) (derived102189 p h)

theorem derived111739 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2707) ∨ (¬ p 3483) ∨ (¬ p 2829) :=
  ElevenRUP.step111739 (p 2122) (p 2707) (p 2829) (p 3483) (p 4471) (p 4624) (derived105408 p h) (derived88441 p h) (derived102189 p h)

theorem derived111740 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2774) ∨ (¬ p 2274) ∨ (¬ p 3425) ∨ (¬ p 4889) :=
  ElevenRUP.step111740 (p 2122) (p 2274) (p 2774) (p 3425) (p 4471) (p 4889) (derived45010 p h) (derived102189 p h)

theorem derived111741 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 3367) ∨ (¬ p 3425) ∨ (¬ p 2598) ∨ (¬ p 2553) :=
  ElevenRUP.step111741 (p 2122) (p 2553) (p 2598) (p 3367) (p 3425) (p 4471) (derived88663 p h) (derived102189 p h)

theorem derived111743 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3425) ∨ (¬ p 2295) ∨ (¬ p 2774) :=
  ElevenRUP.step111743 (p 2122) (p 2295) (p 2774) (p 3425) (p 4471) (p 4843) (derived105449 p h) (derived52881 p h) (derived102189 p h)

theorem derived111744 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2396) ∨ (p 2829) ∨ (¬ p 2774) ∨ (¬ p 3425) :=
  ElevenRUP.step111744 (p 2122) (p 2396) (p 2774) (p 2829) (p 3425) (p 4471) (derived90124 p h) (derived102189 p h)

theorem derived111745 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3425) ∨ (¬ p 2774) ∨ (¬ p 2553) :=
  ElevenRUP.step111745 (p 2122) (p 2553) (p 2774) (p 3425) (p 4471) (p 5222) (derived105793 p h) (derived53616 p h) (derived102189 p h)

theorem derived111754 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2707) ∨ (¬ p 4390) ∨ (¬ p 2829) ∨ (¬ p 2274) :=
  ElevenRUP.step111754 (p 2122) (p 2274) (p 2707) (p 2829) (p 3958) (p 4390) (p 4471) (derived105378 p h) (derived88277 p h) (derived102189 p h)

theorem derived111759 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2177) ∨ (p 2774) ∨ (¬ p 2829) ∨ (p 2707) ∨ (¬ p 3873) :=
  ElevenRUP.step111759 (p 2122) (p 2177) (p 2707) (p 2774) (p 2829) (p 3873) (p 4471) (derived101362 p h) (derived102189 p h)

theorem derived111772 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2098) ∨ (¬ p 3425) :=
  ElevenRUP.step111772 (p 2098) (p 2717) (p 3425) (p 3685) (h 17796) (derived97921 p h)

theorem derived111773 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3537) ∨ (p 2707) :=
  ElevenRUP.step111773 (p 2707) (p 2717) (p 3537) (p 3685) (derived89777 p h) (derived97921 p h)

theorem derived111774 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 4968) ∨ (¬ p 4782) :=
  ElevenRUP.step111774 (p 2717) (p 3685) (p 4782) (p 4968) (h 38910) (derived97921 p h)

theorem derived111775 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 4364) ∨ (¬ p 4357) :=
  ElevenRUP.step111775 (p 2717) (p 3685) (p 4357) (p 4364) (h 40253) (derived97921 p h)

theorem derived111781 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (p 3609) ∨ (¬ p 4895) :=
  ElevenRUP.step111781 (p 2459) (p 2717) (p 2881) (p 3609) (p 3685) (p 4895) (derived97108 p h) (derived97921 p h)

theorem derived111782 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2110) ∨ (¬ p 2088) ∨ (p 3609) ∨ (p 2696) ∨ (¬ p 4782) :=
  ElevenRUP.step111782 (p 2088) (p 2110) (p 2696) (p 2717) (p 3609) (p 3685) (p 4782) (derived82696 p h) (derived97921 p h)

theorem derived111784 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 3873) ∨ (¬ p 3425) ∨ (¬ p 5239) :=
  ElevenRUP.step111784 (p 2088) (p 2717) (p 3425) (p 3609) (p 3685) (p 3873) (p 5239) (derived88657 p h) (derived97921 p h)

theorem derived111785 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 2922) ∨ (¬ p 2098) ∨ (p 2598) ∨ (¬ p 3658) :=
  ElevenRUP.step111785 (p 2098) (p 2598) (p 2717) (p 2922) (p 3658) (p 3685) (p 5214) (derived105492 p h) (derived89802 p h) (derived97921 p h)

theorem derived111792 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 3005) ∨ (p 3256) ∨ (¬ p 2696) ∨ (¬ p 3425) ∨ (¬ p 2459) :=
  ElevenRUP.step111792 (p 2459) (p 2696) (p 2717) (p 3005) (p 3256) (p 3425) (p 3685) (derived110581 p h) (derived97921 p h)

theorem derived111797 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 5564) ∨ (¬ p 3577) ∨ (¬ p 4138) ∨ (¬ p 4063) ∨ (¬ p 2363) ∨ (p 3609) :=
  ElevenRUP.step111797 (p 2363) (p 2717) (p 3577) (p 3609) (p 3685) (p 4063) (p 4138) (p 5564) (derived89800 p h) (derived97921 p h)

theorem derived111799 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 4325) ∨ (¬ p 5612) ∨ (¬ p 3941) ∨ (¬ p 4275) ∨ (¬ p 2449) ∨ (¬ p 2881) :=
  ElevenRUP.step111799 (p 2449) (p 2717) (p 2881) (p 3685) (p 3941) (p 4275) (p 4325) (p 5612) (derived59365 p h) (derived97921 p h)

theorem derived111802 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3425) ∨ (¬ p 2187) ∨ (¬ p 2284) ∨ (¬ p 2459) ∨ (¬ p 2946) ∨ (p 3609) :=
  ElevenRUP.step111802 (p 2187) (p 2284) (p 2459) (p 2717) (p 2946) (p 3425) (p 3609) (p 3685) (p 4133) (p 4786) (derived105712 p h) (derived106425 p h) (derived89803 p h) (derived97921 p h)

theorem derived111803 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 3425) ∨ (p 3609) ∨ (¬ p 2459) :=
  ElevenRUP.step111803 (p 2373) (p 2406) (p 2459) (p 2717) (p 3379) (p 3425) (p 3609) (p 3685) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived97157 p h) (derived97921 p h)

theorem derived111805 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 3609) ∨ (p 2241) ∨ (¬ p 2210) ∨ (¬ p 2166) ∨ (¬ p 2459) ∨ (¬ p 3366) ∨ (¬ p 3425) :=
  ElevenRUP.step111805 (p 2166) (p 2210) (p 2241) (p 2459) (p 2717) (p 2744) (p 3366) (p 3425) (p 3609) (p 3685) (p 4902) (derived106503 p h) (derived105456 p h) (derived89801 p h) (derived97921 p h)

theorem derived111808 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 3193) ∨ (¬ p 3276) ∨ (p 3422) ∨ (¬ p 3146) ∨ (p 3609) ∨ (¬ p 3759) ∨ (¬ p 3347) ∨ (¬ p 2441) ∨ (¬ p 5503) ∨ (¬ p 4253) :=
  ElevenRUP.step111808 (p 2441) (p 2717) (p 3146) (p 3193) (p 3276) (p 3347) (p 3422) (p 3609) (p 3685) (p 3759) (p 4253) (p 4715) (p 5503) (derived105423 p h) (derived97202 p h) (derived97921 p h)

theorem derived111812 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2707) ∨ (p 2829) :=
  ElevenRUP.step111812 (p 2122) (p 2707) (p 2829) (p 3689) (derived87984 p h) (derived101823 p h)

theorem derived111815 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3959) ∨ (¬ p 3819) ∨ (p 2774) :=
  ElevenRUP.step111815 (p 2122) (p 2774) (p 3689) (p 3819) (p 3959) (derived87985 p h) (derived101823 p h)

theorem derived111816 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 2598) ∨ (p 2774) :=
  ElevenRUP.step111816 (p 2122) (p 2177) (p 2598) (p 2717) (p 2774) (p 3689) (derived86307 p h) (derived101823 p h)

theorem derived111817 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2717) ∨ (¬ p 2307) ∨ (¬ p 2177) :=
  ElevenRUP.step111817 (p 2122) (p 2177) (p 2307) (p 2717) (p 2788) (p 3689) (derived105375 p h) (derived87973 p h) (derived101823 p h)

theorem derived111818 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 3483) :=
  ElevenRUP.step111818 (p 2122) (p 2177) (p 2717) (p 3483) (p 3689) (p 4624) (derived105408 p h) (derived87975 p h) (derived101823 p h)

theorem derived111819 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 2553) :=
  ElevenRUP.step111819 (p 2122) (p 2177) (p 2553) (p 2717) (p 3689) (p 5222) (derived105793 p h) (derived87976 p h) (derived101823 p h)

theorem derived111820 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 3434) ∨ (¬ p 2396) ∨ (¬ p 2819) :=
  ElevenRUP.step111820 (p 2122) (p 2396) (p 2819) (p 3434) (p 3689) (p 4405) (derived105512 p h) (derived87982 p h) (derived101823 p h)

theorem derived111821 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 3434) ∨ (¬ p 2396) ∨ (¬ p 2295) :=
  ElevenRUP.step111821 (p 2122) (p 2295) (p 2396) (p 3434) (p 3689) (p 4843) (derived105449 p h) (derived87989 p h) (derived101823 p h)

theorem derived111824 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 4106) ∨ (p 2829) ∨ (¬ p 3367) ∨ (¬ p 3389) :=
  ElevenRUP.step111824 (p 2122) (p 2829) (p 3367) (p 3389) (p 3689) (p 4106) (p 4730) (derived106074 p h) (derived77781 p h) (derived101823 p h)

theorem derived111825 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2598) ∨ (p 2417) ∨ (¬ p 2396) ∨ (¬ p 4106) ∨ (p 2774) :=
  ElevenRUP.step111825 (p 2122) (p 2396) (p 2417) (p 2598) (p 2774) (p 3689) (p 4106) (derived86357 p h) (derived101823 p h)

theorem derived111827 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 3434) ∨ (¬ p 2312) ∨ (¬ p 3516) ∨ (¬ p 2553) :=
  ElevenRUP.step111827 (p 2122) (p 2312) (p 2553) (p 3434) (p 3516) (p 3689) (p 5222) (derived105793 p h) (derived87974 p h) (derived101823 p h)

theorem derived111835 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 4423) ∨ (¬ p 2187) ∨ (¬ p 4185) ∨ (¬ p 4427) ∨ (¬ p 4075) :=
  ElevenRUP.step111835 (p 2122) (p 2187) (p 3689) (p 4075) (p 4185) (p 4405) (p 4423) (p 4427) (derived105512 p h) (derived42248 p h) (derived101823 p h)

theorem derived111839 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 3527) ∨ (¬ p 3546) ∨ (p 2717) ∨ (¬ p 2274) ∨ (¬ p 2312) ∨ (¬ p 4889) :=
  ElevenRUP.step111839 (p 2122) (p 2274) (p 2312) (p 2717) (p 3527) (p 3546) (p 3689) (p 4889) (derived87991 p h) (derived101823 p h)

theorem derived111848 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 5558) ∨ (¬ p 3146) ∨ (p 2774) ∨ (p 2717) ∨ (¬ p 2166) ∨ (¬ p 2210) :=
  ElevenRUP.step111848 (p 2122) (p 2166) (p 2210) (p 2717) (p 2774) (p 3146) (p 3689) (p 4736) (p 5118) (p 5558) (derived105431 p h) (derived105482 p h) (derived87981 p h) (derived101823 p h)

theorem derived111849 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 4328) ∨ (¬ p 5558) ∨ (¬ p 2528) ∨ (¬ p 2470) ∨ (p 2717) ∨ (¬ p 2656) ∨ (¬ p 2630) ∨ (p 2331) :=
  ElevenRUP.step111849 (p 2122) (p 2331) (p 2470) (p 2528) (p 2630) (p 2656) (p 2717) (p 3689) (p 4328) (p 5118) (p 5558) (derived105482 p h) (derived101087 p h) (derived101823 p h)

theorem derived111852 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3609) ∨ (¬ p 3146) :=
  ElevenRUP.step111852 (p 2619) (p 3146) (p 3609) (p 4188) (derived88204 p h) (derived101917 p h)

theorem derived111857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2839) ∨ (¬ p 2098) ∨ (¬ p 3146) ∨ (p 2132) :=
  ElevenRUP.step111857 (p 2098) (p 2132) (p 2619) (p 2839) (p 3146) (p 4188) (derived83700 p h) (derived101917 p h)

theorem derived111858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2098) ∨ (p 2373) ∨ (¬ p 4885) ∨ (p 2132) :=
  ElevenRUP.step111858 (p 2098) (p 2132) (p 2373) (p 2619) (p 4188) (p 4885) (derived88201 p h) (derived101917 p h)

theorem derived111859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2166) ∨ (¬ p 2098) ∨ (p 2132) :=
  ElevenRUP.step111859 (p 2098) (p 2132) (p 2166) (p 2619) (p 4188) (p 4875) (derived106227 p h) (derived88208 p h) (derived101917 p h)

theorem derived111861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3537) ∨ (p 2860) ∨ (p 2839) :=
  ElevenRUP.step111861 (p 2619) (p 2839) (p 2860) (p 3537) (p 4188) (p 4509) (derived105392 p h) (derived88211 p h) (derived101917 p h)

theorem derived111862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3537) ∨ (p 2839) ∨ (¬ p 2132) ∨ (¬ p 3146) :=
  ElevenRUP.step111862 (p 2132) (p 2619) (p 2839) (p 3146) (p 3537) (p 4188) (derived89745 p h) (derived101917 p h)

theorem derived111863 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2373) ∨ (¬ p 3537) ∨ (p 2839) ∨ (¬ p 4885) :=
  ElevenRUP.step111863 (p 2373) (p 2619) (p 2839) (p 3537) (p 4188) (p 4885) (derived89746 p h) (derived101917 p h)

theorem derived111867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3146) ∨ (¬ p 2098) ∨ (p 3105) ∨ (p 2132) :=
  ElevenRUP.step111867 (p 2098) (p 2132) (p 2619) (p 3105) (p 3146) (p 4188) (derived107815 p h) (derived101917 p h)

theorem derived111868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 4009) ∨ (¬ p 5612) ∨ (¬ p 4237) ∨ (p 2284) :=
  ElevenRUP.step111868 (p 2284) (p 2619) (p 4009) (p 4188) (p 4237) (p 4509) (p 5612) (derived105392 p h) (derived84958 p h) (derived101917 p h)

theorem derived111869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2098) ∨ (p 2553) ∨ (¬ p 4342) ∨ (p 3156) ∨ (p 2774) :=
  ElevenRUP.step111869 (p 2098) (p 2553) (p 2619) (p 2774) (p 3156) (p 4188) (p 4342) (derived86336 p h) (derived101917 p h)

theorem derived111872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2098) ∨ (p 2284) ∨ (p 2132) ∨ (¬ p 4316) :=
  ElevenRUP.step111872 (p 2098) (p 2132) (p 2284) (p 2619) (p 4188) (p 4316) (p 4509) (derived105392 p h) (derived88203 p h) (derived101917 p h)

theorem derived111880 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3537) ∨ (p 2459) ∨ (p 2911) ∨ (p 3389) ∨ (¬ p 3969) ∨ (¬ p 2608) :=
  ElevenRUP.step111880 (p 2459) (p 2608) (p 2619) (p 2911) (p 3389) (p 3537) (p 3969) (p 4188) (p 5122) (p 5193) (derived105488 p h) (derived105483 p h) (derived89775 p h) (derived101917 p h)

theorem derived111881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 2668) ∨ (p 2363) ∨ (¬ p 2608) ∨ (p 2331) ∨ (¬ p 3537) ∨ (¬ p 3969) :=
  ElevenRUP.step111881 (p 2254) (p 2331) (p 2363) (p 2608) (p 2619) (p 2668) (p 3537) (p 3969) (p 4188) (p 5122) (derived105366 p h) (derived105483 p h) (derived89784 p h) (derived101917 p h)

theorem derived111882 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3323) ∨ (p 3461) ∨ (¬ p 2608) ∨ (p 2331) ∨ (¬ p 3537) ∨ (¬ p 3969) ∨ (¬ p 5119) :=
  ElevenRUP.step111882 (p 2254) (p 2331) (p 2608) (p 2619) (p 3323) (p 3461) (p 3537) (p 3969) (p 4188) (p 5119) (derived105366 p h) (derived89786 p h) (derived101917 p h)

theorem derived111888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (p 3389) ∨ (¬ p 3146) ∨ (p 2911) ∨ (¬ p 2098) ∨ (¬ p 2655) ∨ (¬ p 5558) ∨ (p 2132) ∨ (¬ p 2252) ∨ (¬ p 2748) :=
  ElevenRUP.step111888 (p 2098) (p 2132) (p 2252) (p 2619) (p 2655) (p 2748) (p 2911) (p 3146) (p 3389) (p 4188) (p 5118) (p 5558) (derived105482 p h) (derived89425 p h) (derived101917 p h)

theorem derived111889 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3791) ∨ (¬ p 4389) ∨ (p 3266) ∨ (p 2220) ∨ (p 3609) ∨ (¬ p 2295) ∨ (¬ p 2573) ∨ (¬ p 2136) ∨ (¬ p 4419) :=
  ElevenRUP.step111889 (p 2136) (p 2220) (p 2295) (p 2573) (p 2619) (p 3266) (p 3609) (p 3791) (p 4188) (p 4389) (p 4419) (p 4826) (derived105444 p h) (derived97159 p h) (derived101917 p h)

theorem derived111892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 3461) ∨ (¬ p 3266) :=
  ElevenRUP.step111892 (p 2363) (p 3266) (p 3461) (p 4345) (h 38851) (derived99552 p h)

theorem derived111893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 2532) ∨ (¬ p 5045) :=
  ElevenRUP.step111893 (p 2363) (p 2532) (p 4345) (p 5045) (h 33471) (derived99552 p h)

theorem derived111894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 4157) ∨ (p 2528) ∨ (¬ p 3990) :=
  ElevenRUP.step111894 (p 2363) (p 2528) (p 3990) (p 4157) (p 4345) (derived80733 p h) (derived99552 p h)

theorem derived111896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 2528) ∨ (¬ p 3323) ∨ (¬ p 4596) ∨ (p 2668) :=
  ElevenRUP.step111896 (p 2363) (p 2528) (p 2668) (p 3323) (p 4345) (p 4596) (derived80730 p h) (derived99552 p h)

theorem derived111897 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3564) ∨ (p 2352) ∨ (p 2459) :=
  ElevenRUP.step111897 (p 2352) (p 2363) (p 2459) (p 3564) (p 4345) (p 4503) (derived106530 p h) (derived80734 p h) (derived99552 p h)

theorem derived111899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3564) ∨ (¬ p 5580) ∨ (p 2352) :=
  ElevenRUP.step111899 (p 2352) (p 2363) (p 3564) (p 4345) (p 5118) (p 5580) (derived105482 p h) (derived80736 p h) (derived99552 p h)

theorem derived111903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 5580) ∨ (¬ p 3323) ∨ (p 2668) :=
  ElevenRUP.step111903 (p 2363) (p 2668) (p 3323) (p 4345) (p 5118) (p 5580) (derived105482 p h) (derived80747 p h) (derived99552 p h)

theorem derived111904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3319) ∨ (p 2459) ∨ (¬ p 3923) :=
  ElevenRUP.step111904 (p 2363) (p 2459) (p 3319) (p 3923) (p 4345) (p 4503) (derived106530 p h) (derived84201 p h) (derived99552 p h)

theorem derived111905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 5580) ∨ (¬ p 3483) ∨ (p 2819) :=
  ElevenRUP.step111905 (p 2363) (p 2819) (p 3483) (p 4345) (p 5118) (p 5580) (derived105482 p h) (derived90234 p h) (derived99552 p h)

theorem derived111906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3654) ∨ (p 2459) ∨ (p 2383) :=
  ElevenRUP.step111906 (p 2363) (p 2383) (p 2459) (p 3654) (p 4345) (p 4503) (derived106530 p h) (derived90927 p h) (derived99552 p h)

theorem derived111907 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3654) ∨ (p 3146) ∨ (p 2383) :=
  ElevenRUP.step111907 (p 2363) (p 2383) (p 3146) (p 3654) (p 4345) (p 4433) (derived106150 p h) (derived90929 p h) (derived99552 p h)

theorem derived111910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 2668) ∨ (p 2459) ∨ (¬ p 3323) :=
  ElevenRUP.step111910 (p 2363) (p 2459) (p 2668) (p 3323) (p 4345) (p 4503) (derived106530 p h) (derived91755 p h) (derived99552 p h)

theorem derived111912 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 2383) ∨ (¬ p 3564) ∨ (p 2352) ∨ (p 2088) :=
  ElevenRUP.step111912 (p 2088) (p 2352) (p 2363) (p 2383) (p 3564) (p 4345) (derived108945 p h) (derived99552 p h)

theorem derived111915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 5580) ∨ (¬ p 3125) ∨ (p 2668) ∨ (¬ p 3986) :=
  ElevenRUP.step111915 (p 2363) (p 2668) (p 3125) (p 3986) (p 4345) (p 5118) (p 5580) (derived105482 p h) (derived79480 p h) (derived99552 p h)

theorem derived111920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3483) ∨ (¬ p 4995) ∨ (¬ p 3858) ∨ (p 2088) ∨ (p 2819) :=
  ElevenRUP.step111920 (p 2088) (p 2363) (p 2819) (p 3483) (p 3858) (p 4345) (p 4995) (derived90242 p h) (derived99552 p h)

theorem derived111921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3564) ∨ (¬ p 5580) ∨ (p 2383) ∨ (¬ p 2386) :=
  ElevenRUP.step111921 (p 2363) (p 2383) (p 2386) (p 3564) (p 4345) (p 5118) (p 5580) (derived105482 p h) (derived91302 p h) (derived99552 p h)

theorem derived111934 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3848) ∨ (¬ p 2641) :=
  ElevenRUP.step111934 (p 2641) (p 3323) (p 3848) (p 4421) (h 33862) (derived95302 p h)

theorem derived111935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3286) ∨ (¬ p 3987) ∨ (¬ p 2667) :=
  ElevenRUP.step111935 (p 2667) (p 3286) (p 3323) (p 3987) (p 4421) (derived84987 p h) (derived95302 p h)

theorem derived111936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3343) ∨ (¬ p 2331) ∨ (p 2651) :=
  ElevenRUP.step111936 (p 2331) (p 2651) (p 3323) (p 3343) (p 4421) (derived109939 p h) (derived95302 p h)

theorem derived111937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3256) ∨ (p 3166) ∨ (¬ p 2331) :=
  ElevenRUP.step111937 (p 2331) (p 3166) (p 3256) (p 3323) (p 4421) (derived111094 p h) (derived95302 p h)

theorem derived111941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 2295) ∨ (p 3461) ∨ (¬ p 3506) :=
  ElevenRUP.step111941 (p 2295) (p 3323) (p 3461) (p 3506) (p 4421) (p 4624) (derived105408 p h) (derived98648 p h) (derived95302 p h)

theorem derived111942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 2668) ∨ (¬ p 3325) ∨ (p 3564) ∨ (p 3461) ∨ (¬ p 3506) :=
  ElevenRUP.step111942 (p 2668) (p 3323) (p 3325) (p 3461) (p 3506) (p 3564) (p 4421) (derived82506 p h) (derived95302 p h)

theorem derived111945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3461) ∨ (¬ p 5454) ∨ (¬ p 3670) ∨ (p 3564) :=
  ElevenRUP.step111945 (p 3323) (p 3461) (p 3564) (p 3670) (p 4421) (p 4976) (p 5454) (derived105465 p h) (derived96196 p h) (derived95302 p h)

theorem derived111947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3343) ∨ (¬ p 3276) ∨ (p 3461) ∨ (p 2651) ∨ (¬ p 2331) :=
  ElevenRUP.step111947 (p 2331) (p 2651) (p 3276) (p 3323) (p 3343) (p 3461) (p 4421) (derived111270 p h) (derived95302 p h)

theorem derived111949 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3266) ∨ (¬ p 5568) ∨ (¬ p 3506) ∨ (p 2132) ∨ (¬ p 2331) ∨ (p 2619) :=
  ElevenRUP.step111949 (p 2132) (p 2331) (p 2619) (p 3266) (p 3323) (p 3506) (p 4421) (p 5568) (derived108990 p h) (derived95302 p h)

theorem derived111950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3266) ∨ (¬ p 5558) ∨ (¬ p 3506) ∨ (¬ p 3425) ∨ (p 2717) ∨ (¬ p 2331) :=
  ElevenRUP.step111950 (p 2331) (p 2717) (p 3266) (p 3323) (p 3425) (p 3506) (p 4421) (p 5558) (derived108991 p h) (derived95302 p h)

theorem derived111955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3266) ∨ (¬ p 2331) ∨ (p 3461) ∨ (p 2619) ∨ (¬ p 3506) ∨ (¬ p 5568) ∨ (p 2132) :=
  ElevenRUP.step111955 (p 2132) (p 2331) (p 2619) (p 3266) (p 3323) (p 3461) (p 3506) (p 4421) (p 5568) (derived109255 p h) (derived95302 p h)

theorem derived111956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3266) ∨ (p 3461) ∨ (¬ p 3425) ∨ (p 2717) ∨ (¬ p 2331) ∨ (¬ p 3506) ∨ (¬ p 5558) :=
  ElevenRUP.step111956 (p 2331) (p 2717) (p 3266) (p 3323) (p 3425) (p 3461) (p 3506) (p 4421) (p 5558) (derived109256 p h) (derived95302 p h)

theorem derived111957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 2331) ∨ (p 3461) ∨ (¬ p 3506) ∨ (p 3246) ∨ (p 2132) ∨ (p 2870) :=
  ElevenRUP.step111957 (p 2132) (p 2331) (p 2870) (p 3246) (p 3323) (p 3461) (p 3506) (p 4421) (p 4621) (p 4786) (derived106425 p h) (derived105407 p h) (derived86784 p h) (derived95302 p h)

theorem derived111961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3246) ∨ (p 2210) ∨ (¬ p 2331) ∨ (¬ p 3506) ∨ (p 3461) ∨ (p 2166) ∨ (¬ p 3747) :=
  ElevenRUP.step111961 (p 2166) (p 2210) (p 2248) (p 2331) (p 3246) (p 3323) (p 3461) (p 3506) (p 3747) (p 4421) (p 4621) (derived105365 p h) (derived105407 p h) (derived75493 p h) (derived95302 p h)

theorem derived111962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 2528) ∨ (p 2651) ∨ (p 3461) ∨ (¬ p 2509) ∨ (¬ p 3506) ∨ (¬ p 3487) ∨ (¬ p 2641) :=
  ElevenRUP.step111962 (p 2249) (p 2509) (p 2528) (p 2641) (p 2651) (p 3323) (p 3461) (p 3487) (p 3506) (p 4330) (p 4421) (derived106513 p h) (derived106329 p h) (derived98162 p h) (derived95302 p h)

theorem derived111963 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3073) ∨ (p 3449) ∨ (p 3461) ∨ (¬ p 2331) ∨ (¬ p 3379) ∨ (¬ p 2753) ∨ (¬ p 3506) ∨ (¬ p 4117) :=
  ElevenRUP.step111963 (p 2331) (p 2753) (p 3073) (p 3323) (p 3379) (p 3449) (p 3461) (p 3506) (p 4117) (p 4330) (p 4421) (derived106329 p h) (derived99063 p h) (derived95302 p h)

theorem derived111964 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 2417) ∨ (p 2922) ∨ (p 2651) ∨ (¬ p 2641) ∨ (p 3461) ∨ (¬ p 3506) ∨ (¬ p 3487) :=
  ElevenRUP.step111964 (p 2249) (p 2417) (p 2641) (p 2651) (p 2922) (p 3323) (p 3461) (p 3487) (p 3506) (p 4421) (p 4621) (derived106513 p h) (derived105407 p h) (derived100073 p h) (derived95302 p h)

theorem derived111965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 2427) ∨ (¬ p 2331) ∨ (p 3461) ∨ (¬ p 3506) ∨ (p 3246) ∨ (¬ p 4117) ∨ (p 2230) :=
  ElevenRUP.step111965 (p 2230) (p 2331) (p 2427) (p 3246) (p 3323) (p 3461) (p 3506) (p 4117) (p 4421) (p 4621) (p 4729) (derived105407 p h) (derived105429 p h) (derived100741 p h) (derived95302 p h)

theorem derived111968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3506) ∨ (p 3051) ∨ (¬ p 2427) ∨ (¬ p 2331) ∨ (p 2982) ∨ (¬ p 4117) ∨ (p 3461) ∨ (¬ p 3904) ∨ (¬ p 4368) :=
  ElevenRUP.step111968 (p 2331) (p 2427) (p 2982) (p 3051) (p 3323) (p 3461) (p 3506) (p 3904) (p 4117) (p 4368) (p 4421) (p 4729) (derived105429 p h) (derived94561 p h) (derived95302 p h)

theorem derived111971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3461) ∨ (p 3399) ∨ (¬ p 2156) ∨ (¬ p 2608) ∨ (p 3631) ∨ (¬ p 3506) ∨ (¬ p 2246) ∨ (¬ p 2958) ∨ (¬ p 3745) :=
  ElevenRUP.step111971 (p 2156) (p 2246) (p 2608) (p 2744) (p 2958) (p 3323) (p 3399) (p 3461) (p 3506) (p 3631) (p 3745) (p 4421) (p 4621) (derived106503 p h) (derived105407 p h) (derived82339 p h) (derived95302 p h)

theorem derived111972 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 2098) ∨ (p 2132) :=
  ElevenRUP.step111972 (p 2098) (p 2132) (p 2619) (p 4359) (derived89708 p h) (derived96150 p h)

theorem derived111973 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3537) ∨ (p 2839) :=
  ElevenRUP.step111973 (p 2619) (p 2839) (p 3537) (p 4359) (derived89733 p h) (derived96150 p h)

theorem derived111974 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3537) ∨ (p 2132) ∨ (¬ p 3366) :=
  ElevenRUP.step111974 (p 2132) (p 2619) (p 3366) (p 3537) (p 4359) (derived89799 p h) (derived96150 p h)

theorem derived111975 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 3105) ∨ (¬ p 2532) :=
  ElevenRUP.step111975 (p 2532) (p 2619) (p 3105) (p 3609) (p 4359) (derived93737 p h) (derived96150 p h)

theorem derived111976 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3146) ∨ (¬ p 2220) ∨ (p 3609) :=
  ElevenRUP.step111976 (p 2220) (p 2619) (p 3146) (p 3609) (p 4359) (derived93739 p h) (derived96150 p h)

theorem derived111978 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (p 3609) ∨ (¬ p 2860) :=
  ElevenRUP.step111978 (p 2619) (p 2860) (p 3073) (p 3449) (p 3609) (p 4359) (derived93733 p h) (derived96150 p h)

theorem derived111979 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 3146) ∨ (p 2839) ∨ (p 2608) :=
  ElevenRUP.step111979 (p 2608) (p 2619) (p 2839) (p 3146) (p 3609) (p 4359) (derived93734 p h) (derived96150 p h)

theorem derived111980 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3156) ∨ (p 3609) ∨ (¬ p 3146) :=
  ElevenRUP.step111980 (p 2619) (p 3146) (p 3156) (p 3609) (p 4359) (p 4906) (derived105632 p h) (derived93738 p h) (derived96150 p h)

theorem derived111981 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 2088) ∨ (¬ p 2860) ∨ (¬ p 3696) :=
  ElevenRUP.step111981 (p 2088) (p 2619) (p 2860) (p 3609) (p 3696) (p 4359) (derived93742 p h) (derived96150 p h)

theorem derived111983 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3696) ∨ (¬ p 3998) ∨ (¬ p 2373) ∨ (¬ p 5612) :=
  ElevenRUP.step111983 (p 2373) (p 2619) (p 3696) (p 3998) (p 4359) (p 4882) (p 5612) (derived105453 p h) (derived61763 p h) (derived96150 p h)

theorem derived111984 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 2166) ∨ (¬ p 2088) ∨ (¬ p 3696) :=
  ElevenRUP.step111984 (p 2088) (p 2166) (p 2619) (p 3609) (p 3696) (p 4359) (p 4878) (derived105452 p h) (derived84610 p h) (derived96150 p h)

theorem derived111986 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 2088) ∨ (¬ p 3156) ∨ (¬ p 3696) :=
  ElevenRUP.step111986 (p 2088) (p 2619) (p 3156) (p 3609) (p 3696) (p 4359) (p 4906) (derived105632 p h) (derived93741 p h) (derived96150 p h)

theorem derived111987 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3073) ∨ (p 3609) ∨ (¬ p 3093) ∨ (¬ p 2870) ∨ (¬ p 4317) :=
  ElevenRUP.step111987 (p 2619) (p 2870) (p 3073) (p 3093) (p 3609) (p 4317) (p 4359) (derived93746 p h) (derived96150 p h)

theorem derived111993 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4044) ∨ (p 3609) ∨ (¬ p 3256) ∨ (p 2996) ∨ (¬ p 4392) :=
  ElevenRUP.step111993 (p 2619) (p 2751) (p 2996) (p 3256) (p 3609) (p 4044) (p 4359) (p 4392) (derived106343 p h) (derived86921 p h) (derived96150 p h)

theorem derived111996 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4688) ∨ (p 3609) ∨ (¬ p 3073) ∨ (¬ p 3695) ∨ (p 2922) :=
  ElevenRUP.step111996 (p 2619) (p 2922) (p 3073) (p 3609) (p 3695) (p 4359) (p 4644) (p 4688) (derived105411 p h) (derived95456 p h) (derived96150 p h)

theorem derived112000 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3537) ∨ (p 3073) ∨ (¬ p 2088) ∨ (¬ p 3096) ∨ (¬ p 2578) ∨ (¬ p 4114) ∨ (¬ p 2870) :=
  ElevenRUP.step112000 (p 2088) (p 2578) (p 2619) (p 2870) (p 3073) (p 3096) (p 3537) (p 4114) (p 4359) (derived109697 p h) (derived96150 p h)

theorem derived112001 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 3146) ∨ (¬ p 3093) ∨ (p 2132) ∨ (¬ p 2177) ∨ (¬ p 3309) :=
  ElevenRUP.step112001 (p 2132) (p 2177) (p 2619) (p 3093) (p 3146) (p 3309) (p 3609) (p 4359) (p 4736) (p 4905) (derived105431 p h) (derived105995 p h) (derived81825 p h) (derived96150 p h)

theorem derived112002 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3609) ∨ (¬ p 3146) ∨ (p 2132) ∨ (¬ p 2264) ∨ (p 2996) ∨ (¬ p 2241) :=
  ElevenRUP.step112002 (p 2132) (p 2241) (p 2264) (p 2619) (p 2996) (p 3146) (p 3609) (p 4359) (p 4736) (p 4905) (derived105431 p h) (derived105995 p h) (derived82135 p h) (derived96150 p h)

theorem derived112004 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 3146) ∨ (¬ p 3379) ∨ (p 2132) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (p 3609) :=
  ElevenRUP.step112004 (p 2132) (p 2619) (p 2911) (p 2922) (p 3146) (p 3379) (p 3609) (p 4359) (p 4736) (p 4905) (derived105431 p h) (derived105995 p h) (derived93747 p h) (derived96150 p h)

theorem derived112008 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 3156) ∨ (p 3609) ∨ (¬ p 5017) ∨ (¬ p 2088) ∨ (¬ p 2870) ∨ (¬ p 2190) ∨ (¬ p 4114) ∨ (p 2992) ∨ (p 2241) :=
  ElevenRUP.step112008 (p 2088) (p 2190) (p 2241) (p 2619) (p 2870) (p 2992) (p 3156) (p 3609) (p 4114) (p 4359) (p 4558) (p 5017) (derived105400 p h) (derived97130 p h) (derived96150 p h)

theorem derived112009 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (¬ p 4590) ∨ (p 3609) ∨ (p 2493) ∨ (p 3379) ∨ (¬ p 2860) ∨ (¬ p 2088) ∨ (¬ p 3660) ∨ (p 2427) :=
  ElevenRUP.step112009 (p 2088) (p 2427) (p 2493) (p 2619) (p 2860) (p 3379) (p 3609) (p 3660) (p 4359) (p 4555) (p 4590) (p 5207) (derived105542 p h) (derived105491 p h) (derived97203 p h) (derived96150 p h)

theorem derived112013 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 3670) ∨ (¬ p 5284) :=
  ElevenRUP.step112013 (p 3670) (p 3755) (p 5284) (p 5454) (derived96183 p h) (derived102612 p h)

theorem derived112018 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (p 3599) ∨ (¬ p 2737) ∨ (¬ p 3286) ∨ (p 2946) :=
  ElevenRUP.step112018 (p 2737) (p 2946) (p 3286) (p 3599) (p 3755) (p 5454) (derived96180 p h) (derived102612 p h)

theorem derived112023 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 3434) ∨ (p 3246) ∨ (p 2807) ∨ (¬ p 3286) :=
  ElevenRUP.step112023 (p 2807) (p 3246) (p 3286) (p 3434) (p 3755) (p 5454) (derived109609 p h) (derived102612 p h)

theorem derived112024 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 3323) ∨ (p 3461) ∨ (¬ p 3670) ∨ (p 3564) :=
  ElevenRUP.step112024 (p 3323) (p 3461) (p 3564) (p 3670) (p 3755) (p 5454) (derived111945 p h) (derived102612 p h)

theorem derived112035 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (p 3564) ∨ (p 3276) ∨ (¬ p 2274) ∨ (p 3125) ∨ (¬ p 3286) ∨ (¬ p 4117) ∨ (¬ p 3670) ∨ (p 2307) :=
  ElevenRUP.step112035 (p 2274) (p 2307) (p 3125) (p 3276) (p 3286) (p 3564) (p 3670) (p 3755) (p 4117) (p 5454) (derived110047 p h) (derived102612 p h)

theorem derived112039 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (p 3276) ∨ (p 2341) ∨ (p 2396) ∨ (¬ p 5260) ∨ (¬ p 4117) ∨ (¬ p 3670) ∨ (¬ p 4275) ∨ (¬ p 3286) ∨ (¬ p 2881) :=
  ElevenRUP.step112039 (p 2341) (p 2396) (p 2881) (p 3276) (p 3286) (p 3670) (p 3755) (p 4117) (p 4275) (p 4638) (p 5260) (p 5454) (derived105409 p h) (derived96177 p h) (derived102612 p h)

theorem derived112054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3073) ∨ (¬ p 3146) :=
  ElevenRUP.step112054 (p 2166) (p 3073) (p 3146) (p 4446) (derived93535 p h) (derived102418 p h)

theorem derived112056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (p 2210) ∨ (p 2373) :=
  ElevenRUP.step112056 (p 2166) (p 2210) (p 2373) (p 3449) (p 4446) (p 4632) (derived106257 p h) (derived76910 p h) (derived102418 p h)

theorem derived112058 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 4993) ∨ (p 2373) ∨ (¬ p 2563) ∨ (¬ p 2668) :=
  ElevenRUP.step112058 (p 2166) (p 2373) (p 2563) (p 2668) (p 4446) (p 4993) (derived79019 p h) (derived102418 p h)

theorem derived112059 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (¬ p 2284) ∨ (p 2241) ∨ (p 3156) :=
  ElevenRUP.step112059 (p 2166) (p 2241) (p 2284) (p 3156) (p 3449) (p 4446) (derived79069 p h) (derived102418 p h)

theorem derived112060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (p 2192) ∨ (p 2210) :=
  ElevenRUP.step112060 (p 2166) (p 2192) (p 2210) (p 3449) (p 4446) (p 4509) (derived105392 p h) (derived80075 p h) (derived102418 p h)

theorem derived112063 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (p 2210) ∨ (p 2619) :=
  ElevenRUP.step112063 (p 2166) (p 2210) (p 2619) (p 3449) (p 4446) (p 4878) (derived105452 p h) (derived84829 p h) (derived102418 p h)

theorem derived112067 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (p 2210) ∨ (¬ p 5053) ∨ (p 3156) ∨ (¬ p 4418) :=
  ElevenRUP.step112067 (p 2166) (p 2210) (p 3156) (p 3449) (p 4418) (p 4446) (p 5053) (derived80760 p h) (derived102418 p h)

theorem derived112069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 5590) ∨ (¬ p 3858) ∨ (¬ p 3941) ∨ (¬ p 3146) ∨ (¬ p 2177) :=
  ElevenRUP.step112069 (p 2166) (p 2177) (p 3146) (p 3858) (p 3941) (p 4446) (p 5590) (derived59273 p h) (derived102418 p h)

theorem derived112071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3073) ∨ (¬ p 2528) ∨ (¬ p 4355) ∨ (p 3156) :=
  ElevenRUP.step112071 (p 2166) (p 2528) (p 3073) (p 3156) (p 4355) (p 4446) (p 4702) (derived106079 p h) (derived93534 p h) (derived102418 p h)

theorem derived112086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (¬ p 3425) ∨ (p 2717) ∨ (p 2459) ∨ (¬ p 3366) ∨ (¬ p 3969) ∨ (p 2241) :=
  ElevenRUP.step112086 (p 2166) (p 2241) (p 2459) (p 2717) (p 2744) (p 3366) (p 3425) (p 3449) (p 3969) (p 4446) (p 5122) (derived106503 p h) (derived105483 p h) (derived97070 p h) (derived102418 p h)

theorem derived112087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 3201) ∨ (p 2417) ∨ (¬ p 3146) ∨ (p 2210) ∨ (¬ p 3449) ∨ (¬ p 3366) ∨ (p 2598) :=
  ElevenRUP.step112087 (p 2166) (p 2210) (p 2417) (p 2598) (p 3146) (p 3201) (p 3366) (p 3449) (p 4377) (p 4446) (p 4669) (derived105415 p h) (derived106170 p h) (derived100085 p h) (derived102418 p h)

theorem derived112088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2819) ∨ (p 2363) ∨ (p 2774) ∨ (p 2210) ∨ (¬ p 3449) ∨ (¬ p 3366) ∨ (¬ p 3969) :=
  ElevenRUP.step112088 (p 2166) (p 2210) (p 2363) (p 2774) (p 2819) (p 3366) (p 3449) (p 3969) (p 4377) (p 4446) (p 5122) (derived106170 p h) (derived105483 p h) (derived100838 p h) (derived102418 p h)

theorem derived112089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2819) ∨ (p 2363) ∨ (p 3379) ∨ (p 2774) ∨ (¬ p 3449) ∨ (¬ p 3366) ∨ (¬ p 3969) :=
  ElevenRUP.step112089 (p 2166) (p 2363) (p 2774) (p 2819) (p 3366) (p 3379) (p 3449) (p 3969) (p 4376) (p 4446) (p 5122) (derived106320 p h) (derived105483 p h) (derived100839 p h) (derived102418 p h)

theorem derived112091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2685) ∨ (p 2449) ∨ (p 2210) ∨ (¬ p 3146) ∨ (¬ p 3449) ∨ (¬ p 3366) ∨ (p 2696) :=
  ElevenRUP.step112091 (p 2166) (p 2210) (p 2449) (p 2685) (p 2696) (p 3146) (p 3366) (p 3449) (p 4377) (p 4446) (p 4669) (derived105415 p h) (derived106170 p h) (derived101627 p h) (derived102418 p h)

theorem derived112094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2417) ∨ (¬ p 3683) ∨ (p 2210) ∨ (p 3201) ∨ (¬ p 3146) ∨ (¬ p 3449) ∨ (¬ p 3366) ∨ (¬ p 4236) ∨ (p 2651) :=
  ElevenRUP.step112094 (p 2166) (p 2210) (p 2417) (p 2651) (p 3146) (p 3201) (p 3366) (p 3449) (p 3683) (p 4236) (p 4377) (p 4446) (p 4669) (derived105415 p h) (derived106170 p h) (derived100062 p h) (derived102418 p h)

theorem derived112095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3449) ∨ (p 3564) ∨ (p 3422) ∨ (p 2651) ∨ (p 2210) ∨ (¬ p 3146) ∨ (¬ p 3366) ∨ (¬ p 4236) ∨ (¬ p 3683) :=
  ElevenRUP.step112095 (p 2166) (p 2210) (p 2651) (p 3146) (p 3366) (p 3422) (p 3449) (p 3564) (p 3683) (p 4236) (p 4377) (p 4446) (p 4604) (derived106293 p h) (derived106170 p h) (derived101454 p h) (derived102418 p h)

theorem derived112096 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 2459) ∨ (¬ p 3256) :=
  ElevenRUP.step112096 (p 2264) (p 2459) (p 3256) (p 4548) (derived75187 p h) (derived95329 p h)

theorem derived112098 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3189) ∨ (¬ p 2177) ∨ (p 2996) :=
  ElevenRUP.step112098 (p 2177) (p 2264) (p 2996) (p 3189) (p 4548) (derived81972 p h) (derived95329 p h)

theorem derived112100 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3166) ∨ (¬ p 2807) ∨ (¬ p 2177) :=
  ElevenRUP.step112100 (p 2177) (p 2264) (p 2807) (p 3166) (p 4548) (derived101948 p h) (derived95329 p h)

theorem derived112101 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3189) ∨ (¬ p 2881) ∨ (p 2996) :=
  ElevenRUP.step112101 (p 2264) (p 2881) (p 2996) (p 3189) (p 4280) (p 4548) (derived105599 p h) (derived81965 p h) (derived95329 p h)

theorem derived112104 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2449) ∨ (¬ p 2807) ∨ (p 3166) :=
  ElevenRUP.step112104 (p 2264) (p 2449) (p 2807) (p 3166) (p 4548) (p 4668) (derived105414 p h) (derived86553 p h) (derived95329 p h)

theorem derived112105 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2449) ∨ (p 3005) ∨ (¬ p 2685) :=
  ElevenRUP.step112105 (p 2264) (p 2449) (p 2685) (p 3005) (p 4548) (p 4668) (derived105414 p h) (derived89041 p h) (derived95329 p h)

theorem derived112106 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3005) ∨ (¬ p 2881) ∨ (¬ p 2685) :=
  ElevenRUP.step112106 (p 2264) (p 2685) (p 2881) (p 3005) (p 4280) (p 4548) (derived105599 p h) (derived89067 p h) (derived95329 p h)

theorem derived112107 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3527) ∨ (¬ p 2685) ∨ (¬ p 3040) ∨ (p 3005) :=
  ElevenRUP.step112107 (p 2264) (p 2685) (p 3005) (p 3040) (p 3527) (p 4548) (derived89068 p h) (derived95329 p h)

theorem derived112108 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3931) ∨ (¬ p 5564) ∨ (¬ p 2685) ∨ (p 3005) :=
  ElevenRUP.step112108 (p 2264) (p 2685) (p 3005) (p 3931) (p 4548) (p 5564) (derived89077 p h) (derived95329 p h)

theorem derived112109 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3166) ∨ (¬ p 2807) ∨ (¬ p 2911) :=
  ElevenRUP.step112109 (p 2264) (p 2807) (p 2911) (p 3166) (p 4327) (p 4548) (derived105381 p h) (derived95143 p h) (derived95329 p h)

theorem derived112112 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3166) ∨ (p 2797) ∨ (¬ p 2331) ∨ (¬ p 2630) :=
  ElevenRUP.step112112 (p 2264) (p 2331) (p 2630) (p 2797) (p 3166) (p 4548) (derived101578 p h) (derived95329 p h)

theorem derived112113 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2911) ∨ (p 3166) ∨ (¬ p 2651) ∨ (p 2630) :=
  ElevenRUP.step112113 (p 2264) (p 2630) (p 2651) (p 2911) (p 3166) (p 4548) (derived101949 p h) (derived95329 p h)

theorem derived112114 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3166) ∨ (¬ p 2807) ∨ (¬ p 2881) :=
  ElevenRUP.step112114 (p 2264) (p 2807) (p 2881) (p 3166) (p 4280) (p 4548) (derived105599 p h) (derived101956 p h) (derived95329 p h)

theorem derived112120 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3246) ∨ (¬ p 3657) ∨ (p 3005) ∨ (¬ p 2685) :=
  ElevenRUP.step112120 (p 2264) (p 2685) (p 3005) (p 3246) (p 3657) (p 4280) (p 4548) (derived105599 p h) (derived89038 p h) (derived95329 p h)

theorem derived112122 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3005) ∨ (¬ p 2630) ∨ (p 2651) ∨ (¬ p 2911) ∨ (¬ p 4236) :=
  ElevenRUP.step112122 (p 2264) (p 2630) (p 2651) (p 2911) (p 3005) (p 4236) (p 4548) (derived98136 p h) (derived95329 p h)

theorem derived112126 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 4009) ∨ (¬ p 3961) ∨ (¬ p 2177) ∨ (¬ p 5590) :=
  ElevenRUP.step112126 (p 2177) (p 2264) (p 2315) (p 3961) (p 4009) (p 4548) (p 5590) (derived105368 p h) (derived58246 p h) (derived95329 p h)

theorem derived112136 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2177) ∨ (¬ p 2252) ∨ (p 2331) ∨ (¬ p 3146) ∨ (¬ p 2373) ∨ (¬ p 2230) ∨ (p 3005) ∨ (¬ p 3519) ∨ (¬ p 2797) ∨ (¬ p 2741) :=
  ElevenRUP.step112136 (p 2177) (p 2230) (p 2252) (p 2264) (p 2331) (p 2373) (p 2741) (p 2797) (p 3005) (p 3146) (p 3519) (p 4376) (p 4548) (derived106320 p h) (derived101091 p h) (derived95329 p h)

theorem derived112138 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3858) ∨ (¬ p 3177) :=
  ElevenRUP.step112138 (p 3177) (p 3189) (p 3858) (p 5074) (h 35060) (derived87329 p h)

theorem derived112139 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 4009) ∨ (¬ p 4181) :=
  ElevenRUP.step112139 (p 3189) (p 4009) (p 4181) (p 5074) (h 40760) (derived87329 p h)

theorem derived112140 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 3073) ∨ (p 3256) :=
  ElevenRUP.step112140 (p 3073) (p 3189) (p 3256) (p 5074) (derived110468 p h) (derived87329 p h)

theorem derived112141 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3449) ∨ (¬ p 3166) ∨ (¬ p 2253) :=
  ElevenRUP.step112141 (p 2253) (p 3166) (p 3189) (p 3449) (p 5074) (derived100024 p h) (derived87329 p h)

theorem derived112144 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 3005) ∨ (p 3449) ∨ (¬ p 2241) :=
  ElevenRUP.step112144 (p 2241) (p 2745) (p 3005) (p 3189) (p 3449) (p 5074) (derived105523 p h) (derived80608 p h) (derived87329 p h)

theorem derived112145 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 4318) ∨ (p 2187) ∨ (p 2331) ∨ (¬ p 3166) :=
  ElevenRUP.step112145 (p 2187) (p 2331) (p 3166) (p 3189) (p 4318) (p 5074) (derived92355 p h) (derived87329 p h)

theorem derived112147 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 3527) ∨ (p 2911) ∨ (p 2807) ∨ (¬ p 3166) :=
  ElevenRUP.step112147 (p 2807) (p 2911) (p 3166) (p 3189) (p 3527) (p 5074) (derived111029 p h) (derived87329 p h)

theorem derived112149 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 4687) ∨ (p 3641) ∨ (p 2651) ∨ (¬ p 3166) :=
  ElevenRUP.step112149 (p 2651) (p 3166) (p 3189) (p 3641) (p 4687) (p 4750) (p 5074) (derived105433 p h) (derived95419 p h) (derived87329 p h)

theorem derived112151 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3449) ∨ (¬ p 2748) ∨ (¬ p 2241) ∨ (¬ p 2630) :=
  ElevenRUP.step112151 (p 2241) (p 2630) (p 2748) (p 3189) (p 3449) (p 5008) (p 5074) (derived105469 p h) (derived101518 p h) (derived87329 p h)

theorem derived112164 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 5503) ∨ (¬ p 3266) ∨ (¬ p 3166) ∨ (p 2727) ∨ (¬ p 2662) ∨ (p 3389) ∨ (¬ p 3073) :=
  ElevenRUP.step112164 (p 2255) (p 2662) (p 2727) (p 3073) (p 3166) (p 3189) (p 3266) (p 3389) (p 4831) (p 5074) (p 5503) (derived105367 p h) (derived105445 p h) (derived76593 p h) (derived87329 p h)

theorem derived112168 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 2363) ∨ (p 3051) ∨ (p 2992) ∨ (¬ p 3166) ∨ (¬ p 3073) ∨ (¬ p 2957) ∨ (p 2881) :=
  ElevenRUP.step112168 (p 2255) (p 2363) (p 2881) (p 2957) (p 2992) (p 3051) (p 3073) (p 3166) (p 3189) (p 4133) (p 5074) (derived105367 p h) (derived105712 p h) (derived80191 p h) (derived87329 p h)

theorem derived112169 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 3449) ∨ (p 2449) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 2241) ∨ (¬ p 2839) ∨ (¬ p 4044) :=
  ElevenRUP.step112169 (p 2241) (p 2449) (p 2750) (p 2839) (p 2870) (p 2881) (p 3189) (p 3449) (p 4044) (p 4666) (p 5074) (derived106345 p h) (derived105658 p h) (derived83769 p h) (derived87329 p h)

theorem derived112173 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 5506) ∨ (¬ p 4149) ∨ (p 3449) ∨ (p 3425) ∨ (¬ p 2717) ∨ (¬ p 2753) ∨ (¬ p 5600) ∨ (¬ p 2241) ∨ (p 2177) :=
  ElevenRUP.step112173 (p 2177) (p 2241) (p 2717) (p 2753) (p 3189) (p 3425) (p 3449) (p 4149) (p 5074) (p 5506) (p 5600) (derived108762 p h) (derived87329 p h)

theorem derived112183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2177) ∨ (p 2911) ∨ (p 2449) :=
  ElevenRUP.step112183 (p 2177) (p 2417) (p 2449) (p 2911) (p 3192) (derived111709 p h) (derived96425 p h)

theorem derived112185 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 5558) ∨ (¬ p 5600) :=
  ElevenRUP.step112185 (p 2264) (p 4378) (p 5558) (p 5600) (h 30915) (derived96456 p h)

theorem derived112187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 3256) ∨ (¬ p 2459) :=
  ElevenRUP.step112187 (p 2264) (p 2459) (p 3256) (p 4378) (h 40560) (derived96456 p h)

theorem derived112196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3189) ∨ (p 2177) ∨ (¬ p 2651) ∨ (p 2727) :=
  ElevenRUP.step112196 (p 2177) (p 2264) (p 2651) (p 2727) (p 3189) (p 4378) (derived91893 p h) (derived96456 p h)

theorem derived112197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3189) ∨ (¬ p 2996) ∨ (¬ p 4653) ∨ (p 2911) :=
  ElevenRUP.step112197 (p 2264) (p 2911) (p 2996) (p 3189) (p 4378) (p 4653) (derived91966 p h) (derived96456 p h)

theorem derived112202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3005) ∨ (p 2685) ∨ (p 2449) :=
  ElevenRUP.step112202 (p 2264) (p 2449) (p 2685) (p 3005) (p 4378) (p 4666) (derived105658 p h) (derived100160 p h) (derived96456 p h)

theorem derived112203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2996) ∨ (p 3527) ∨ (p 2807) ∨ (¬ p 3166) :=
  ElevenRUP.step112203 (p 2264) (p 2807) (p 2996) (p 3166) (p 3527) (p 4378) (derived109376 p h) (derived96456 p h)

theorem derived112210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2619) ∨ (p 2870) ∨ (p 2911) ∨ (¬ p 4312) :=
  ElevenRUP.step112210 (p 2264) (p 2619) (p 2870) (p 2911) (p 4277) (p 4312) (p 4378) (derived105380 p h) (derived86675 p h) (derived96456 p h)

theorem derived112211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3189) ∨ (p 2177) ∨ (¬ p 2331) ∨ (p 2641) ∨ (¬ p 2253) :=
  ElevenRUP.step112211 (p 2177) (p 2253) (p 2264) (p 2331) (p 2641) (p 3189) (p 4378) (derived92005 p h) (derived96456 p h)

theorem derived112214 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 3256) ∨ (¬ p 3325) ∨ (¬ p 2363) ∨ (p 2911) :=
  ElevenRUP.step112214 (p 2264) (p 2363) (p 2911) (p 3256) (p 3325) (p 4276) (p 4378) (derived105516 p h) (derived101399 p h) (derived96456 p h)

theorem derived112215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 3256) ∨ (¬ p 2996) ∨ (¬ p 3842) ∨ (p 2911) ∨ (¬ p 4653) :=
  ElevenRUP.step112215 (p 2264) (p 2911) (p 2996) (p 3256) (p 3842) (p 4378) (p 4653) (derived111102 p h) (derived96456 p h)

theorem derived112217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 4189) ∨ (¬ p 3177) ∨ (p 2088) ∨ (¬ p 4914) ∨ (p 2881) ∨ (¬ p 3073) :=
  ElevenRUP.step112217 (p 2088) (p 2264) (p 2881) (p 3073) (p 3177) (p 4189) (p 4378) (p 4914) (derived80200 p h) (derived96456 p h)

theorem derived112230 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 4371) ∨ (¬ p 4105) :=
  ElevenRUP.step112230 (p 3527) (p 3544) (p 4105) (p 4371) (h 28047) (derived102269 p h)

theorem derived112231 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3449) ∨ (p 3399) :=
  ElevenRUP.step112231 (p 3399) (p 3449) (p 3527) (p 3544) (h 27565) (derived102269 p h)

theorem derived112233 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2341) ∨ (¬ p 3543) ∨ (¬ p 3542) :=
  ElevenRUP.step112233 (p 2341) (p 3527) (p 3542) (p 3543) (p 3544) (h 5164) (derived102269 p h)

theorem derived112234 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3073) ∨ (¬ p 2459) ∨ (p 3399) ∨ (¬ p 2241) :=
  ElevenRUP.step112234 (p 2241) (p 2459) (p 3073) (p 3399) (p 3527) (p 3544) (derived91613 p h) (derived102269 p h)

theorem derived112235 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2717) ∨ (¬ p 2459) ∨ (¬ p 4794) ∨ (p 3073) :=
  ElevenRUP.step112235 (p 2459) (p 2717) (p 3073) (p 3527) (p 3544) (p 4794) (derived91624 p h) (derived102269 p h)

theorem derived112238 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 4075) ∨ (¬ p 4372) ∨ (¬ p 2363) ∨ (p 3073) :=
  ElevenRUP.step112238 (p 2363) (p 3073) (p 3527) (p 3544) (p 4075) (p 4372) (derived97257 p h) (derived102269 p h)

theorem derived112239 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3073) ∨ (p 3399) ∨ (¬ p 2459) ∨ (¬ p 2608) :=
  ElevenRUP.step112239 (p 2459) (p 2608) (p 3073) (p 3399) (p 3527) (p 3544) (derived99036 p h) (derived102269 p h)

theorem derived112240 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2459) ∨ (p 3073) ∨ (¬ p 4911) ∨ (¬ p 2881) :=
  ElevenRUP.step112240 (p 2459) (p 2881) (p 3073) (p 3527) (p 3544) (p 4911) (derived99044 p h) (derived102269 p h)

theorem derived112241 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 4372) ∨ (¬ p 4075) ∨ (p 3073) ∨ (¬ p 3146) :=
  ElevenRUP.step112241 (p 3073) (p 3146) (p 3527) (p 3544) (p 4075) (p 4372) (derived99087 p h) (derived102269 p h)

theorem derived112242 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3073) ∨ (¬ p 2598) ∨ (¬ p 3425) ∨ (¬ p 2459) ∨ (¬ p 3576) :=
  ElevenRUP.step112242 (p 2459) (p 2598) (p 3073) (p 3425) (p 3527) (p 3544) (p 3576) (derived88582 p h) (derived102269 p h)

theorem derived112243 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 5693) ∨ (¬ p 2881) ∨ (¬ p 2933) ∨ (¬ p 3941) :=
  ElevenRUP.step112243 (p 2881) (p 2933) (p 3527) (p 3544) (p 3941) (p 4277) (p 5693) (derived105380 p h) (derived41768 p h) (derived102269 p h)

theorem derived112245 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2911) ∨ (p 3073) ∨ (¬ p 4138) ∨ (¬ p 2363) :=
  ElevenRUP.step112245 (p 2363) (p 2911) (p 2930) (p 3073) (p 3527) (p 3544) (p 4138) (derived105376 p h) (derived91623 p h) (derived102269 p h)

theorem derived112246 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3031) ∨ (p 3073) ∨ (¬ p 3256) ∨ (¬ p 3166) :=
  ElevenRUP.step112246 (p 2255) (p 3031) (p 3073) (p 3166) (p 3256) (p 3527) (p 3544) (derived105367 p h) (derived91625 p h) (derived102269 p h)

theorem derived112247 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2619) ∨ (¬ p 5693) ∨ (¬ p 3969) ∨ (¬ p 3554) :=
  ElevenRUP.step112247 (p 2619) (p 3527) (p 3544) (p 3554) (p 3969) (p 4875) (p 5693) (derived106227 p h) (derived41763 p h) (derived102269 p h)

end ElevenLogic
