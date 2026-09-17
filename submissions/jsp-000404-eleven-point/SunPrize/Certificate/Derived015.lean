import SunPrize.Certificate.Derived014
import SunPrize.Certificate.Logic015
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived54050 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 3549) ∨ (¬ p 3550) ∨ (¬ p 4107) ∨ (¬ p 4666) :=
  ElevenRUP.step54050 (p 2027) (p 3063) (p 3549) (p 3550) (p 4107) (p 4666) (derived40810 p h) (h 27716)

theorem derived54055 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 3402) ∨ (¬ p 4137) :=
  ElevenRUP.step54055 (p 1977) (p 2027) (p 2499) (p 2997) (p 3097) (p 3125) (p 3402) (p 4137) (h 2137) (derived40810 p h) (derived40890 p h) (h 27722)

theorem derived54056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 3055) ∨ (¬ p 3238) ∨ (¬ p 3362) ∨ (¬ p 5214) :=
  ElevenRUP.step54056 (p 2027) (p 2230) (p 3055) (p 3238) (p 3362) (p 5214) (derived40810 p h) (h 27724)

theorem derived54060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2717) ∨ (¬ p 2952) ∨ (¬ p 3952) ∨ (¬ p 3989) ∨ (¬ p 4503) :=
  ElevenRUP.step54060 (p 2027) (p 2254) (p 2608) (p 2707) (p 2717) (p 2952) (p 3952) (p 3989) (p 4503) (derived40810 p h) (h 27728)

theorem derived54061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2363) ∨ (¬ p 3027) ∨ (¬ p 4340) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54061 (p 2027) (p 2104) (p 2241) (p 2264) (p 2363) (p 3027) (p 4340) (p 4503) (p 4736) (derived40810 p h) (h 27729)

theorem derived54066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2589) ∨ (¬ p 3363) ∨ (¬ p 3471) ∨ (¬ p 3527) ∨ (¬ p 3585) ∨ (¬ p 4235) ∨ (¬ p 4424) ∨ (¬ p 4559) ∨ (¬ p 4737) :=
  ElevenRUP.step54066 (p 2027) (p 2299) (p 2589) (p 3363) (p 3471) (p 3527) (p 3585) (p 4235) (p 4424) (p 4559) (p 4737) (derived40810 p h) (h 27734)

theorem derived54070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3105) ∨ (¬ p 4244) :=
  ElevenRUP.step54070 (p 2011) (p 2027) (p 2210) (p 2699) (p 2891) (p 3105) (p 4244) (h 2171) (derived40810 p h) (derived40881 p h) (h 27739)

theorem derived54076 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2459) ∨ (¬ p 3986) ∨ (¬ p 4037) ∨ (¬ p 4133) ∨ (¬ p 4171) :=
  ElevenRUP.step54076 (p 2027) (p 2187) (p 2459) (p 3986) (p 4037) (p 4133) (p 4171) (derived40810 p h) (h 27748)

theorem derived54077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 3379) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4149) ∨ (¬ p 4348) ∨ (¬ p 4736) ∨ (¬ p 5122) :=
  ElevenRUP.step54077 (p 2027) (p 2518) (p 3379) (p 3425) (p 3659) (p 4149) (p 4348) (p 4736) (p 5122) (derived40810 p h) (h 27749)

theorem derived54078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3644) ∨ (¬ p 3868) ∨ (¬ p 4133) ∨ (¬ p 4441) ∨ (¬ p 5562) ∨ (¬ p 5568) :=
  ElevenRUP.step54078 (p 2027) (p 3644) (p 3868) (p 4133) (p 4441) (p 5562) (p 5568) (derived40810 p h) (h 27750)

theorem derived54080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3552) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4620) :=
  ElevenRUP.step54080 (p 2027) (p 3027) (p 3552) (p 4037) (p 4154) (p 4620) (derived40810 p h) (h 27752)

theorem derived54081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2553) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 2881) ∨ (¬ p 3016) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4559) :=
  ElevenRUP.step54081 (p 2027) (p 2246) (p 2553) (p 2651) (p 2744) (p 2881) (p 3016) (p 3366) (p 3425) (p 3659) (p 4559) (derived40810 p h) (h 27753)

theorem derived54087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 4111) :=
  ElevenRUP.step54087 (p 1977) (p 2027) (p 2462) (p 2651) (p 3414) (p 3947) (p 4111) (h 2137) (derived40810 p h) (derived40875 p h) (h 27760)

theorem derived54088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 3956) ∨ (¬ p 4111) ∨ (¬ p 4347) :=
  ElevenRUP.step54088 (p 1977) (p 2027) (p 2579) (p 2662) (p 2766) (p 3956) (p 4111) (p 4347) (h 2137) (derived40810 p h) (derived40884 p h) (h 27761)

theorem derived54094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2440) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 3324) ∨ (¬ p 4116) ∨ (¬ p 4154) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54094 (p 1984) (p 2027) (p 2202) (p 2247) (p 2440) (p 2518) (p 2528) (p 3324) (p 4116) (p 4154) (p 4348) (p 4503) (h 2144) (derived40810 p h) (derived40867 p h) (h 27767)

theorem derived54096 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 3005) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 3880) ∨ (¬ p 4195) ∨ (¬ p 5063) :=
  ElevenRUP.step54096 (p 2027) (p 2248) (p 2331) (p 3005) (p 3238) (p 3452) (p 3880) (p 4195) (p 5063) (derived40810 p h) (h 27770)

theorem derived54097 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3699) ∨ (¬ p 4555) :=
  ElevenRUP.step54097 (p 2027) (p 2284) (p 2992) (p 2996) (p 3699) (p 4555) (derived40810 p h) (h 27771)

theorem derived54099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step54099 (p 2027) (p 2363) (p 2774) (p 2819) (p 2928) (p 3452) (p 4278) (p 4669) (p 4733) (derived40810 p h) (h 27774)

theorem derived54102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 3880) ∨ (¬ p 4348) ∨ (¬ p 4905) :=
  ElevenRUP.step54102 (p 1984) (p 2027) (p 2363) (p 2641) (p 2668) (p 2688) (p 3238) (p 3452) (p 3880) (p 4348) (p 4905) (h 2144) (derived40810 p h) (derived40880 p h) (h 27778)

theorem derived54107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2737) ∨ (¬ p 3551) ∨ (¬ p 3820) ∨ (¬ p 4734) ∨ (¬ p 4781) :=
  ElevenRUP.step54107 (p 2027) (p 2717) (p 2737) (p 3551) (p 3820) (p 4734) (p 4781) (derived40810 p h) (h 27783)

theorem derived54110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2881) ∨ (¬ p 3551) ∨ (¬ p 4107) ∨ (¬ p 4155) ∨ (¬ p 4559) :=
  ElevenRUP.step54110 (p 2027) (p 2449) (p 2881) (p 3551) (p 4107) (p 4155) (p 4559) (derived40810 p h) (h 27786)

theorem derived54111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2972) ∨ (¬ p 3369) ∨ (¬ p 4032) ∨ (¬ p 5568) :=
  ElevenRUP.step54111 (p 1984) (p 2027) (p 2191) (p 2972) (p 3369) (p 3982) (p 4032) (p 5568) (h 2144) (derived40810 p h) (derived40909 p h) (h 27787)

theorem derived54113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3574) ∨ (¬ p 3585) ∨ (¬ p 4343) :=
  ElevenRUP.step54113 (p 1976) (p 2027) (p 2737) (p 3008) (p 3365) (p 3574) (p 3585) (p 4343) (h 2136) (derived40810 p h) (derived40891 p h) (h 27789)

theorem derived54115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2249) ∨ (¬ p 2499) ∨ (¬ p 2657) ∨ (¬ p 3027) ∨ (¬ p 3171) ∨ (¬ p 3487) ∨ (¬ p 3956) ∨ (¬ p 4044) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54115 (p 2027) (p 2088) (p 2249) (p 2499) (p 2657) (p 3027) (p 3171) (p 3487) (p 3956) (p 4044) (p 4348) (p 4503) (derived40810 p h) (h 27791)

theorem derived54117 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2499) ∨ (¬ p 3146) ∨ (¬ p 3452) ∨ (¬ p 3956) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4521) :=
  ElevenRUP.step54117 (p 2027) (p 2220) (p 2499) (p 3146) (p 3452) (p 3956) (p 4348) (p 4503) (p 4521) (derived40810 p h) (h 27793)

theorem derived54120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2499) ∨ (¬ p 2807) ∨ (¬ p 3256) ∨ (¬ p 3452) ∨ (¬ p 3956) ∨ (¬ p 4044) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54120 (p 2027) (p 2248) (p 2499) (p 2807) (p 3256) (p 3452) (p 3956) (p 4044) (p 4348) (p 4503) (derived40810 p h) (h 27796)

theorem derived54127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 2839) :=
  ElevenRUP.step54127 (p 1994) (p 2027) (p 2114) (p 2138) (p 2630) (p 2696) (p 2839) (h 2154) (derived40810 p h) (derived40864 p h) (h 27803)

theorem derived54129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3358) ∨ (¬ p 4322) ∨ (¬ p 4355) ∨ (¬ p 4385) ∨ (¬ p 4882) :=
  ElevenRUP.step54129 (p 2027) (p 3276) (p 3358) (p 4322) (p 4355) (p 4385) (p 4882) (derived40810 p h) (h 27805)

theorem derived54130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2717) ∨ (¬ p 3989) ∨ (¬ p 4110) ∨ (¬ p 4503) ∨ (¬ p 5193) :=
  ElevenRUP.step54130 (p 2027) (p 2589) (p 2608) (p 2707) (p 2717) (p 3989) (p 4110) (p 4503) (p 5193) (derived40810 p h) (h 27806)

theorem derived54135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3989) ∨ (¬ p 4110) ∨ (¬ p 4503) ∨ (¬ p 5193) :=
  ElevenRUP.step54135 (p 2027) (p 2241) (p 2264) (p 2589) (p 3027) (p 3989) (p 4110) (p 4503) (p 5193) (derived40810 p h) (h 27814)

theorem derived54141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 4009) ∨ (¬ p 4118) ∨ (¬ p 4434) ∨ (¬ p 5568) :=
  ElevenRUP.step54141 (p 2027) (p 2528) (p 4009) (p 4118) (p 4434) (p 5568) (derived40810 p h) (h 27822)

theorem derived54149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2363) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3347) ∨ (¬ p 3402) ∨ (¬ p 4503) :=
  ElevenRUP.step54149 (p 2027) (p 2132) (p 2363) (p 2476) (p 2534) (p 2750) (p 2753) (p 2870) (p 2881) (p 3347) (p 3402) (p 4503) (derived40810 p h) (h 27832)

theorem derived54151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2542) ∨ (¬ p 3389) ∨ (¬ p 3742) :=
  ElevenRUP.step54151 (p 1997) (p 2027) (p 2476) (p 2542) (p 3389) (p 3498) (p 3742) (h 2157) (derived40810 p h) (derived40899 p h) (h 27836)

theorem derived54156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2655) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4116) ∨ (¬ p 4787) :=
  ElevenRUP.step54156 (p 2027) (p 2630) (p 2655) (p 2922) (p 3540) (p 4116) (p 4787) (derived40810 p h) (h 27844)

theorem derived54157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3083) ∨ (¬ p 3572) ∨ (¬ p 3879) ∨ (¬ p 4156) ∨ (¬ p 4336) ∨ (¬ p 4610) :=
  ElevenRUP.step54157 (p 2027) (p 2630) (p 3083) (p 3572) (p 3879) (p 4156) (p 4336) (p 4610) (derived40810 p h) (h 27845)

theorem derived54162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2459) ∨ (¬ p 2534) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 3954) ∨ (¬ p 4186) ∨ (¬ p 4902) ∨ (¬ p 5216) :=
  ElevenRUP.step54162 (p 2027) (p 2166) (p 2210) (p 2459) (p 2534) (p 3347) (p 3540) (p 3954) (p 4186) (p 4902) (p 5216) (derived40810 p h) (h 27850)

theorem derived54164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2946) ∨ (¬ p 3983) ∨ (¬ p 4563) :=
  ElevenRUP.step54164 (p 2027) (p 2295) (p 2313) (p 2946) (p 3983) (p 4563) (derived40810 p h) (h 27852)

theorem derived54173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2241) ∨ (¬ p 3548) ∨ (¬ p 4366) :=
  ElevenRUP.step54173 (p 1977) (p 2027) (p 2177) (p 2241) (p 2997) (p 3548) (p 4366) (h 2137) (derived40810 p h) (derived40890 p h) (h 27861)

theorem derived54175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2363) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3027) ∨ (¬ p 3688) ∨ (¬ p 4078) ∨ (¬ p 4340) ∨ (¬ p 4503) ∨ (¬ p 4737) :=
  ElevenRUP.step54175 (p 2027) (p 2264) (p 2363) (p 2696) (p 2742) (p 3027) (p 3688) (p 4078) (p 4340) (p 4503) (p 4737) (derived40810 p h) (h 27864)

theorem derived54182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3555) ∨ (¬ p 3989) ∨ (¬ p 4173) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step54182 (p 2027) (p 2598) (p 2911) (p 3201) (p 3555) (p 3989) (p 4173) (p 4503) (p 4733) (derived40810 p h) (h 27871)

theorem derived54184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3555) ∨ (¬ p 3989) ∨ (¬ p 4173) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 5190) :=
  ElevenRUP.step54184 (p 2027) (p 2470) (p 2528) (p 3555) (p 3989) (p 4173) (p 4348) (p 4503) (p 5190) (derived40810 p h) (h 27875)

theorem derived54188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2749) ∨ (¬ p 3166) ∨ (¬ p 3256) :=
  ElevenRUP.step54188 (p 1982) (p 2027) (p 2114) (p 2657) (p 2727) (p 2749) (p 3166) (p 3256) (h 2142) (derived40810 p h) (derived40864 p h) (h 27879)

theorem derived54190 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2850) ∨ (¬ p 3952) ∨ (¬ p 4109) ∨ (¬ p 4700) ∨ (¬ p 4753) :=
  ElevenRUP.step54190 (p 2027) (p 2156) (p 2850) (p 3952) (p 4109) (p 4700) (p 4753) (derived40810 p h) (h 27881)

theorem derived54192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2891) ∨ (¬ p 4363) ∨ (¬ p 4382) ∨ (¬ p 4556) :=
  ElevenRUP.step54192 (p 2027) (p 2396) (p 2891) (p 4363) (p 4382) (p 4556) (derived40810 p h) (h 27884)

theorem derived54195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 3767) ∨ (¬ p 4444) ∨ (¬ p 5295) :=
  ElevenRUP.step54195 (p 1982) (p 2027) (p 2633) (p 3246) (p 3570) (p 3767) (p 4444) (p 5295) (h 2142) (derived40810 p h) (derived40879 p h) (h 27887)

theorem derived54197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2534) ∨ (¬ p 3189) ∨ (¬ p 3256) :=
  ElevenRUP.step54197 (p 2007) (p 2027) (p 2241) (p 2534) (p 2699) (p 3189) (p 3256) (h 2167) (derived40810 p h) (derived40881 p h) (h 27892)

theorem derived54198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2363) ∨ (¬ p 3821) ∨ (¬ p 4445) ∨ (¬ p 4503) :=
  ElevenRUP.step54198 (p 2027) (p 2341) (p 2363) (p 3821) (p 4445) (p 4503) (derived40810 p h) (h 27894)

theorem derived54200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2363) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3688) ∨ (¬ p 3740) ∨ (¬ p 4078) ∨ (¬ p 4340) ∨ (¬ p 4503) ∨ (¬ p 4737) :=
  ElevenRUP.step54200 (p 2027) (p 2264) (p 2363) (p 2598) (p 3201) (p 3688) (p 3740) (p 4078) (p 4340) (p 4503) (p 4737) (derived40810 p h) (h 27898)

theorem derived54202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2901) ∨ (¬ p 3556) ∨ (¬ p 4110) ∨ (¬ p 4705) :=
  ElevenRUP.step54202 (p 2027) (p 2156) (p 2901) (p 3556) (p 4110) (p 4705) (derived40810 p h) (h 27900)

theorem derived54203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2509) ∨ (¬ p 3156) ∨ (¬ p 3693) ∨ (¬ p 4705) :=
  ElevenRUP.step54203 (p 2027) (p 2406) (p 2509) (p 3156) (p 3693) (p 4705) (derived40810 p h) (h 27901)

theorem derived54204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 2901) ∨ (¬ p 3246) ∨ (¬ p 4278) ∨ (¬ p 4705) :=
  ElevenRUP.step54204 (p 2027) (p 2441) (p 2901) (p 3246) (p 4278) (p 4705) (derived40810 p h) (h 27902)

theorem derived54207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3661) ∨ (¬ p 3691) ∨ (¬ p 3767) ∨ (¬ p 4349) ∨ (¬ p 4702) ∨ (¬ p 5284) ∨ (¬ p 5300) :=
  ElevenRUP.step54207 (p 2027) (p 2427) (p 3661) (p 3691) (p 3767) (p 4349) (p 4702) (p 5284) (p 5300) (derived40810 p h) (h 27905)

theorem derived54208 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2363) ∨ (¬ p 3027) ∨ (¬ p 3646) ∨ (¬ p 3692) ∨ (¬ p 3988) ∨ (¬ p 4503) ∨ (¬ p 4524) :=
  ElevenRUP.step54208 (p 2027) (p 2241) (p 2264) (p 2363) (p 3027) (p 3646) (p 3692) (p 3988) (p 4503) (p 4524) (derived40810 p h) (h 27906)

theorem derived54209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3985) ∨ (¬ p 3989) ∨ (¬ p 4244) ∨ (¬ p 4555) :=
  ElevenRUP.step54209 (p 2027) (p 2819) (p 3985) (p 3989) (p 4244) (p 4555) (derived40810 p h) (h 27907)

theorem derived54212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3019) ∨ (¬ p 3347) ∨ (¬ p 4811) :=
  ElevenRUP.step54212 (p 2027) (p 2295) (p 2579) (p 2588) (p 3019) (p 3347) (p 4811) (derived40810 p h) (h 27910)

theorem derived54213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2952) ∨ (¬ p 3879) ∨ (¬ p 4322) ∨ (¬ p 4948) :=
  ElevenRUP.step54213 (p 1994) (p 2027) (p 2651) (p 2764) (p 2952) (p 3879) (p 4322) (p 4948) (h 2154) (derived40810 p h) (derived40882 p h) (h 27911)

theorem derived54217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2255) ∨ (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3956) ∨ (¬ p 4111) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54217 (p 2027) (p 2255) (p 2579) (p 2662) (p 3166) (p 3256) (p 3956) (p 4111) (p 4348) (p 4503) (derived40810 p h) (h 27915)

theorem derived54220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2406) ∨ (¬ p 2440) ∨ (¬ p 3379) :=
  ElevenRUP.step54220 (p 1994) (p 2027) (p 2247) (p 2406) (p 2440) (p 2688) (p 3379) (h 2154) (derived40810 p h) (derived40880 p h) (h 27918)

theorem derived54221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3136) ∨ (¬ p 4241) ∨ (¬ p 4715) :=
  ElevenRUP.step54221 (p 2027) (p 2579) (p 2662) (p 2810) (p 3136) (p 4241) (p 4715) (derived40810 p h) (h 27919)

theorem derived54222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 3422) :=
  ElevenRUP.step54222 (p 1998) (p 2027) (p 2579) (p 2842) (p 2911) (p 3389) (p 3422) (h 2158) (derived40810 p h) (derived40885 p h) (h 27920)

theorem derived54223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3389) ∨ (¬ p 3422) ∨ (¬ p 3742) ∨ (¬ p 4753) :=
  ElevenRUP.step54223 (p 2027) (p 2579) (p 3389) (p 3422) (p 3742) (p 4753) (derived40810 p h) (h 27921)

theorem derived54231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 4235) :=
  ElevenRUP.step54231 (p 1992) (p 2027) (p 2608) (p 2938) (p 3238) (p 3452) (p 4235) (h 2152) (derived40810 p h) (derived40888 p h) (h 27930)

theorem derived54233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3083) ∨ (¬ p 3742) ∨ (¬ p 4348) ∨ (¬ p 4370) :=
  ElevenRUP.step54233 (p 1998) (p 2027) (p 2914) (p 3073) (p 3083) (p 3742) (p 4348) (p 4370) (h 2158) (derived40810 p h) (derived40887 p h) (h 27932)

theorem derived54235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3324) ∨ (¬ p 3365) ∨ (¬ p 3379) ∨ (¬ p 4195) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54235 (p 2027) (p 2911) (p 2922) (p 3324) (p 3365) (p 3379) (p 4195) (p 4503) (p 4736) (derived40810 p h) (h 27934)

theorem derived54237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 3367) ∨ (¬ p 3683) ∨ (¬ p 3877) ∨ (¬ p 5008) :=
  ElevenRUP.step54237 (p 2027) (p 2743) (p 3367) (p 3683) (p 3877) (p 5008) (derived40810 p h) (h 27936)

theorem derived54238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2901) ∨ (¬ p 2911) ∨ (¬ p 3548) ∨ (¬ p 3952) ∨ (¬ p 4366) ∨ (¬ p 4521) ∨ (¬ p 4647) :=
  ElevenRUP.step54238 (p 2027) (p 2156) (p 2901) (p 2911) (p 3548) (p 3952) (p 4366) (p 4521) (p 4647) (derived40810 p h) (h 27937)

theorem derived54241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 4315) :=
  ElevenRUP.step54241 (p 1976) (p 2027) (p 2388) (p 2743) (p 3055) (p 3367) (p 4315) (h 2136) (derived40810 p h) (derived40873 p h) (h 27940)

theorem derived54242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 2743) ∨ (¬ p 2881) ∨ (¬ p 3434) ∨ (¬ p 3690) :=
  ElevenRUP.step54242 (p 1998) (p 2027) (p 2622) (p 2707) (p 2743) (p 2881) (p 3434) (p 3690) (h 2158) (derived40810 p h) (derived40878 p h) (h 27941)

theorem derived54243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2657) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3574) ∨ (¬ p 3956) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54243 (p 2027) (p 2254) (p 2657) (p 3073) (p 3449) (p 3574) (p 3956) (p 4348) (p 4503) (derived40810 p h) (h 27942)

theorem derived54245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 3692) :=
  ElevenRUP.step54245 (p 2001) (p 2027) (p 2148) (p 2156) (p 2187) (p 2363) (p 3692) (h 2161) (derived40810 p h) (derived40865 p h) (h 27944)

theorem derived54246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2579) ∨ (¬ p 2992) ∨ (¬ p 3115) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 4450) ∨ (¬ p 5193) :=
  ElevenRUP.step54246 (p 2027) (p 2241) (p 2579) (p 2992) (p 3115) (p 3956) (p 4347) (p 4450) (p 5193) (derived40810 p h) (h 27946)

theorem derived54247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 3969) ∨ (¬ p 4381) ∨ (¬ p 5119) :=
  ElevenRUP.step54247 (p 2027) (p 2166) (p 2210) (p 2254) (p 3414) (p 3947) (p 3969) (p 4381) (p 5119) (derived40810 p h) (h 27947)

theorem derived54250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2363) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 4503) ∨ (¬ p 5193) :=
  ElevenRUP.step54250 (p 2027) (p 2210) (p 2363) (p 2476) (p 2534) (p 2881) (p 2891) (p 4503) (p 5193) (derived40810 p h) (h 27950)

theorem derived54251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4107) :=
  ElevenRUP.step54251 (p 2000) (p 2027) (p 2177) (p 2462) (p 3540) (p 3644) (p 4107) (h 2160) (derived40810 p h) (derived40875 p h) (h 27951)

theorem derived54252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2668) ∨ (¬ p 3019) ∨ (¬ p 3688) ∨ (¬ p 4358) :=
  ElevenRUP.step54252 (p 1992) (p 2027) (p 2202) (p 2440) (p 2668) (p 3019) (p 3688) (p 4358) (h 2152) (derived40810 p h) (derived40867 p h) (h 27952)

theorem derived54253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 3641) ∨ (¬ p 3876) ∨ (¬ p 3905) ∨ (¬ p 4278) :=
  ElevenRUP.step54253 (p 1976) (p 2027) (p 2462) (p 2476) (p 3641) (p 3876) (p 3905) (p 4278) (h 2136) (derived40810 p h) (derived40875 p h) (h 27953)

theorem derived54256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2363) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 2963) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4503) :=
  ElevenRUP.step54256 (p 2027) (p 2210) (p 2254) (p 2363) (p 2881) (p 2891) (p 2963) (p 4118) (p 4196) (p 4503) (derived40810 p h) (h 27956)

theorem derived54257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3324) ∨ (¬ p 4345) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54257 (p 2027) (p 3323) (p 3324) (p 4345) (p 4348) (p 4503) (derived40810 p h) (h 27957)

theorem derived54258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 3389) :=
  ElevenRUP.step54258 (p 2010) (p 2027) (p 2476) (p 2534) (p 3146) (p 3389) (p 3578) (h 2170) (derived40810 p h) (derived40900 p h) (h 27958)

theorem derived54259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2829) ∨ (¬ p 3097) ∨ (¬ p 3583) ∨ (¬ p 4328) :=
  ElevenRUP.step54259 (p 1990) (p 2027) (p 2295) (p 2829) (p 3097) (p 3474) (p 3583) (p 4328) (h 2150) (derived40810 p h) (derived40898 p h) (h 27959)

theorem derived54261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2588) ∨ (¬ p 2657) ∨ (¬ p 3574) :=
  ElevenRUP.step54261 (p 1991) (p 2027) (p 2274) (p 2588) (p 2657) (p 2765) (p 3574) (h 2151) (derived40810 p h) (derived40883 p h) (h 27961)

theorem derived54264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 2963) ∨ (¬ p 3005) :=
  ElevenRUP.step54264 (p 1993) (p 2027) (p 2287) (p 2651) (p 2810) (p 2963) (p 3005) (h 2153) (derived40810 p h) (derived40869 p h) (h 27967)

theorem derived54265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 2274) ∨ (¬ p 2528) ∨ (¬ p 3452) ∨ (¬ p 3453) ∨ (¬ p 4261) ∨ (¬ p 4438) ∨ (¬ p 4521) :=
  ElevenRUP.step54265 (p 2027) (p 2156) (p 2177) (p 2274) (p 2528) (p 3452) (p 3453) (p 4261) (p 4438) (p 4521) (derived40810 p h) (h 27968)

theorem derived54274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 4129) ∨ (¬ p 4386) ∨ (¬ p 4391) ∨ (¬ p 4702) :=
  ElevenRUP.step54274 (p 2027) (p 2427) (p 4129) (p 4386) (p 4391) (p 4702) (derived40810 p h) (h 27981)

theorem derived54277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2247) ∨ (¬ p 3324) ∨ (¬ p 3609) ∨ (¬ p 4154) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step54277 (p 2027) (p 2098) (p 2247) (p 3324) (p 3609) (p 4154) (p 4348) (p 4503) (p 4733) (derived40810 p h) (h 27985)

theorem derived54280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2406) ∨ (¬ p 2598) ∨ (¬ p 3698) ∨ (¬ p 5217) :=
  ElevenRUP.step54280 (p 2027) (p 2138) (p 2406) (p 2598) (p 3698) (p 5217) (derived40810 p h) (h 27989)

theorem derived54283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2780) ∨ (¬ p 2911) ∨ (¬ p 3367) ∨ (¬ p 3389) ∨ (¬ p 3759) ∨ (¬ p 4078) ∨ (¬ p 4340) ∨ (¬ p 4503) ∨ (¬ p 4734) :=
  ElevenRUP.step54283 (p 2027) (p 2363) (p 2780) (p 2911) (p 3367) (p 3389) (p 3759) (p 4078) (p 4340) (p 4503) (p 4734) (derived40810 p h) (h 27992)

theorem derived54293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 3555) ∨ (¬ p 3609) ∨ (¬ p 3989) ∨ (¬ p 4173) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step54293 (p 2027) (p 2098) (p 3555) (p 3609) (p 3989) (p 4173) (p 4348) (p 4503) (p 4733) (derived40810 p h) (h 28004)

theorem derived54298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2449) ∨ (¬ p 2995) ∨ (¬ p 3952) ∨ (¬ p 4278) ∨ (¬ p 4710) :=
  ElevenRUP.step54298 (p 1998) (p 2027) (p 2177) (p 2449) (p 2765) (p 2995) (p 3952) (p 4278) (p 4710) (h 2158) (derived40810 p h) (derived40883 p h) (h 28011)

theorem derived54300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 2911) ∨ (¬ p 3389) :=
  ElevenRUP.step54300 (p 1975) (p 2027) (p 2299) (p 2622) (p 2630) (p 2656) (p 2911) (p 3389) (h 2135) (derived40810 p h) (derived40878 p h) (h 28013)

theorem derived54302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2427) ∨ (¬ p 2608) ∨ (¬ p 2881) ∨ (¬ p 3031) ∨ (¬ p 3519) ∨ (¬ p 3817) ∨ (¬ p 4376) ∨ (¬ p 4666) :=
  ElevenRUP.step54302 (p 2027) (p 2230) (p 2247) (p 2427) (p 2608) (p 2881) (p 3031) (p 3519) (p 3817) (p 4376) (p 4666) (derived40810 p h) (h 28015)

theorem derived54304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2608) ∨ (¬ p 2881) ∨ (¬ p 3519) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4376) ∨ (¬ p 4503) :=
  ElevenRUP.step54304 (p 2027) (p 2230) (p 2427) (p 2608) (p 2881) (p 3519) (p 3591) (p 3923) (p 4376) (p 4503) (derived40810 p h) (h 28017)

theorem derived54307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2881) ∨ (¬ p 3309) ∨ (¬ p 3690) ∨ (¬ p 4338) :=
  ElevenRUP.step54307 (p 1998) (p 2027) (p 2396) (p 2873) (p 2881) (p 3309) (p 3690) (p 4338) (h 2158) (derived40810 p h) (derived40886 p h) (h 28020)

theorem derived54312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 3527) ∨ (¬ p 3817) :=
  ElevenRUP.step54312 (p 1998) (p 2027) (p 2417) (p 2437) (p 2545) (p 3527) (p 3817) (h 2158) (derived40810 p h) (derived40876 p h) (h 28025)

theorem derived54313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3585) ∨ (¬ p 3876) :=
  ElevenRUP.step54313 (p 1976) (p 2027) (p 2437) (p 2545) (p 2737) (p 3365) (p 3585) (p 3876) (h 2136) (derived40810 p h) (derived40876 p h) (h 28026)

theorem derived54315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2245) ∨ (¬ p 2363) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 2963) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step54315 (p 2027) (p 2132) (p 2245) (p 2363) (p 2870) (p 2881) (p 2963) (p 4118) (p 4196) (p 4503) (p 4733) (derived40810 p h) (h 28030)

theorem derived54316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3189) ∨ (¬ p 3662) ∨ (¬ p 4348) ∨ (¬ p 4417) :=
  ElevenRUP.step54316 (p 1998) (p 2027) (p 2363) (p 2388) (p 3189) (p 3662) (p 4348) (p 4417) (h 2158) (derived40810 p h) (derived40873 p h) (h 28031)

theorem derived54317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3324) ∨ (¬ p 4154) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 5190) :=
  ElevenRUP.step54317 (p 2027) (p 2247) (p 2470) (p 2528) (p 3324) (p 4154) (p 4348) (p 4503) (p 5190) (derived40810 p h) (h 28033)

theorem derived54321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3097) ∨ (¬ p 3555) ∨ (¬ p 4173) ∨ (¬ p 4405) ∨ (¬ p 4733) :=
  ElevenRUP.step54321 (p 2027) (p 2668) (p 2696) (p 2797) (p 3097) (p 3555) (p 4173) (p 4405) (p 4733) (derived40810 p h) (h 28039)

theorem derived54322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2589) ∨ (¬ p 3506) ∨ (¬ p 3690) ∨ (¬ p 4117) ∨ (¬ p 4191) ∨ (¬ p 4235) ∨ (¬ p 4421) ∨ (¬ p 4621) ∨ (¬ p 4729) :=
  ElevenRUP.step54322 (p 2027) (p 2331) (p 2589) (p 3506) (p 3690) (p 4117) (p 4191) (p 4235) (p 4421) (p 4621) (p 4729) (derived40810 p h) (h 28040)

theorem derived54328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3324) ∨ (¬ p 3365) ∨ (¬ p 4079) ∨ (¬ p 4195) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54328 (p 2027) (p 2470) (p 2528) (p 3324) (p 3365) (p 4079) (p 4195) (p 4348) (p 4503) (p 4736) (derived40810 p h) (h 28050)

theorem derived54329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2590) ∨ (¬ p 3654) ∨ (¬ p 3743) ∨ (¬ p 4137) ∨ (¬ p 4705) :=
  ElevenRUP.step54329 (p 2027) (p 2284) (p 2590) (p 3654) (p 3743) (p 4137) (p 4705) (derived40810 p h) (h 28051)

theorem derived54331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2441) ∨ (¬ p 2901) ∨ (¬ p 3644) ∨ (¬ p 3691) ∨ (¬ p 4705) :=
  ElevenRUP.step54331 (p 2027) (p 2341) (p 2441) (p 2901) (p 3644) (p 3691) (p 4705) (derived40810 p h) (h 28053)

theorem derived54333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3156) ∨ (¬ p 3693) ∨ (¬ p 3874) ∨ (¬ p 4705) :=
  ElevenRUP.step54333 (p 2027) (p 2850) (p 3156) (p 3693) (p 3874) (p 4705) (derived40810 p h) (h 28055)

theorem derived54336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 3644) ∨ (¬ p 4705) :=
  ElevenRUP.step54336 (p 2027) (p 2441) (p 2881) (p 2901) (p 3644) (p 4705) (derived40810 p h) (h 28058)

theorem derived54337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2363) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3172) ∨ (¬ p 3379) ∨ (¬ p 4118) ∨ (¬ p 4503) :=
  ElevenRUP.step54337 (p 2027) (p 2254) (p 2363) (p 2911) (p 2922) (p 3172) (p 3379) (p 4118) (p 4503) (derived40810 p h) (h 28059)

theorem derived54341 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2255) ∨ (¬ p 2363) ∨ (¬ p 2651) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3177) ∨ (¬ p 3857) ∨ (¬ p 4116) ∨ (¬ p 4360) ∨ (¬ p 4503) :=
  ElevenRUP.step54341 (p 2027) (p 2255) (p 2363) (p 2651) (p 2911) (p 2922) (p 3177) (p 3857) (p 4116) (p 4360) (p 4503) (derived40810 p h) (h 28064)

theorem derived54342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3156) ∨ (¬ p 3688) ∨ (¬ p 3954) ∨ (¬ p 4042) ∨ (¬ p 4320) ∨ (¬ p 4358) ∨ (¬ p 4503) ∨ (¬ p 4521) :=
  ElevenRUP.step54342 (p 2027) (p 3051) (p 3156) (p 3688) (p 3954) (p 4042) (p 4320) (p 4358) (p 4503) (p 4521) (derived40810 p h) (h 28065)

theorem derived54343 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2750) ∨ (¬ p 3166) ∨ (¬ p 3954) ∨ (¬ p 4360) :=
  ElevenRUP.step54343 (p 2027) (p 2253) (p 2750) (p 3166) (p 3954) (p 4360) (derived40810 p h) (h 28066)

theorem derived54345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2749) ∨ (¬ p 2992) ∨ (¬ p 3585) ∨ (¬ p 3589) ∨ (¬ p 4315) :=
  ElevenRUP.step54345 (p 1987) (p 2027) (p 2598) (p 2699) (p 2749) (p 2992) (p 3585) (p 3589) (p 4315) (h 2147) (derived40810 p h) (derived40881 p h) (h 28068)

theorem derived54346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2274) ∨ (¬ p 2313) ∨ (¬ p 3583) ∨ (¬ p 3989) ∨ (¬ p 4198) :=
  ElevenRUP.step54346 (p 1992) (p 2027) (p 2143) (p 2169) (p 2274) (p 2313) (p 3583) (p 3989) (p 4198) (h 2152) (derived40810 p h) (derived40866 p h) (h 28069)

theorem derived54348 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3758) ∨ (¬ p 3989) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54348 (p 2027) (p 2138) (p 3073) (p 3449) (p 3758) (p 3989) (p 4348) (p 4503) (p 4736) (derived40810 p h) (h 28071)

theorem derived54349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3758) ∨ (¬ p 3989) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54349 (p 2027) (p 2138) (p 2911) (p 2922) (p 3379) (p 3758) (p 3989) (p 4503) (p 4736) (derived40810 p h) (h 28072)

theorem derived54351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3692) ∨ (¬ p 4120) ∨ (¬ p 4503) ∨ (¬ p 4524) :=
  ElevenRUP.step54351 (p 2027) (p 2363) (p 2911) (p 2922) (p 3379) (p 3692) (p 4120) (p 4503) (p 4524) (derived40810 p h) (h 28074)

theorem derived54352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2787) ∨ (¬ p 2946) ∨ (¬ p 3644) ∨ (¬ p 3755) ∨ (¬ p 4117) ∨ (¬ p 4315) ∨ (¬ p 4348) ∨ (¬ p 4710) ∨ (¬ p 5109) :=
  ElevenRUP.step54352 (p 2027) (p 2313) (p 2787) (p 2946) (p 3644) (p 3755) (p 4117) (p 4315) (p 4348) (p 4710) (p 5109) (derived40810 p h) (h 28075)

theorem derived54353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2498) ∨ (¬ p 2749) ∨ (¬ p 2946) ∨ (¬ p 3005) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 3956) ∨ (¬ p 4315) ∨ (¬ p 4771) ∨ (¬ p 5216) :=
  ElevenRUP.step54353 (p 2027) (p 2246) (p 2498) (p 2749) (p 2946) (p 3005) (p 3379) (p 3591) (p 3956) (p 4315) (p 4771) (p 5216) (derived40810 p h) (h 28076)

theorem derived54355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 4066) ∨ (¬ p 4235) ∨ (¬ p 4283) ∨ (¬ p 4315) ∨ (¬ p 4705) :=
  ElevenRUP.step54355 (p 2027) (p 2685) (p 4066) (p 4235) (p 4283) (p 4315) (p 4705) (derived40810 p h) (h 28080)

theorem derived54357 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3051) ∨ (¬ p 4120) ∨ (¬ p 4244) :=
  ElevenRUP.step54357 (p 2006) (p 2027) (p 2166) (p 2873) (p 3051) (p 4120) (p 4244) (h 2166) (derived40810 p h) (derived40886 p h) (h 28082)

theorem derived54361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3324) ∨ (¬ p 4154) ∨ (¬ p 4503) ∨ (¬ p 5190) :=
  ElevenRUP.step54361 (p 2027) (p 2230) (p 2247) (p 2427) (p 2881) (p 3324) (p 4154) (p 4503) (p 5190) (derived40810 p h) (h 28086)

theorem derived54363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 3923) ∨ (¬ p 4345) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step54363 (p 2027) (p 3319) (p 3923) (p 4345) (p 4348) (p 4503) (derived40810 p h) (h 28088)

theorem derived54364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4503) :=
  ElevenRUP.step54364 (p 2027) (p 2241) (p 2598) (p 2750) (p 2753) (p 2911) (p 3201) (p 3591) (p 3923) (p 4503) (derived40810 p h) (h 28089)

theorem derived54366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 2810) ∨ (¬ p 2963) ∨ (¬ p 3286) ∨ (¬ p 5177) :=
  ElevenRUP.step54366 (p 2027) (p 2797) (p 2810) (p 2963) (p 3286) (p 5177) (derived40810 p h) (h 28091)

theorem derived54367 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2797) ∨ (¬ p 2963) ∨ (¬ p 3877) ∨ (¬ p 4041) ∨ (¬ p 4236) ∨ (¬ p 4348) ∨ (¬ p 4419) :=
  ElevenRUP.step54367 (p 2027) (p 2470) (p 2528) (p 2797) (p 2963) (p 3877) (p 4041) (p 4236) (p 4348) (p 4419) (derived40810 p h) (h 28092)

theorem derived54371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2386) ∨ (¬ p 2406) ∨ (¬ p 2499) ∨ (¬ p 3743) ∨ (¬ p 4705) :=
  ElevenRUP.step54371 (p 2027) (p 2284) (p 2386) (p 2406) (p 2499) (p 3743) (p 4705) (derived40810 p h) (h 28098)

theorem derived54373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3690) :=
  ElevenRUP.step54373 (p 1991) (p 2027) (p 2462) (p 2881) (p 3414) (p 3553) (p 3690) (h 2151) (derived40810 p h) (derived40875 p h) (h 28100)

theorem derived54374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 2786) ∨ (¬ p 2819) ∨ (¬ p 3822) ∨ (¬ p 3880) ∨ (¬ p 4134) ∨ (¬ p 4789) :=
  ElevenRUP.step54374 (p 2027) (p 2307) (p 2440) (p 2657) (p 2786) (p 2819) (p 3822) (p 3880) (p 4134) (p 4789) (derived40810 p h) (h 28101)

theorem derived54375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 2737) ∨ (¬ p 3759) ∨ (¬ p 4257) ∨ (¬ p 4749) :=
  ElevenRUP.step54375 (p 2027) (p 2499) (p 2573) (p 2737) (p 3759) (p 4257) (p 4749) (derived40810 p h) (h 28104)

theorem derived54376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3949) ∨ (¬ p 3969) ∨ (¬ p 4208) ∨ (¬ p 5122) :=
  ElevenRUP.step54376 (p 2027) (p 3156) (p 3949) (p 3969) (p 4208) (p 5122) (derived40810 p h) (h 28105)

theorem derived54378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 3690) :=
  ElevenRUP.step54378 (p 1985) (p 2027) (p 2608) (p 2699) (p 2707) (p 3434) (p 3690) (h 2145) (derived40810 p h) (derived40881 p h) (h 28107)

theorem derived54382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2584) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 3654) ∨ (¬ p 4137) :=
  ElevenRUP.step54382 (p 1975) (p 2027) (p 2553) (p 2584) (p 2622) (p 2630) (p 2656) (p 3654) (p 4137) (h 2135) (derived40810 p h) (derived40878 p h) (h 28112)

theorem derived54384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2319) ∨ (¬ p 2341) ∨ (¬ p 2441) ∨ (¬ p 3644) ∨ (¬ p 3743) ∨ (¬ p 4705) :=
  ElevenRUP.step54384 (p 2027) (p 2284) (p 2319) (p 2341) (p 2441) (p 3644) (p 3743) (p 4705) (derived40810 p h) (h 28114)

theorem derived54385 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) ∨ (¬ p 3414) ∨ (¬ p 3644) ∨ (¬ p 4653) ∨ (¬ p 5074) ∨ (¬ p 5307) :=
  ElevenRUP.step54385 (p 2027) (p 3166) (p 3414) (p 3644) (p 4653) (p 5074) (p 5307) (derived40810 p h) (h 28115)

theorem derived54386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2406) ∨ (¬ p 2982) ∨ (¬ p 3379) ∨ (¬ p 4348) ∨ (¬ p 4450) ∨ (¬ p 5021) :=
  ElevenRUP.step54386 (p 2027) (p 2299) (p 2313) (p 2406) (p 2982) (p 3379) (p 4348) (p 4450) (p 5021) (derived40810 p h) (h 28116)

theorem derived54389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 4232) ∨ (¬ p 5026) ∨ (¬ p 5043) :=
  ElevenRUP.step54389 (p 2027) (p 2132) (p 2860) (p 4232) (p 5026) (p 5043) (derived40810 p h) (h 28119)

theorem derived54390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2911) ∨ (¬ p 3389) :=
  ElevenRUP.step54390 (p 1982) (p 2027) (p 2459) (p 2656) (p 2688) (p 2727) (p 2911) (p 3389) (h 2142) (derived40810 p h) (derived40880 p h) (h 28120)

theorem derived54391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2972) ∨ (¬ p 3412) ∨ (¬ p 3680) ∨ (¬ p 3952) ∨ (¬ p 4444) :=
  ElevenRUP.step54391 (p 1982) (p 2027) (p 2765) (p 2972) (p 3412) (p 3680) (p 3952) (p 4444) (h 2142) (derived40810 p h) (derived40883 p h) (h 28121)

theorem derived54392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3055) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4666) ∨ (¬ p 4736) :=
  ElevenRUP.step54392 (p 2027) (p 2210) (p 2881) (p 2891) (p 3055) (p 3876) (p 4278) (p 4666) (p 4736) (derived40810 p h) (h 28122)

theorem derived54393 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3551) ∨ (¬ p 3588) ∨ (¬ p 3959) ∨ (¬ p 5558) :=
  ElevenRUP.step54393 (p 1987) (p 2027) (p 2737) (p 3551) (p 3588) (p 3959) (p 3982) (p 5558) (h 2147) (derived40810 p h) (derived40909 p h) (h 28125)

theorem derived54397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2911) ∨ (¬ p 3548) ∨ (¬ p 4366) :=
  ElevenRUP.step54397 (p 1992) (p 2027) (p 2608) (p 2911) (p 2914) (p 3548) (p 4366) (h 2152) (derived40810 p h) (derived40887 p h) (h 28129)

theorem derived54398 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 2891) ∨ (¬ p 2911) ∨ (¬ p 3347) ∨ (¬ p 3551) ∨ (¬ p 3741) ∨ (¬ p 4110) ∨ (¬ p 4257) ∨ (¬ p 4558) ∨ (¬ p 5197) :=
  ElevenRUP.step54398 (p 2027) (p 2210) (p 2247) (p 2744) (p 2891) (p 2911) (p 3347) (p 3551) (p 3741) (p 4110) (p 4257) (p 4558) (p 5197) (derived40810 p h) (h 28130)

theorem derived54399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4669) ∨ (¬ p 4786) :=
  ElevenRUP.step54399 (p 2027) (p 2138) (p 2331) (p 2363) (p 2668) (p 3690) (p 4244) (p 4669) (p 4786) (derived40810 p h) (h 28131)

theorem derived54400 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2807) ∨ (¬ p 3506) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4381) ∨ (¬ p 4661) ∨ (¬ p 4786) :=
  ElevenRUP.step54400 (p 2027) (p 2138) (p 2807) (p 3506) (p 3692) (p 3694) (p 3950) (p 4381) (p 4661) (p 4786) (derived40810 p h) (h 28132)

theorem derived54402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3573) ∨ (¬ p 3979) ∨ (¬ p 4286) ∨ (¬ p 5225) :=
  ElevenRUP.step54402 (p 2027) (p 2819) (p 3573) (p 3979) (p 4286) (p 5225) (derived40810 p h) (h 28135)

theorem derived54403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2284) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2946) ∨ (¬ p 3125) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4330) :=
  ElevenRUP.step54403 (p 2027) (p 2246) (p 2284) (p 2608) (p 2744) (p 2946) (p 3125) (p 3860) (p 4261) (p 4330) (derived40810 p h) (h 28140)

theorem derived54412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3680) ∨ (¬ p 4391) ∨ (¬ p 4419) ∨ (¬ p 4831) :=
  ElevenRUP.step54412 (p 2027) (p 2230) (p 2982) (p 3365) (p 3572) (p 3680) (p 4391) (p 4419) (p 4831) (derived40810 p h) (h 28152)

theorem derived54414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2657) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3570) ∨ (¬ p 3584) ∨ (¬ p 3683) ∨ (¬ p 4137) ∨ (¬ p 4236) ∨ (¬ p 4377) ∨ (¬ p 4625) ∨ (¬ p 4988) :=
  ElevenRUP.step54414 (p 2027) (p 2341) (p 2657) (p 3246) (p 3366) (p 3370) (p 3570) (p 3584) (p 3683) (p 4137) (p 4236) (p 4377) (p 4625) (p 4988) (derived40810 p h) (h 28154)

theorem derived54417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3483) ∨ (¬ p 3905) ∨ (¬ p 4137) ∨ (¬ p 4358) :=
  ElevenRUP.step54417 (p 1976) (p 2027) (p 2169) (p 2579) (p 3483) (p 3905) (p 4137) (p 4358) (h 2136) (derived40810 p h) (derived40866 p h) (h 28158)

theorem derived54418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 3587) ∨ (¬ p 3690) ∨ (¬ p 3952) ∨ (¬ p 4316) ∨ (¬ p 4558) :=
  ElevenRUP.step54418 (p 2027) (p 3434) (p 3587) (p 3690) (p 3952) (p 4316) (p 4558) (derived40810 p h) (h 28160)

theorem derived54419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2220) ∨ (¬ p 2891) ∨ (¬ p 3646) ∨ (¬ p 4558) :=
  ElevenRUP.step54419 (p 2027) (p 2191) (p 2220) (p 2891) (p 3646) (p 4558) (derived40810 p h) (h 28161)

theorem derived54420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 3857) ∨ (¬ p 3961) ∨ (¬ p 5258) :=
  ElevenRUP.step54420 (p 2027) (p 2459) (p 2717) (p 3857) (p 3961) (p 5258) (derived40810 p h) (h 28162)

theorem derived54424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2586) ∨ (¬ p 3016) ∨ (¬ p 4256) ∨ (¬ p 4432) :=
  ElevenRUP.step54424 (p 2027) (p 2383) (p 2586) (p 3016) (p 4256) (p 4432) (derived40810 p h) (h 28167)

theorem derived54428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2588) ∨ (¬ p 3574) ∨ (¬ p 5558) :=
  ElevenRUP.step54428 (p 1994) (p 2027) (p 2299) (p 2588) (p 3574) (p 3982) (p 5558) (h 2154) (derived40810 p h) (derived40909 p h) (h 28173)

theorem derived54429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2299) ∨ (¬ p 2780) ∨ (¬ p 2946) ∨ (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3822) ∨ (¬ p 4237) ∨ (¬ p 4736) ∨ (¬ p 4902) :=
  ElevenRUP.step54429 (p 2027) (p 2253) (p 2299) (p 2780) (p 2946) (p 3256) (p 3692) (p 3822) (p 4237) (p 4736) (p 4902) (derived40810 p h) (h 28174)

theorem derived54430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3125) ∨ (¬ p 3946) ∨ (¬ p 4198) ∨ (¬ p 4558) :=
  ElevenRUP.step54430 (p 2027) (p 3051) (p 3125) (p 3946) (p 4198) (p 4558) (derived40810 p h) (h 28175)

theorem derived54439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (¬ p 4133) ∨ (¬ p 4340) ∨ (¬ p 4786) :=
  ElevenRUP.step54439 (p 2027) (p 2104) (p 2352) (p 2459) (p 2651) (p 3016) (p 4133) (p 4340) (p 4786) (derived40810 p h) (h 28186)

theorem derived54442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2518) ∨ (¬ p 2608) ∨ (¬ p 4108) ∨ (¬ p 4376) :=
  ElevenRUP.step54442 (p 2027) (p 2476) (p 2518) (p 2608) (p 4108) (p 4376) (derived40810 p h) (h 28189)

theorem derived54444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3055) ∨ (¬ p 3644) ∨ (¬ p 3876) :=
  ElevenRUP.step54444 (p 1976) (p 2027) (p 2881) (p 2938) (p 3055) (p 3644) (p 3876) (h 2136) (derived40810 p h) (derived40888 p h) (h 28192)

theorem derived54448 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2668) ∨ (p 4973) :=
  ElevenRUP.step54448 (p 1982) (p 2363) (p 2668) (p 3008) (p 4973) (h 2142) (derived40891 p h) (h 28196)

theorem derived54449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 3055) ∨ (¬ p 3471) :=
  ElevenRUP.step54449 (p 1982) (p 2027) (p 2459) (p 2717) (p 2842) (p 3055) (p 3471) (h 2142) (derived40810 p h) (derived40885 p h) (h 28198)

theorem derived54451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2598) ∨ (¬ p 3486) ∨ (¬ p 3570) ∨ (¬ p 4243) :=
  ElevenRUP.step54451 (p 1986) (p 2027) (p 2138) (p 2598) (p 2633) (p 3486) (p 3570) (p 4243) (h 2146) (derived40810 p h) (derived40879 p h) (h 28202)

theorem derived54452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2619) ∨ (¬ p 3051) ∨ (¬ p 3370) ∨ (¬ p 3758) ∨ (¬ p 4558) :=
  ElevenRUP.step54452 (p 2027) (p 2191) (p 2619) (p 3051) (p 3370) (p 3758) (p 4558) (derived40810 p h) (h 28203)

theorem derived54454 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3323) ∨ (¬ p 3324) ∨ (¬ p 3583) ∨ (¬ p 3954) ∨ (¬ p 4368) ∨ (¬ p 4385) ∨ (¬ p 5017) :=
  ElevenRUP.step54454 (p 2027) (p 2383) (p 3323) (p 3324) (p 3583) (p 3954) (p 4368) (p 4385) (p 5017) (derived40810 p h) (h 28205)

theorem derived54456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 2870) ∨ (¬ p 3758) ∨ (¬ p 3958) ∨ (¬ p 4140) :=
  ElevenRUP.step54456 (p 2027) (p 2588) (p 2870) (p 3758) (p 3958) (p 4140) (derived40810 p h) (h 28209)

theorem derived54457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2743) ∨ (¬ p 2753) ∨ (¬ p 3146) :=
  ElevenRUP.step54457 (p 1982) (p 2027) (p 2132) (p 2619) (p 2622) (p 2743) (p 2753) (p 3146) (h 2142) (derived40810 p h) (derived40878 p h) (h 28211)

theorem derived54460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2248) ∨ (¬ p 2363) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3873) ∨ (¬ p 4340) ∨ (¬ p 4503) :=
  ElevenRUP.step54460 (p 2027) (p 2104) (p 2248) (p 2363) (p 2881) (p 2901) (p 2946) (p 3873) (p 4340) (p 4503) (derived40810 p h) (h 28216)

theorem derived54461 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3146) ∨ (¬ p 3758) ∨ (¬ p 4348) :=
  ElevenRUP.step54461 (p 1998) (p 2027) (p 2619) (p 2765) (p 3146) (p 3758) (p 4348) (h 2158) (derived40810 p h) (derived40883 p h) (h 28217)

theorem derived54462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 3146) ∨ (¬ p 3688) ∨ (¬ p 3954) ∨ (¬ p 4348) ∨ (¬ p 4358) ∨ (¬ p 4503) ∨ (¬ p 4521) :=
  ElevenRUP.step54462 (p 2027) (p 2220) (p 3146) (p 3688) (p 3954) (p 4348) (p 4358) (p 4503) (p 4521) (derived40810 p h) (h 28218)

theorem derived54463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 2850) ∨ (¬ p 3475) ∨ (¬ p 3572) :=
  ElevenRUP.step54463 (p 1994) (p 2027) (p 2323) (p 2440) (p 2807) (p 2850) (p 3475) (p 3572) (h 2154) (derived40810 p h) (derived40870 p h) (h 28219)

theorem derived54466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3471) :=
  ElevenRUP.step54466 (p 1998) (p 2027) (p 2114) (p 2717) (p 2737) (p 3365) (p 3471) (h 2158) (derived40810 p h) (derived40864 p h) (h 28223)

theorem derived54468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2663) ∨ (¬ p 3389) ∨ (¬ p 3422) ∨ (¬ p 3574) ∨ (¬ p 3876) :=
  ElevenRUP.step54468 (p 1994) (p 2027) (p 2323) (p 2663) (p 3389) (p 3422) (p 3574) (p 3876) (h 2154) (derived40810 p h) (derived40870 p h) (h 28225)

theorem derived54470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2363) ∨ (¬ p 2534) ∨ (¬ p 2579) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3573) ∨ (¬ p 4503) ∨ (¬ p 5216) :=
  ElevenRUP.step54470 (p 2027) (p 2264) (p 2363) (p 2534) (p 2579) (p 2685) (p 2696) (p 2753) (p 3347) (p 3573) (p 4503) (p 5216) (derived40810 p h) (h 28227)

theorem derived54471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 3946) ∨ (¬ p 4031) ∨ (¬ p 4198) :=
  ElevenRUP.step54471 (p 1994) (p 2027) (p 2440) (p 2997) (p 3097) (p 3125) (p 3946) (p 4031) (p 4198) (h 2154) (derived40810 p h) (derived40890 p h) (h 28229)

theorem derived54472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3347) ∨ (¬ p 3449) ∨ (¬ p 3544) ∨ (¬ p 3631) ∨ (¬ p 3954) ∨ (¬ p 4668) ∨ (¬ p 5216) :=
  ElevenRUP.step54472 (p 2027) (p 2299) (p 2579) (p 2588) (p 3347) (p 3449) (p 3544) (p 3631) (p 3954) (p 4668) (p 5216) (derived40810 p h) (h 28230)

theorem derived54482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2780) ∨ (¬ p 3989) ∨ (¬ p 4326) ∨ (¬ p 4401) :=
  ElevenRUP.step54482 (p 2027) (p 2098) (p 2780) (p 3989) (p 4326) (p 4401) (derived40810 p h) (h 28243)

theorem derived54483 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2589) ∨ (¬ p 3389) ∨ (¬ p 3947) :=
  ElevenRUP.step54483 (p 1996) (p 2027) (p 2202) (p 2417) (p 2589) (p 3389) (p 3947) (h 2156) (derived40810 p h) (derived40867 p h) (h 28244)

theorem derived54486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2528) ∨ (¬ p 3692) ∨ (¬ p 4355) ∨ (¬ p 4629) :=
  ElevenRUP.step54486 (p 2027) (p 2191) (p 2528) (p 3692) (p 4355) (p 4629) (derived40810 p h) (h 28247)

theorem derived54488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3692) ∨ (¬ p 4075) ∨ (¬ p 4120) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step54488 (p 2027) (p 2136) (p 2247) (p 2744) (p 3366) (p 3399) (p 3692) (p 4075) (p 4120) (p 4444) (p 4826) (derived40810 p h) (h 28249)

theorem derived54490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 4260) ∨ (¬ p 4831) ∨ (¬ p 5193) :=
  ElevenRUP.step54490 (p 2027) (p 2241) (p 2579) (p 2588) (p 3506) (p 3842) (p 4260) (p 4831) (p 5193) (derived40810 p h) (h 28251)

theorem derived54491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2807) ∨ (¬ p 3256) ∨ (¬ p 3591) ∨ (¬ p 3918) ∨ (¬ p 4044) ∨ (¬ p 4348) ∨ (¬ p 4358) ∨ (¬ p 4503) :=
  ElevenRUP.step54491 (p 2027) (p 2246) (p 2608) (p 2744) (p 2807) (p 3256) (p 3591) (p 3918) (p 4044) (p 4348) (p 4358) (p 4503) (derived40810 p h) (h 28252)

theorem derived54492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 4786) :=
  ElevenRUP.step54492 (p 2027) (p 2780) (p 2881) (p 2901) (p 2946) (p 3822) (p 4107) (p 4666) (p 4786) (derived40810 p h) (h 28253)

theorem derived54494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2911) ∨ (¬ p 3323) ∨ (¬ p 3551) ∨ (¬ p 4278) ∨ (¬ p 4621) ∨ (¬ p 5193) ∨ (¬ p 5197) :=
  ElevenRUP.step54494 (p 2027) (p 2241) (p 2641) (p 2911) (p 3323) (p 3551) (p 4278) (p 4621) (p 5193) (p 5197) (derived40810 p h) (h 28255)

theorem derived54495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 3952) :=
  ElevenRUP.step54495 (p 1998) (p 2027) (p 2202) (p 2563) (p 2881) (p 2901) (p 3952) (h 2158) (derived40810 p h) (derived40867 p h) (h 28256)

theorem derived54496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 2810) ∨ (¬ p 3347) ∨ (¬ p 3487) ∨ (¬ p 3956) :=
  ElevenRUP.step54496 (p 1987) (p 2027) (p 2169) (p 2313) (p 2553) (p 2577) (p 2810) (p 3347) (p 3487) (p 3956) (h 2147) (derived40810 p h) (derived40866 p h) (h 28257)

theorem derived54497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2459) ∨ (¬ p 3556) ∨ (¬ p 3692) ∨ (¬ p 4031) ∨ (¬ p 4119) :=
  ElevenRUP.step54497 (p 1994) (p 2027) (p 2440) (p 2459) (p 2633) (p 3556) (p 3692) (p 4031) (p 4119) (h 2154) (derived40810 p h) (derived40879 p h) (h 28258)

theorem derived54512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2166) ∨ (¬ p 3371) ∨ (¬ p 3694) ∨ (¬ p 4734) :=
  ElevenRUP.step54512 (p 2027) (p 2138) (p 2166) (p 3371) (p 3694) (p 4734) (derived40810 p h) (h 28274)

theorem derived54518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2493) ∨ (¬ p 2579) ∨ (¬ p 2750) ∨ (¬ p 3541) ∨ (¬ p 4108) :=
  ElevenRUP.step54518 (p 2027) (p 2241) (p 2493) (p 2579) (p 2750) (p 3541) (p 4108) (derived40810 p h) (h 28282)

theorem derived54519 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2319) ∨ (¬ p 2563) ∨ (¬ p 3957) ∨ (¬ p 4340) ∨ (¬ p 4359) ∨ (¬ p 4590) ∨ (¬ p 4882) ∨ (¬ p 5016) :=
  ElevenRUP.step54519 (p 2027) (p 2088) (p 2319) (p 2563) (p 3957) (p 4340) (p 4359) (p 4590) (p 4882) (p 5016) (derived40810 p h) (h 28283)

theorem derived54532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2230) ∨ (¬ p 2363) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4340) ∨ (¬ p 4376) ∨ (¬ p 4503) :=
  ElevenRUP.step54532 (p 2027) (p 2104) (p 2230) (p 2363) (p 2427) (p 2881) (p 3366) (p 3519) (p 4340) (p 4376) (p 4503) (derived40810 p h) (h 28299)

theorem derived54533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 3292) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3631) ∨ (¬ p 3950) ∨ (¬ p 4236) ∨ (¬ p 4376) ∨ (¬ p 5284) :=
  ElevenRUP.step54533 (p 2027) (p 3266) (p 3292) (p 3366) (p 3399) (p 3452) (p 3631) (p 3950) (p 4236) (p 4376) (p 5284) (derived40810 p h) (h 28300)

theorem derived54534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3324) ∨ (¬ p 3471) ∨ (¬ p 3591) ∨ (¬ p 3609) ∨ (¬ p 4319) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4805) :=
  ElevenRUP.step54534 (p 2027) (p 2241) (p 2750) (p 2753) (p 3324) (p 3471) (p 3591) (p 3609) (p 4319) (p 4348) (p 4503) (p 4805) (derived40810 p h) (h 28301)

theorem derived54535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3365) ∨ (¬ p 4111) ∨ (¬ p 4315) :=
  ElevenRUP.step54535 (p 1976) (p 2027) (p 2545) (p 2992) (p 3365) (p 4111) (p 4315) (h 2136) (derived40810 p h) (derived40876 p h) (h 28302)

theorem derived54536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2901) ∨ (¬ p 3486) ∨ (¬ p 4110) ∨ (¬ p 4705) :=
  ElevenRUP.step54536 (p 2027) (p 2192) (p 2901) (p 3486) (p 4110) (p 4705) (derived40810 p h) (h 28303)

theorem derived54538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2590) ∨ (¬ p 2901) ∨ (¬ p 3581) ∨ (¬ p 3644) ∨ (¬ p 3691) ∨ (¬ p 4705) :=
  ElevenRUP.step54538 (p 2027) (p 2341) (p 2590) (p 2901) (p 3581) (p 3644) (p 3691) (p 4705) (derived40810 p h) (h 28305)

theorem derived54540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2470) ∨ (¬ p 2579) ∨ (¬ p 3016) ∨ (¬ p 4157) :=
  ElevenRUP.step54540 (p 1982) (p 2027) (p 2363) (p 2470) (p 2545) (p 2579) (p 3016) (p 4157) (h 2142) (derived40810 p h) (derived40876 p h) (h 28307)

theorem derived54542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2210) ∨ (¬ p 2363) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 4340) ∨ (¬ p 4503) ∨ (¬ p 4736) :=
  ElevenRUP.step54542 (p 2027) (p 2104) (p 2210) (p 2363) (p 2881) (p 2891) (p 4340) (p 4503) (p 4736) (derived40810 p h) (h 28309)

theorem derived54543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 2963) ∨ (¬ p 3201) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4503) ∨ (¬ p 4789) :=
  ElevenRUP.step54543 (p 2027) (p 2363) (p 2598) (p 2911) (p 2963) (p 3201) (p 4118) (p 4196) (p 4503) (p 4789) (derived40810 p h) (h 28310)

theorem derived54548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2727) ∨ (¬ p 2810) ∨ (¬ p 3954) :=
  ElevenRUP.step54548 (p 1987) (p 2027) (p 2114) (p 2241) (p 2727) (p 2810) (p 3954) (h 2147) (derived40810 p h) (derived40864 p h) (h 28315)

theorem derived54549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3585) ∨ (¬ p 3876) ∨ (¬ p 4390) ∨ (¬ p 4708) :=
  ElevenRUP.step54549 (p 2027) (p 2829) (p 3585) (p 3876) (p 4390) (p 4708) (derived40810 p h) (h 28316)

theorem derived54550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2312) ∨ (¬ p 2341) ∨ (¬ p 3548) ∨ (¬ p 4105) ∨ (¬ p 4514) :=
  ElevenRUP.step54550 (p 2027) (p 2274) (p 2312) (p 2341) (p 3548) (p 4105) (p 4514) (derived40810 p h) (h 28317)

theorem derived54551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2737) ∨ (¬ p 3688) ∨ (¬ p 4358) :=
  ElevenRUP.step54551 (p 1987) (p 2027) (p 2344) (p 2383) (p 2737) (p 3688) (p 4358) (h 2147) (derived40810 p h) (derived40871 p h) (h 28318)

theorem derived54553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2952) ∨ (¬ p 3097) ∨ (¬ p 3136) ∨ (¬ p 3379) ∨ (¬ p 3745) ∨ (¬ p 4195) ∨ (¬ p 4236) ∨ (¬ p 4736) :=
  ElevenRUP.step54553 (p 1982) (p 2027) (p 2518) (p 2528) (p 2952) (p 2997) (p 3097) (p 3136) (p 3379) (p 3745) (p 4195) (p 4236) (p 4736) (h 2142) (derived40810 p h) (derived40890 p h) (h 28320)

theorem derived54558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2319) ∨ (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 2779) ∨ (¬ p 2829) :=
  ElevenRUP.step54558 (p 1983) (p 2027) (p 2114) (p 2299) (p 2319) (p 2341) (p 2396) (p 2779) (p 2829) (h 2143) (derived40810 p h) (derived40864 p h) (h 28328)

theorem derived54560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2962) ∨ (¬ p 3097) ∨ (¬ p 4110) ∨ (¬ p 4539) :=
  ElevenRUP.step54560 (p 2027) (p 2307) (p 2962) (p 3097) (p 4110) (p 4539) (derived40810 p h) (h 28330)

theorem derived54566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 3860) ∨ (¬ p 4370) :=
  ElevenRUP.step54566 (p 1992) (p 2027) (p 2202) (p 2608) (p 3641) (p 3684) (p 3860) (p 4370) (h 2152) (derived40810 p h) (derived40867 p h) (h 28337)

theorem derived54568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2946) ∨ (¬ p 3156) ∨ (¬ p 3880) :=
  ElevenRUP.step54568 (p 1994) (p 2027) (p 2323) (p 2440) (p 2946) (p 3156) (p 3880) (h 2154) (derived40810 p h) (derived40870 p h) (h 28339)

theorem derived54572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 3379) :=
  ElevenRUP.step54572 (p 1981) (p 2027) (p 2247) (p 2352) (p 2493) (p 2688) (p 3379) (h 2141) (derived40810 p h) (derived40880 p h) (h 28343)

theorem derived54575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2363) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 3105) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4335) ∨ (¬ p 4433) :=
  ElevenRUP.step54575 (p 2027) (p 2254) (p 2363) (p 2608) (p 2839) (p 3105) (p 3172) (p 4118) (p 4335) (p 4433) (derived40810 p h) (h 28348)

theorem derived54578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 2608) ∨ (¬ p 3370) ∨ (¬ p 3452) ∨ (¬ p 3590) ∨ (¬ p 4377) ∨ (¬ p 4697) ∨ (¬ p 5160) :=
  ElevenRUP.step54578 (p 2027) (p 2156) (p 2187) (p 2363) (p 2608) (p 3370) (p 3452) (p 3590) (p 4377) (p 4697) (p 5160) (derived40810 p h) (h 28352)

theorem derived54579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3055) ∨ (¬ p 3319) ∨ (¬ p 3549) ∨ (¬ p 3684) ∨ (¬ p 4368) ∨ (¬ p 4736) ∨ (¬ p 4948) ∨ (¬ p 5020) :=
  ElevenRUP.step54579 (p 2027) (p 2307) (p 3055) (p 3319) (p 3549) (p 3684) (p 4368) (p 4736) (p 4948) (p 5020) (derived40810 p h) (h 28353)

theorem derived54580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2807) ∨ (¬ p 3172) ∨ (¬ p 3690) :=
  ElevenRUP.step54580 (p 1985) (p 2027) (p 2449) (p 2807) (p 3042) (p 3172) (p 3690) (h 2145) (derived40810 p h) (derived40892 p h) (h 28355)

theorem derived54583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3946) ∨ (¬ p 3998) ∨ (¬ p 4114) ∨ (¬ p 4186) ∨ (¬ p 4286) ∨ (¬ p 4620) ∨ (¬ p 4710) :=
  ElevenRUP.step54583 (p 2027) (p 3946) (p 3998) (p 4114) (p 4186) (p 4286) (p 4620) (p 4710) (derived40810 p h) (h 28365)

theorem derived54587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3553) ∨ (¬ p 4386) ∨ (¬ p 5053) :=
  ElevenRUP.step54587 (p 2027) (p 2870) (p 2881) (p 3553) (p 4386) (p 5053) (derived40810 p h) (h 28369)

theorem derived54595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 3097) ∨ (¬ p 3379) ∨ (¬ p 3641) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3954) ∨ (¬ p 4030) ∨ (¬ p 4420) ∨ (¬ p 4877) :=
  ElevenRUP.step54595 (p 2027) (p 2299) (p 3097) (p 3379) (p 3641) (p 3645) (p 3646) (p 3954) (p 4030) (p 4420) (p 4877) (derived40810 p h) (h 28379)

theorem derived54599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2598) ∨ (¬ p 2780) ∨ (¬ p 3822) :=
  ElevenRUP.step54599 (p 1986) (p 2027) (p 2553) (p 2598) (p 2780) (p 3008) (p 3822) (h 2146) (derived40810 p h) (derived40891 p h) (h 28384)

theorem derived54601 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2553) ∨ (¬ p 3568) ∨ (¬ p 3591) ∨ (¬ p 4319) :=
  ElevenRUP.step54601 (p 1977) (p 2027) (p 2241) (p 2553) (p 3008) (p 3568) (p 3591) (p 4319) (h 2137) (derived40810 p h) (derived40891 p h) (h 28386)

theorem derived54604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 3880) ∨ (¬ p 4134) ∨ (¬ p 4733) :=
  ElevenRUP.step54604 (p 2027) (p 2668) (p 2696) (p 2797) (p 3238) (p 3452) (p 3880) (p 4134) (p 4733) (derived40810 p h) (h 28389)

theorem derived54607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3568) ∨ (¬ p 4140) ∨ (¬ p 4173) ∨ (¬ p 4564) :=
  ElevenRUP.step54607 (p 2027) (p 2891) (p 3568) (p 4140) (p 4173) (p 4564) (derived40810 p h) (h 28394)

theorem derived54608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2807) ∨ (¬ p 3238) ∨ (¬ p 3256) ∨ (¬ p 3452) ∨ (¬ p 3880) ∨ (¬ p 4044) ∨ (¬ p 4348) ∨ (¬ p 4905) :=
  ElevenRUP.step54608 (p 2027) (p 2248) (p 2807) (p 3238) (p 3256) (p 3452) (p 3880) (p 4044) (p 4348) (p 4905) (derived40810 p h) (h 28395)

theorem derived54609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2630) ∨ (¬ p 3177) ∨ (¬ p 3857) ∨ (¬ p 3877) :=
  ElevenRUP.step54609 (p 1994) (p 2027) (p 2528) (p 2630) (p 3177) (p 3498) (p 3857) (p 3877) (h 2154) (derived40810 p h) (derived40899 p h) (h 28396)

theorem derived54610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2406) ∨ (¬ p 2509) ∨ (¬ p 2589) ∨ (¬ p 2655) ∨ (¬ p 3471) ∨ (¬ p 3609) ∨ (¬ p 4348) ∨ (¬ p 4438) ∨ (¬ p 4733) ∨ (¬ p 4805) :=
  ElevenRUP.step54610 (p 2027) (p 2245) (p 2406) (p 2509) (p 2589) (p 2655) (p 3471) (p 3609) (p 4348) (p 4438) (p 4733) (p 4805) (derived40810 p h) (h 28397)

theorem derived54614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 3276) ∨ (¬ p 4191) ∨ (¬ p 4422) ∨ (¬ p 4624) :=
  ElevenRUP.step54614 (p 2027) (p 2588) (p 3276) (p 4191) (p 4422) (p 4624) (derived40810 p h) (h 28401)

theorem derived54618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3309) ∨ (¬ p 3822) ∨ (¬ p 3923) ∨ (¬ p 5220) :=
  ElevenRUP.step54618 (p 1976) (p 2027) (p 2169) (p 3055) (p 3309) (p 3822) (p 3923) (p 5220) (h 2136) (derived40810 p h) (derived40866 p h) (h 28407)

theorem derived54620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2922) ∨ (¬ p 3361) ∨ (¬ p 3414) ∨ (¬ p 3740) ∨ (¬ p 4814) :=
  ElevenRUP.step54620 (p 2027) (p 2630) (p 2922) (p 3361) (p 3414) (p 3740) (p 4814) (derived40810 p h) (h 28410)

theorem derived54627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2383) ∨ (¬ p 3055) ∨ (¬ p 3266) ∨ (¬ p 3876) ∨ (¬ p 3987) ∨ (¬ p 4786) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step54627 (p 2027) (p 2363) (p 2383) (p 3055) (p 3266) (p 3876) (p 3987) (p 4786) (p 4831) (p 5503) (derived40810 p h) (h 28418)

theorem derived54629 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2577) ∨ (¬ p 3389) ∨ (¬ p 3564) ∨ (¬ p 3660) ∨ (¬ p 3946) ∨ (¬ p 4646) :=
  ElevenRUP.step54629 (p 2027) (p 2577) (p 3389) (p 3564) (p 3660) (p 3946) (p 4646) (derived40810 p h) (h 28420)

theorem derived54630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2579) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3324) ∨ (¬ p 3347) ∨ (¬ p 3984) ∨ (¬ p 5118) ∨ (¬ p 5216) ∨ (¬ p 5580) :=
  ElevenRUP.step54630 (p 2027) (p 2132) (p 2579) (p 2619) (p 2753) (p 3146) (p 3324) (p 3347) (p 3984) (p 5118) (p 5216) (p 5580) (derived40810 p h) (h 28421)

theorem derived54631 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2963) ∨ (¬ p 4037) ∨ (¬ p 4191) ∨ (¬ p 4253) ∨ (¬ p 4826) :=
  ElevenRUP.step54631 (p 2027) (p 2254) (p 2608) (p 2707) (p 2963) (p 4037) (p 4191) (p 4253) (p 4826) (derived40810 p h) (h 28423)

theorem derived54633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3904) ∨ (¬ p 4120) ∨ (¬ p 4787) :=
  ElevenRUP.step54633 (p 2027) (p 2655) (p 3136) (p 3156) (p 3904) (p 4120) (p 4787) (derived40810 p h) (h 28425)

theorem derived54639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4521) ∨ (¬ p 4604) :=
  ElevenRUP.step54639 (p 2027) (p 2247) (p 2459) (p 2881) (p 3051) (p 4037) (p 4154) (p 4521) (p 4604) (derived40810 p h) (h 28432)

theorem derived54645 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 2696) ∨ (¬ p 3370) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4418) ∨ (¬ p 4668) ∨ (¬ p 5049) :=
  ElevenRUP.step54645 (p 2027) (p 2156) (p 2274) (p 2396) (p 2696) (p 3370) (p 3425) (p 3659) (p 4418) (p 4668) (p 5049) (derived40810 p h) (h 28439)

theorem derived54649 (p : Nat → Prop) (h : Inputs p) :
    (p 2751) ∨ (¬ p 4111) :=
  ElevenRUP.step54649 (p 1987) (p 2545) (p 2751) (p 4111) (h 2147) (derived40876 p h) (h 28444)

theorem derived54653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3952) :=
  ElevenRUP.step54653 (p 1979) (p 2027) (p 2766) (p 2860) (p 3692) (p 3694) (p 3952) (h 2139) (derived40810 p h) (derived40884 p h) (h 28449)

theorem derived54654 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3692) ∨ (¬ p 3952) ∨ (¬ p 4120) :=
  ElevenRUP.step54654 (p 1979) (p 2027) (p 2156) (p 2766) (p 3692) (p 3952) (p 4120) (h 2139) (derived40810 p h) (derived40884 p h) (h 28450)

theorem derived54659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2749) ∨ (¬ p 3093) ∨ (¬ p 4870) :=
  ElevenRUP.step54659 (p 2027) (p 2245) (p 2657) (p 2727) (p 2749) (p 3093) (p 4870) (derived40810 p h) (h 28456)

theorem derived54661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2437) ∨ (¬ p 3232) ∨ (¬ p 3359) ∨ (¬ p 3830) :=
  ElevenRUP.step54661 (p 2010) (p 2027) (p 2247) (p 2437) (p 2688) (p 3232) (p 3359) (p 3830) (h 2170) (derived40810 p h) (derived40880 p h) (h 28458)

theorem derived54664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 4311) ∨ (¬ p 4315) ∨ (¬ p 5569) ∨ (¬ p 5740) :=
  ElevenRUP.step54664 (p 2027) (p 3005) (p 4311) (p 4315) (p 5569) (p 5740) (derived40810 p h) (h 28461)

theorem derived54667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2589) ∨ (¬ p 3553) ∨ (¬ p 3984) ∨ (¬ p 4067) ∨ (¬ p 4717) ∨ (¬ p 5201) :=
  ElevenRUP.step54667 (p 2027) (p 2341) (p 2589) (p 3553) (p 3984) (p 4067) (p 4717) (p 5201) (derived40810 p h) (h 28466)

theorem derived54669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3292) ∨ (¬ p 4154) ∨ (¬ p 5284) :=
  ElevenRUP.step54669 (p 1977) (p 2027) (p 2331) (p 2764) (p 3292) (p 4154) (p 5284) (h 2137) (derived40810 p h) (derived40882 p h) (h 28469)

theorem derived54672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3551) ∨ (p 4905) :=
  ElevenRUP.step54672 (p 2022) (p 3551) (p 3578) (p 4905) (h 2182) (derived40900 p h) (h 28472)

theorem derived54673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2696) ∨ (¬ p 2707) ∨ (¬ p 2743) ∨ (¬ p 3589) ∨ (¬ p 4325) :=
  ElevenRUP.step54673 (p 1983) (p 2027) (p 2449) (p 2696) (p 2699) (p 2707) (p 2743) (p 3589) (p 4325) (h 2143) (derived40810 p h) (derived40881 p h) (h 28473)

theorem derived54674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2284) ∨ (¬ p 2891) ∨ (¬ p 4320) ∨ (¬ p 4365) :=
  ElevenRUP.step54674 (p 1990) (p 2027) (p 2241) (p 2284) (p 2699) (p 2891) (p 4320) (p 4365) (h 2150) (derived40810 p h) (derived40881 p h) (h 28474)

theorem derived54676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 3323) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 5193) :=
  ElevenRUP.step54676 (p 2027) (p 2241) (p 2641) (p 3323) (p 3540) (p 3644) (p 4330) (p 4348) (p 5193) (derived40810 p h) (h 28477)

theorem derived54680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3193) ∨ (¬ p 3246) ∨ (¬ p 4264) ∨ (¬ p 4277) ∨ (¬ p 5295) :=
  ElevenRUP.step54680 (p 2027) (p 2922) (p 3193) (p 3246) (p 4264) (p 4277) (p 5295) (derived40810 p h) (h 28481)

theorem derived54688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2518) ∨ (¬ p 3379) ∨ (¬ p 3954) ∨ (¬ p 4157) :=
  ElevenRUP.step54688 (p 1982) (p 2027) (p 2114) (p 2363) (p 2518) (p 3379) (p 3954) (p 4157) (h 2142) (derived40810 p h) (derived40864 p h) (h 28490)

theorem derived54692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 3979) ∨ (¬ p 4733) ∨ (¬ p 5122) :=
  ElevenRUP.step54692 (p 2027) (p 2191) (p 2774) (p 2819) (p 3555) (p 3692) (p 3979) (p 4733) (p 5122) (derived40810 p h) (h 28494)

theorem derived54698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 3146) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3954) ∨ (¬ p 4905) :=
  ElevenRUP.step54698 (p 2027) (p 2252) (p 2476) (p 2534) (p 2655) (p 2750) (p 3146) (p 3399) (p 3527) (p 3954) (p 4905) (derived40810 p h) (h 28501)

theorem derived54699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3105) ∨ (¬ p 3694) ∨ (¬ p 4348) ∨ (¬ p 4905) :=
  ElevenRUP.step54699 (p 2027) (p 2532) (p 3105) (p 3694) (p 4348) (p 4905) (derived40810 p h) (h 28502)

theorem derived54703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3471) ∨ (¬ p 3583) :=
  ElevenRUP.step54703 (p 2008) (p 2027) (p 2737) (p 3365) (p 3471) (p 3474) (p 3583) (h 2168) (derived40810 p h) (derived40898 p h) (h 28508)

theorem derived54704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3115) ∨ (¬ p 3588) ∨ (¬ p 3952) ∨ (¬ p 3954) ∨ (¬ p 4106) ∨ (¬ p 4278) ∨ (¬ p 4521) ∨ (¬ p 4621) ∨ (¬ p 5045) :=
  ElevenRUP.step54704 (p 2027) (p 2156) (p 3115) (p 3588) (p 3952) (p 3954) (p 4106) (p 4278) (p 4521) (p 4621) (p 5045) (derived40810 p h) (h 28509)

theorem derived54706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2668) ∨ (¬ p 3745) ∨ (¬ p 4235) ∨ (¬ p 4275) ∨ (¬ p 4405) :=
  ElevenRUP.step54706 (p 2027) (p 2563) (p 2668) (p 3745) (p 4235) (p 4275) (p 4405) (derived40810 p h) (h 28511)

theorem derived54707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3051) ∨ (¬ p 4032) ∨ (¬ p 4382) ∨ (¬ p 4647) :=
  ElevenRUP.step54707 (p 2027) (p 2417) (p 3051) (p 4032) (p 4382) (p 4647) (derived40810 p h) (h 28512)

theorem derived54710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2177) ∨ (¬ p 2307) ∨ (¬ p 2786) ∨ (¬ p 3570) :=
  ElevenRUP.step54710 (p 1985) (p 2027) (p 2138) (p 2177) (p 2307) (p 2786) (p 3474) (p 3570) (h 2145) (derived40810 p h) (derived40898 p h) (h 28515)

theorem derived54712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4129) ∨ (¬ p 4425) ∨ (¬ p 4826) :=
  ElevenRUP.step54712 (p 2027) (p 2248) (p 2901) (p 2946) (p 3193) (p 3452) (p 4129) (p 4425) (p 4826) (derived40810 p h) (h 28520)

theorem derived54713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2132) ∨ (¬ p 2476) ∨ (¬ p 3083) ∨ (¬ p 3097) ∨ (¬ p 3574) ∨ (¬ p 3589) ∨ (¬ p 3985) ∨ (¬ p 4718) ∨ (¬ p 5193) :=
  ElevenRUP.step54713 (p 2027) (p 2122) (p 2132) (p 2476) (p 3083) (p 3097) (p 3574) (p 3589) (p 3985) (p 4718) (p 5193) (derived40810 p h) (h 28521)

theorem derived54716 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2963) ∨ (¬ p 2972) ∨ (¬ p 3324) ∨ (¬ p 3680) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step54716 (p 2027) (p 2210) (p 2254) (p 2963) (p 2972) (p 3324) (p 3680) (p 5123) (p 5580) (derived40810 p h) (h 28525)

theorem derived54722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2992) ∨ (¬ p 3506) ∨ (¬ p 4322) ∨ (¬ p 5038) :=
  ElevenRUP.step54722 (p 2011) (p 2027) (p 2241) (p 2699) (p 2992) (p 3506) (p 4322) (p 5038) (h 2171) (derived40810 p h) (derived40881 p h) (h 28531)

theorem derived54726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3051) ∨ (¬ p 4120) ∨ (¬ p 4235) ∨ (¬ p 4885) :=
  ElevenRUP.step54726 (p 2027) (p 2619) (p 3051) (p 4120) (p 4235) (p 4885) (derived40810 p h) (h 28536)

theorem derived54732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2663) ∨ (¬ p 2952) ∨ (¬ p 3574) ∨ (¬ p 4701) :=
  ElevenRUP.step54732 (p 2027) (p 2573) (p 2663) (p 2952) (p 3574) (p 4701) (derived40810 p h) (h 28544)

theorem derived54734 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 3146) ∨ (¬ p 4348) :=
  ElevenRUP.step54734 (p 1998) (p 2027) (p 2220) (p 2622) (p 2951) (p 3136) (p 3146) (p 4348) (h 2158) (derived40810 p h) (derived40878 p h) (h 28547)

theorem derived54737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 2963) ∨ (¬ p 3324) :=
  ElevenRUP.step54737 (p 1987) (p 2027) (p 2169) (p 2651) (p 2810) (p 2963) (p 3324) (h 2147) (derived40810 p h) (derived40866 p h) (h 28550)

theorem derived54740 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 4117) ∨ (¬ p 4807) :=
  ElevenRUP.step54740 (p 2027) (p 2104) (p 2264) (p 2807) (p 4117) (p 4807) (derived40810 p h) (h 28556)

theorem derived54741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 3146) ∨ (¬ p 4261) ∨ (¬ p 4492) ∨ (¬ p 4507) :=
  ElevenRUP.step54741 (p 2027) (p 2192) (p 3146) (p 4261) (p 4492) (p 4507) (derived40810 p h) (h 28557)

theorem derived54744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2589) ∨ (¬ p 2655) ∨ (¬ p 2807) ∨ (¬ p 4116) ∨ (¬ p 4652) :=
  ElevenRUP.step54744 (p 2027) (p 2406) (p 2589) (p 2655) (p 2807) (p 4116) (p 4652) (derived40810 p h) (h 28560)

theorem derived54753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2797) ∨ (¬ p 2810) ∨ (¬ p 4154) :=
  ElevenRUP.step54753 (p 1984) (p 2027) (p 2247) (p 2545) (p 2797) (p 2810) (p 4154) (h 2144) (derived40810 p h) (derived40876 p h) (h 28575)

theorem derived54755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3471) ∨ (¬ p 4173) ∨ (¬ p 4243) ∨ (¬ p 4344) ∨ (¬ p 4558) :=
  ElevenRUP.step54755 (p 2027) (p 2138) (p 3471) (p 4173) (p 4243) (p 4344) (p 4558) (derived40810 p h) (h 28577)

theorem derived54756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2936) ∨ (¬ p 3389) ∨ (¬ p 3527) ∨ (¬ p 4383) :=
  ElevenRUP.step54756 (p 2027) (p 2476) (p 2936) (p 3389) (p 3527) (p 4383) (derived40810 p h) (h 28578)

theorem derived54758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2187) ∨ (¬ p 2774) ∨ (¬ p 4857) ∨ (¬ p 4889) :=
  ElevenRUP.step54758 (p 2027) (p 2104) (p 2187) (p 2774) (p 4857) (p 4889) (derived40810 p h) (h 28580)

theorem derived54759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3954) ∨ (¬ p 4242) ∨ (¬ p 4324) ∨ (¬ p 4666) ∨ (¬ p 4805) ∨ (¬ p 5190) :=
  ElevenRUP.step54759 (p 2027) (p 2177) (p 2553) (p 2573) (p 3954) (p 4242) (p 4324) (p 4666) (p 4805) (p 5190) (derived40810 p h) (h 28581)

theorem derived54760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2810) ∨ (¬ p 3537) ∨ (¬ p 4967) ∨ (¬ p 5011) :=
  ElevenRUP.step54760 (p 2027) (p 2743) (p 2810) (p 3537) (p 4967) (p 5011) (derived40810 p h) (h 28582)

theorem derived54763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3989) ∨ (¬ p 4111) :=
  ElevenRUP.step54763 (p 1990) (p 2027) (p 2545) (p 2641) (p 2668) (p 3989) (p 4111) (h 2150) (derived40810 p h) (derived40876 p h) (h 28585)

theorem derived54765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3019) ∨ (¬ p 3189) ∨ (¬ p 3549) ∨ (¬ p 4245) ∨ (¬ p 5011) :=
  ElevenRUP.step54765 (p 2027) (p 2295) (p 3019) (p 3189) (p 3549) (p 4245) (p 5011) (derived40810 p h) (h 28587)

theorem derived54769 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 3686) ∨ (¬ p 4324) ∨ (¬ p 4750) :=
  ElevenRUP.step54769 (p 2027) (p 2417) (p 2437) (p 3686) (p 4324) (p 4750) (derived40810 p h) (h 28591)

theorem derived54771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3661) ∨ (¬ p 4118) ∨ (¬ p 4315) ∨ (¬ p 5568) :=
  ElevenRUP.step54771 (p 1987) (p 2027) (p 3146) (p 3661) (p 3982) (p 4118) (p 4315) (p 5568) (h 2147) (derived40810 p h) (derived40909 p h) (h 28593)

theorem derived54773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2143) ∨ (¬ p 3097) ∨ (¬ p 3985) ∨ (¬ p 4032) ∨ (¬ p 5043) :=
  ElevenRUP.step54773 (p 2027) (p 2122) (p 2143) (p 3097) (p 3985) (p 4032) (p 5043) (derived40810 p h) (h 28595)

theorem derived54774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2166) ∨ (¬ p 4120) ∨ (¬ p 4244) ∨ (¬ p 4418) :=
  ElevenRUP.step54774 (p 1990) (p 2027) (p 2156) (p 2166) (p 2938) (p 4120) (p 4244) (p 4418) (h 2150) (derived40810 p h) (derived40888 p h) (h 28597)

theorem derived54776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3684) :=
  ElevenRUP.step54776 (p 1986) (p 2027) (p 2230) (p 2476) (p 2534) (p 2766) (p 3684) (h 2146) (derived40810 p h) (derived40884 p h) (h 28601)

theorem derived54780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2192) ∨ (¬ p 2363) ∨ (¬ p 3857) ∨ (¬ p 4115) :=
  ElevenRUP.step54780 (p 1990) (p 2027) (p 2169) (p 2191) (p 2192) (p 2363) (p 3857) (p 4115) (h 2150) (derived40810 p h) (derived40866 p h) (h 28605)

theorem derived54781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3093) ∨ (¬ p 3860) ∨ (¬ p 4514) ∨ (¬ p 4993) :=
  ElevenRUP.step54781 (p 2027) (p 2187) (p 3093) (p 3860) (p 4514) (p 4993) (derived40810 p h) (h 28606)

theorem derived54784 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 3201) ∨ (¬ p 3367) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 4276) :=
  ElevenRUP.step54784 (p 2027) (p 2177) (p 2254) (p 2608) (p 3201) (p 3367) (p 3414) (p 3553) (p 4276) (derived40810 p h) (h 28612)

theorem derived54785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2437) ∨ (¬ p 2482) ∨ (¬ p 3540) ∨ (¬ p 4340) :=
  ElevenRUP.step54785 (p 2018) (p 2027) (p 2088) (p 2437) (p 2482) (p 2545) (p 3540) (p 4340) (h 2178) (derived40810 p h) (derived40876 p h) (h 28613)

theorem derived54787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3516) ∨ (¬ p 3819) ∨ (¬ p 4324) ∨ (¬ p 4357) ∨ (¬ p 4749) :=
  ElevenRUP.step54787 (p 2027) (p 3055) (p 3516) (p 3819) (p 4324) (p 4357) (p 4749) (derived40810 p h) (h 28615)

theorem derived54791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2136) ∨ (¬ p 2363) ∨ (¬ p 2860) ∨ (¬ p 3646) ∨ (¬ p 4326) :=
  ElevenRUP.step54791 (p 1982) (p 2027) (p 2098) (p 2136) (p 2363) (p 2860) (p 3474) (p 3646) (p 4326) (h 2142) (derived40810 p h) (derived40898 p h) (h 28620)

theorem derived54793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2484) ∨ (¬ p 3266) ∨ (¬ p 4045) ∨ (¬ p 4425) :=
  ElevenRUP.step54793 (p 2027) (p 2088) (p 2484) (p 3266) (p 4045) (p 4425) (derived40810 p h) (h 28622)

theorem derived54795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2459) ∨ (¬ p 2518) ∨ (¬ p 3204) ∨ (¬ p 3379) ∨ (¬ p 3954) ∨ (¬ p 4347) ∨ (¬ p 4420) ∨ (¬ p 4870) :=
  ElevenRUP.step54795 (p 2027) (p 2387) (p 2459) (p 2518) (p 3204) (p 3379) (p 3954) (p 4347) (p 4420) (p 4870) (derived40810 p h) (h 28624)

theorem derived54803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3136) ∨ (¬ p 3540) ∨ (¬ p 4241) ∨ (¬ p 4644) :=
  ElevenRUP.step54803 (p 2027) (p 2662) (p 2810) (p 3136) (p 3540) (p 4241) (p 4644) (derived40810 p h) (h 28634)

theorem derived54811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2249) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3146) ∨ (¬ p 3292) ∨ (¬ p 3461) ∨ (¬ p 4399) ∨ (¬ p 4604) ∨ (¬ p 5284) :=
  ElevenRUP.step54811 (p 2027) (p 2220) (p 2249) (p 2656) (p 2727) (p 3146) (p 3292) (p 3461) (p 4399) (p 4604) (p 5284) (derived40810 p h) (h 28644)

theorem derived54815 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2396) ∨ (¬ p 2750) ∨ (¬ p 3292) ∨ (¬ p 3399) ∨ (¬ p 3547) ∨ (¬ p 3680) ∨ (¬ p 3951) ∨ (¬ p 3954) ∨ (¬ p 5284) :=
  ElevenRUP.step54815 (p 2027) (p 2252) (p 2396) (p 2750) (p 3292) (p 3399) (p 3547) (p 3680) (p 3951) (p 3954) (p 5284) (derived40810 p h) (h 28649)

theorem derived54816 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2780) ∨ (¬ p 3016) ∨ (¬ p 4342) ∨ (¬ p 4750) :=
  ElevenRUP.step54816 (p 2027) (p 2598) (p 2780) (p 3016) (p 4342) (p 4750) (derived40810 p h) (h 28650)

theorem derived54817 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2743) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3361) ∨ (¬ p 3609) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 4737) :=
  ElevenRUP.step54817 (p 2027) (p 2098) (p 2743) (p 2963) (p 3324) (p 3361) (p 3609) (p 4348) (p 4503) (p 4737) (derived40810 p h) (h 28651)

theorem derived54819 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 3688) ∨ (¬ p 4324) ∨ (¬ p 4357) ∨ (¬ p 4842) :=
  ElevenRUP.step54819 (p 2027) (p 3631) (p 3687) (p 3688) (p 4324) (p 4357) (p 4842) (derived40810 p h) (h 28653)

theorem derived54820 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 2860) ∨ (¬ p 4242) ∨ (¬ p 4507) ∨ (¬ p 4740) :=
  ElevenRUP.step54820 (p 2027) (p 2839) (p 2860) (p 4242) (p 4507) (p 4740) (derived40810 p h) (h 28654)

theorem derived54822 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 4208) ∨ (¬ p 4244) ∨ (¬ p 4322) :=
  ElevenRUP.step54822 (p 2006) (p 2027) (p 2764) (p 2901) (p 4208) (p 4244) (p 4322) (h 2166) (derived40810 p h) (derived40882 p h) (h 28656)

theorem derived54823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 3146) ∨ (¬ p 3222) ∨ (¬ p 3276) ∨ (¬ p 3347) ∨ (¬ p 3584) ∨ (¬ p 3685) ∨ (¬ p 3759) ∨ (¬ p 4253) ∨ (¬ p 4340) ∨ (¬ p 4715) ∨ (¬ p 5503) :=
  ElevenRUP.step54823 (p 1988) (p 2027) (p 2441) (p 3146) (p 3222) (p 3276) (p 3347) (p 3578) (p 3584) (p 3685) (p 3759) (p 4253) (p 4340) (p 4715) (p 5503) (h 2148) (derived40810 p h) (derived40900 p h) (h 28657)

theorem derived54826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2741) ∨ (¬ p 3292) ∨ (¬ p 3519) ∨ (¬ p 3680) ∨ (¬ p 4376) ∨ (¬ p 5059) ∨ (¬ p 5284) :=
  ElevenRUP.step54826 (p 2027) (p 2252) (p 2352) (p 2363) (p 2573) (p 2741) (p 3292) (p 3519) (p 3680) (p 4376) (p 5059) (p 5284) (derived40810 p h) (h 28661)

theorem derived54831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 4172) ∨ (¬ p 4173) :=
  ElevenRUP.step54831 (p 1998) (p 2027) (p 2156) (p 2699) (p 2881) (p 2891) (p 4172) (p 4173) (h 2158) (derived40810 p h) (derived40881 p h) (h 28666)

theorem derived54832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2166) ∨ (¬ p 2743) ∨ (¬ p 3146) ∨ (¬ p 3361) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 4418) ∨ (¬ p 4669) ∨ (¬ p 4737) :=
  ElevenRUP.step54832 (p 2027) (p 2132) (p 2166) (p 2743) (p 3146) (p 3361) (p 3414) (p 3947) (p 4418) (p 4669) (p 4737) (derived40810 p h) (h 28667)

theorem derived54833 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3868) ∨ (¬ p 4067) ∨ (¬ p 4194) ∨ (¬ p 4391) ∨ (¬ p 4753) :=
  ElevenRUP.step54833 (p 2027) (p 3201) (p 3868) (p 4067) (p 4194) (p 4391) (p 4753) (derived40810 p h) (h 28670)

theorem derived54835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2850) ∨ (¬ p 3905) ∨ (¬ p 4425) ∨ (¬ p 5160) :=
  ElevenRUP.step54835 (p 1976) (p 2027) (p 2589) (p 2764) (p 2850) (p 3905) (p 4425) (p 5160) (h 2136) (derived40810 p h) (derived40882 p h) (h 28672)

theorem derived54841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2246) ∨ (¬ p 2440) ∨ (¬ p 2531) ∨ (¬ p 2608) ∨ (¬ p 2663) ∨ (¬ p 2744) ∨ (¬ p 3083) ∨ (¬ p 3548) ∨ (¬ p 4366) ∨ (¬ p 4902) :=
  ElevenRUP.step54841 (p 2027) (p 2230) (p 2246) (p 2440) (p 2531) (p 2608) (p 2663) (p 2744) (p 3083) (p 3548) (p 4366) (p 4902) (derived40810 p h) (h 28678)

theorem derived54849 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2778) ∨ (¬ p 3553) ∨ (¬ p 3931) ∨ (¬ p 4260) :=
  ElevenRUP.step54849 (p 1976) (p 2027) (p 2313) (p 2633) (p 2778) (p 3553) (p 3931) (p 4260) (h 2136) (derived40810 p h) (derived40879 p h) (h 28688)

theorem derived54853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3941) ∨ (¬ p 4035) ∨ (¬ p 4377) ∨ (¬ p 5119) ∨ (¬ p 5284) :=
  ElevenRUP.step54853 (p 2027) (p 2881) (p 3051) (p 3365) (p 3366) (p 3370) (p 3941) (p 4035) (p 4377) (p 5119) (p 5284) (derived40810 p h) (h 28692)

theorem derived54862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2313) ∨ (¬ p 2383) ∨ (¬ p 3324) ∨ (¬ p 4564) :=
  ElevenRUP.step54862 (p 2027) (p 2274) (p 2313) (p 2383) (p 3324) (p 4564) (derived40810 p h) (h 28705)

theorem derived54864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2534) ∨ (¬ p 2651) ∨ (¬ p 3256) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4121) ∨ (¬ p 4420) :=
  ElevenRUP.step54864 (p 2027) (p 2248) (p 2534) (p 2651) (p 3256) (p 3486) (p 3555) (p 3570) (p 4121) (p 4420) (derived40810 p h) (h 28707)

theorem derived54867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4376) ∨ (¬ p 5113) :=
  ElevenRUP.step54867 (p 2027) (p 2352) (p 2363) (p 2573) (p 2952) (p 3136) (p 3366) (p 3519) (p 4035) (p 4236) (p 4376) (p 5113) (derived40810 p h) (h 28711)

theorem derived54869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2870) ∨ (¬ p 4366) ∨ (¬ p 4875) ∨ (¬ p 4909) :=
  ElevenRUP.step54869 (p 2027) (p 2210) (p 2870) (p 4366) (p 4875) (p 4909) (derived40810 p h) (h 28714)

theorem derived54870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2819) ∨ (¬ p 3956) ∨ (¬ p 4375) ∨ (¬ p 4727) :=
  ElevenRUP.step54870 (p 2027) (p 2579) (p 2819) (p 3956) (p 4375) (p 4727) (derived40810 p h) (h 28715)

theorem derived54871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3422) ∨ (¬ p 3905) ∨ (¬ p 4425) ∨ (¬ p 5160) :=
  ElevenRUP.step54871 (p 1976) (p 2027) (p 2579) (p 2764) (p 3422) (p 3905) (p 4425) (p 5160) (h 2136) (derived40810 p h) (derived40882 p h) (h 28716)

theorem derived54872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3266) ∨ (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 4318) :=
  ElevenRUP.step54872 (p 1988) (p 2027) (p 2363) (p 3266) (p 3449) (p 3591) (p 3818) (p 4318) (h 2148) (derived40810 p h) (derived40905 p h) (h 28719)

theorem derived54875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2839) ∨ (¬ p 3570) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 4169) :=
  ElevenRUP.step54875 (p 1984) (p 2027) (p 2138) (p 2633) (p 2839) (p 3570) (p 3588) (p 3873) (p 4169) (h 2144) (derived40810 p h) (derived40879 p h) (h 28722)

theorem derived54876 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2630) ∨ (¬ p 2657) :=
  ElevenRUP.step54876 (p 1975) (p 2027) (p 2295) (p 2331) (p 2622) (p 2630) (p 2657) (h 2135) (derived40810 p h) (derived40878 p h) (h 28723)

theorem derived54878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 4278) ∨ (¬ p 4381) :=
  ElevenRUP.step54878 (p 1997) (p 2027) (p 2406) (p 2764) (p 3347) (p 3540) (p 4278) (p 4381) (h 2157) (derived40810 p h) (derived40882 p h) (h 28725)

theorem derived54879 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2946) ∨ (¬ p 4117) ∨ (¬ p 4272) ∨ (¬ p 5433) :=
  ElevenRUP.step54879 (p 1990) (p 2027) (p 2563) (p 2611) (p 2946) (p 4117) (p 4272) (p 5433) (h 2150) (derived40810 p h) (derived40877 p h) (h 28727)

theorem derived54880 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2743) ∨ (¬ p 2839) ∨ (¬ p 3880) :=
  ElevenRUP.step54880 (p 1997) (p 2027) (p 2619) (p 2622) (p 2743) (p 2839) (p 3880) (h 2157) (derived40810 p h) (derived40878 p h) (h 28728)

theorem derived54881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3136) ∨ (¬ p 3572) ∨ (¬ p 3691) ∨ (¬ p 4155) ∨ (¬ p 4960) :=
  ElevenRUP.step54881 (p 2027) (p 2891) (p 3136) (p 3572) (p 3691) (p 4155) (p 4960) (derived40810 p h) (h 28729)

theorem derived54882 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2839) ∨ (¬ p 3549) ∨ (¬ p 3953) ∨ (¬ p 4426) ∨ (¬ p 5052) :=
  ElevenRUP.step54882 (p 2027) (p 2122) (p 2839) (p 3549) (p 3953) (p 4426) (p 5052) (derived40810 p h) (h 28730)

theorem derived54883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2829) ∨ (¬ p 3588) ∨ (¬ p 3958) ∨ (¬ p 4390) ∨ (¬ p 4471) :=
  ElevenRUP.step54883 (p 2027) (p 2274) (p 2829) (p 3588) (p 3958) (p 4390) (p 4471) (derived40810 p h) (h 28731)

theorem derived54884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 3609) ∨ (¬ p 3684) ∨ (¬ p 3857) ∨ (¬ p 4197) ∨ (¬ p 4354) ∨ (¬ p 4717) :=
  ElevenRUP.step54884 (p 2027) (p 2386) (p 3609) (p 3684) (p 3857) (p 4197) (p 4354) (p 4717) (derived40810 p h) (h 28732)

theorem derived54885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 3950) ∨ (¬ p 4347) :=
  ElevenRUP.step54885 (p 2027) (p 2248) (p 2901) (p 2946) (p 3246) (p 3591) (p 3923) (p 3950) (p 4347) (derived40810 p h) (h 28734)

theorem derived54888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4370) :=
  ElevenRUP.step54888 (p 1995) (p 2027) (p 2534) (p 3146) (p 3379) (p 3578) (p 3860) (p 4370) (h 2155) (derived40810 p h) (derived40900 p h) (h 28737)

theorem derived54889 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2363) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3591) ∨ (¬ p 4261) ∨ (¬ p 4371) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step54889 (p 2027) (p 2132) (p 2363) (p 2870) (p 2881) (p 3591) (p 4261) (p 4371) (p 4503) (p 4733) (derived40810 p h) (h 28738)

theorem derived54891 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2668) ∨ (¬ p 3947) ∨ (¬ p 4067) ∨ (¬ p 4405) :=
  ElevenRUP.step54891 (p 2027) (p 2396) (p 2668) (p 3947) (p 4067) (p 4405) (derived40810 p h) (h 28741)

theorem derived54892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 3266) ∨ (¬ p 3343) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3742) ∨ (¬ p 4120) ∨ (¬ p 4322) ∨ (¬ p 4332) ∨ (¬ p 4335) :=
  ElevenRUP.step54892 (p 2027) (p 2145) (p 3266) (p 3343) (p 3362) (p 3389) (p 3742) (p 4120) (p 4322) (p 4332) (p 4335) (derived40810 p h) (h 28742)

theorem derived54894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 3986) ∨ (¬ p 4208) ∨ (¬ p 4315) ∨ (¬ p 5043) :=
  ElevenRUP.step54894 (p 2027) (p 2797) (p 3986) (p 4208) (p 4315) (p 5043) (derived40810 p h) (h 28744)

theorem derived54897 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2563) ∨ (¬ p 2807) ∨ (¬ p 3646) ∨ (¬ p 4117) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step54897 (p 2027) (p 2145) (p 2264) (p 2459) (p 2563) (p 2807) (p 3646) (p 4117) (p 4948) (p 5059) (derived40810 p h) (h 28748)

theorem derived54899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 4322) ∨ (¬ p 4363) ∨ (¬ p 4875) ∨ (¬ p 5031) :=
  ElevenRUP.step54899 (p 2027) (p 3670) (p 4322) (p 4363) (p 4875) (p 5031) (derived40810 p h) (h 28750)

theorem derived54904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 3570) ∨ (¬ p 4135) ∨ (¬ p 4244) ∨ (¬ p 4668) :=
  ElevenRUP.step54904 (p 2027) (p 3105) (p 3570) (p 4135) (p 4244) (p 4668) (derived40810 p h) (h 28756)

theorem derived54905 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2352) ∨ (¬ p 2387) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 4137) ∨ (¬ p 4625) ∨ (¬ p 5021) :=
  ElevenRUP.step54905 (p 2027) (p 2241) (p 2352) (p 2387) (p 2449) (p 3027) (p 4137) (p 4625) (p 5021) (derived40810 p h) (h 28758)

theorem derived54909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 3125) ∨ (¬ p 3848) ∨ (¬ p 4190) ∨ (¬ p 4564) :=
  ElevenRUP.step54909 (p 2027) (p 2641) (p 3125) (p 3848) (p 4190) (p 4564) (derived40810 p h) (h 28762)

theorem derived54910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2311) ∨ (¬ p 2785) ∨ (¬ p 3551) ∨ (¬ p 3688) ∨ (¬ p 4107) :=
  ElevenRUP.step54910 (p 1992) (p 2027) (p 2177) (p 2311) (p 2462) (p 2785) (p 3551) (p 3688) (p 4107) (h 2152) (derived40810 p h) (derived40875 p h) (h 28763)

theorem derived54911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2190) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3097) ∨ (¬ p 3366) ∨ (¬ p 3694) ∨ (¬ p 4405) :=
  ElevenRUP.step54911 (p 2027) (p 2138) (p 2190) (p 2247) (p 2744) (p 3063) (p 3093) (p 3097) (p 3366) (p 3694) (p 4405) (derived40810 p h) (h 28764)

theorem derived54913 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3097) ∨ (¬ p 3379) ∨ (¬ p 3646) ∨ (¬ p 4107) ∨ (¬ p 4524) ∨ (¬ p 4666) :=
  ElevenRUP.step54913 (p 2027) (p 2911) (p 2922) (p 3097) (p 3379) (p 3646) (p 4107) (p 4524) (p 4666) (derived40810 p h) (h 28766)

theorem derived54914 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 3359) ∨ (¬ p 3461) ∨ (¬ p 4425) :=
  ElevenRUP.step54914 (p 2005) (p 2027) (p 3016) (p 3128) (p 3359) (p 3461) (p 4425) (h 2165) (derived40810 p h) (derived40894 p h) (h 28767)

theorem derived54915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 3868) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 4786) ∨ (¬ p 4826) :=
  ElevenRUP.step54915 (p 2027) (p 2138) (p 2437) (p 2651) (p 3868) (p 4322) (p 4385) (p 4786) (p 4826) (derived40810 p h) (h 28768)

theorem derived54916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3363) ∨ (¬ p 3585) ∨ (¬ p 4425) :=
  ElevenRUP.step54916 (p 1992) (p 2027) (p 2766) (p 3266) (p 3346) (p 3363) (p 3585) (p 4425) (h 2152) (derived40810 p h) (derived40884 p h) (h 28770)

theorem derived54918 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 3172) ∨ (¬ p 4437) :=
  ElevenRUP.step54918 (p 1987) (p 2027) (p 2534) (p 2651) (p 2766) (p 2810) (p 3172) (p 4437) (h 2147) (derived40810 p h) (derived40884 p h) (h 28773)

theorem derived54919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4381) :=
  ElevenRUP.step54919 (p 1983) (p 2027) (p 2247) (p 2688) (p 3707) (p 3830) (p 4381) (h 2143) (derived40810 p h) (derived40880 p h) (h 28774)

theorem derived54921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3379) ∨ (¬ p 3555) ∨ (¬ p 4134) ∨ (¬ p 5216) :=
  ElevenRUP.step54921 (p 2027) (p 2191) (p 2668) (p 2696) (p 2753) (p 2797) (p 3379) (p 3555) (p 4134) (p 5216) (derived40810 p h) (h 28778)

theorem derived54923 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2589) ∨ (¬ p 2774) ∨ (¬ p 3791) ∨ (¬ p 4322) ∨ (¬ p 4729) ∨ (¬ p 4826) ∨ (¬ p 4948) :=
  ElevenRUP.step54923 (p 2027) (p 2122) (p 2589) (p 2774) (p 3791) (p 4322) (p 4729) (p 4826) (p 4948) (derived40810 p h) (h 28780)

theorem derived54926 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3931) ∨ (¬ p 4322) ∨ (¬ p 4729) ∨ (¬ p 4826) ∨ (¬ p 4948) :=
  ElevenRUP.step54926 (p 2027) (p 2589) (p 2685) (p 2696) (p 3931) (p 4322) (p 4729) (p 4826) (p 4948) (derived40810 p h) (h 28783)

theorem derived54927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 3817) ∨ (¬ p 4366) :=
  ElevenRUP.step54927 (p 1984) (p 2027) (p 2633) (p 3246) (p 3570) (p 3817) (p 4366) (h 2144) (derived40810 p h) (derived40879 p h) (h 28784)

theorem derived54929 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 2901) ∨ (¬ p 3146) ∨ (¬ p 3661) ∨ (¬ p 4118) ∨ (¬ p 4558) :=
  ElevenRUP.step54929 (p 2027) (p 2190) (p 2901) (p 3146) (p 3661) (p 4118) (p 4558) (derived40810 p h) (h 28786)

theorem derived54930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2387) ∨ (¬ p 2630) ∨ (¬ p 2667) ∨ (¬ p 4195) :=
  ElevenRUP.step54930 (p 1994) (p 2027) (p 2352) (p 2387) (p 2630) (p 2667) (p 3008) (p 4195) (h 2154) (derived40810 p h) (derived40891 p h) (h 28787)

theorem derived54932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2563) ∨ (¬ p 3051) ∨ (¬ p 3646) ∨ (¬ p 4140) :=
  ElevenRUP.step54932 (p 1983) (p 2027) (p 2202) (p 2396) (p 2563) (p 3051) (p 3646) (p 4140) (h 2143) (derived40810 p h) (derived40867 p h) (h 28789)

theorem derived54935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2619) ∨ (¬ p 3471) ∨ (¬ p 4120) ∨ (¬ p 4897) :=
  ElevenRUP.step54935 (p 2027) (p 2136) (p 2619) (p 3471) (p 4120) (p 4897) (derived40810 p h) (h 28795)

theorem derived54937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2744) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3193) ∨ (¬ p 3246) ∨ (¬ p 3452) ∨ (¬ p 4641) :=
  ElevenRUP.step54937 (p 2027) (p 2246) (p 2608) (p 2744) (p 2901) (p 2946) (p 3193) (p 3246) (p 3452) (p 4641) (derived40810 p h) (h 28799)

theorem derived54941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2241) ∨ (¬ p 3555) ∨ (¬ p 3692) :=
  ElevenRUP.step54941 (p 1977) (p 2027) (p 2191) (p 2241) (p 2766) (p 3555) (p 3692) (h 2137) (derived40810 p h) (derived40884 p h) (h 28803)

theorem derived54942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3645) ∨ (¬ p 3646) :=
  ElevenRUP.step54942 (p 1998) (p 2027) (p 2202) (p 2563) (p 2881) (p 2891) (p 3645) (p 3646) (h 2158) (derived40810 p h) (derived40867 p h) (h 28804)

theorem derived54943 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 3646) :=
  ElevenRUP.step54943 (p 1998) (p 2027) (p 2202) (p 2563) (p 2881) (p 3051) (p 3646) (h 2158) (derived40810 p h) (derived40867 p h) (h 28805)

theorem derived54947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2870) ∨ (¬ p 3646) ∨ (¬ p 3694) ∨ (¬ p 4558) :=
  ElevenRUP.step54947 (p 2027) (p 2220) (p 2870) (p 3646) (p 3694) (p 4558) (derived40810 p h) (h 28810)

theorem derived54949 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 4075) ∨ (¬ p 4340) ∨ (¬ p 4376) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step54949 (p 2027) (p 2104) (p 3366) (p 3399) (p 3452) (p 4075) (p 4340) (p 4376) (p 4444) (p 4826) (derived40810 p h) (h 28812)

theorem derived54950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3172) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 4075) ∨ (¬ p 4236) ∨ (¬ p 4340) ∨ (¬ p 4376) ∨ (¬ p 4444) ∨ (¬ p 4826) ∨ (¬ p 4967) :=
  ElevenRUP.step54950 (p 2027) (p 3172) (p 3366) (p 3399) (p 3452) (p 4075) (p 4236) (p 4340) (p 4376) (p 4444) (p 4826) (p 4967) (derived40810 p h) (h 28813)

theorem derived54957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2810) ∨ (¬ p 3097) ∨ (¬ p 3136) ∨ (¬ p 3567) ∨ (¬ p 4336) :=
  ElevenRUP.step54957 (p 1990) (p 2027) (p 2307) (p 2545) (p 2810) (p 3097) (p 3136) (p 3567) (p 4336) (h 2150) (derived40810 p h) (derived40876 p h) (h 28820)

theorem derived54958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2274) ∨ (¬ p 3956) ∨ (¬ p 4138) ∨ (¬ p 4203) ∨ (¬ p 4361) :=
  ElevenRUP.step54958 (p 2027) (p 2264) (p 2274) (p 3956) (p 4138) (p 4203) (p 4361) (derived40810 p h) (h 28822)

theorem derived54959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2589) ∨ (¬ p 3389) ∨ (¬ p 4107) :=
  ElevenRUP.step54959 (p 1975) (p 2027) (p 2202) (p 2417) (p 2589) (p 3389) (p 4107) (h 2135) (derived40810 p h) (derived40867 p h) (h 28823)

theorem derived54961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2641) ∨ (¬ p 2656) ∨ (¬ p 3031) ∨ (¬ p 3548) ∨ (¬ p 4975) ∨ (¬ p 5201) :=
  ElevenRUP.step54961 (p 2027) (p 2341) (p 2641) (p 2656) (p 3031) (p 3548) (p 4975) (p 5201) (derived40810 p h) (h 28825)

theorem derived54964 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2963) ∨ (¬ p 3201) ∨ (¬ p 3324) ∨ (¬ p 3589) ∨ (¬ p 3950) ∨ (¬ p 4347) :=
  ElevenRUP.step54964 (p 2027) (p 2254) (p 2417) (p 2598) (p 2963) (p 3201) (p 3324) (p 3589) (p 3950) (p 4347) (derived40810 p h) (h 28828)

theorem derived54966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3537) ∨ (¬ p 3670) ∨ (¬ p 4444) ∨ (¬ p 5344) :=
  ElevenRUP.step54966 (p 1982) (p 2027) (p 2608) (p 2699) (p 3537) (p 3670) (p 4444) (p 5344) (h 2142) (derived40810 p h) (derived40881 p h) (h 28832)

theorem derived54967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 3877) ∨ (¬ p 4437) :=
  ElevenRUP.step54967 (p 1991) (p 2027) (p 2534) (p 2630) (p 2657) (p 2766) (p 3877) (p 4437) (h 2151) (derived40810 p h) (derived40884 p h) (h 28834)

theorem derived54970 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2156) ∨ (¬ p 2748) ∨ (¬ p 2839) ∨ (¬ p 3125) ∨ (¬ p 3365) ∨ (¬ p 4118) ∨ (¬ p 4330) ∨ (¬ p 4360) ∨ (¬ p 4734) :=
  ElevenRUP.step54970 (p 2027) (p 2137) (p 2156) (p 2748) (p 2839) (p 3125) (p 3365) (p 4118) (p 4330) (p 4360) (p 4734) (derived40810 p h) (h 28837)

theorem derived54978 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3367) ∨ (¬ p 3486) ∨ (¬ p 3759) ∨ (¬ p 4399) ∨ (¬ p 4877) :=
  ElevenRUP.step54978 (p 2027) (p 3051) (p 3367) (p 3486) (p 3759) (p 4399) (p 4877) (derived40810 p h) (h 28850)

theorem derived54983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3696) ∨ (¬ p 3758) ∨ (¬ p 3956) ∨ (¬ p 3958) ∨ (¬ p 4113) :=
  ElevenRUP.step54983 (p 2027) (p 2619) (p 3696) (p 3758) (p 3956) (p 3958) (p 4113) (derived40810 p h) (h 28855)

theorem derived54987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2590) ∨ (¬ p 2797) ∨ (¬ p 2810) ∨ (¬ p 3238) ∨ (¬ p 3984) ∨ (¬ p 4811) :=
  ElevenRUP.step54987 (p 2027) (p 2590) (p 2797) (p 2810) (p 3238) (p 3984) (p 4811) (derived40810 p h) (h 28863)

theorem derived54989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3819) ∨ (¬ p 4242) ∨ (¬ p 4340) ∨ (¬ p 4590) ∨ (¬ p 4737) :=
  ElevenRUP.step54989 (p 2027) (p 2088) (p 3819) (p 4242) (p 4340) (p 4590) (p 4737) (derived40810 p h) (h 28865)

theorem derived54990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2780) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4736) :=
  ElevenRUP.step54990 (p 2027) (p 2210) (p 2780) (p 2891) (p 3246) (p 3950) (p 4347) (p 4358) (p 4736) (derived40810 p h) (h 28866)

theorem derived54991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2797) ∨ (¬ p 3027) ∨ (¬ p 3572) :=
  ElevenRUP.step54991 (p 1980) (p 2027) (p 2241) (p 2699) (p 2797) (p 3027) (p 3572) (h 2140) (derived40810 p h) (derived40881 p h) (h 28867)

theorem derived54992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2788) ∨ (¬ p 3319) ∨ (¬ p 3549) ∨ (¬ p 3917) :=
  ElevenRUP.step54992 (p 2027) (p 2307) (p 2788) (p 3319) (p 3549) (p 3917) (derived40810 p h) (h 28868)

theorem derived54993 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2651) ∨ (¬ p 3172) ∨ (¬ p 4111) ∨ (¬ p 4437) :=
  ElevenRUP.step54993 (p 1977) (p 2027) (p 2534) (p 2651) (p 2766) (p 3172) (p 4111) (p 4437) (h 2137) (derived40810 p h) (derived40884 p h) (h 28869)

theorem derived54997 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2210) ∨ (¬ p 3097) ∨ (¬ p 3309) ∨ (¬ p 4338) :=
  ElevenRUP.step54997 (p 1981) (p 2027) (p 2187) (p 2210) (p 2699) (p 3097) (p 3309) (p 4338) (h 2141) (derived40810 p h) (derived40881 p h) (h 28873)

theorem derived54998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2952) ∨ (¬ p 3286) ∨ (¬ p 4379) ∨ (¬ p 5454) :=
  ElevenRUP.step54998 (p 1987) (p 2027) (p 2388) (p 2737) (p 2952) (p 3286) (p 4379) (p 5454) (h 2147) (derived40810 p h) (derived40873 p h) (h 28874)

theorem derived55005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2509) ∨ (¬ p 2553) ∨ (¬ p 4432) ∨ (¬ p 4501) :=
  ElevenRUP.step55005 (p 2027) (p 2493) (p 2509) (p 2553) (p 4432) (p 4501) (derived40810 p h) (h 28882)

theorem derived55006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3551) ∨ (¬ p 4155) :=
  ElevenRUP.step55006 (p 1979) (p 2027) (p 2177) (p 2992) (p 2996) (p 2997) (p 3551) (p 4155) (h 2139) (derived40810 p h) (derived40890 p h) (h 28883)

theorem derived55011 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2972) ∨ (¬ p 3371) ∨ (¬ p 4385) ∨ (¬ p 4734) :=
  ElevenRUP.step55011 (p 2027) (p 2138) (p 2972) (p 3371) (p 4385) (p 4734) (derived40810 p h) (h 28888)

theorem derived55014 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2500) ∨ (¬ p 3063) ∨ (¬ p 3379) ∨ (¬ p 5015) :=
  ElevenRUP.step55014 (p 2027) (p 2387) (p 2500) (p 3063) (p 3379) (p 5015) (derived40810 p h) (h 28891)

theorem derived55022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3189) ∨ (¬ p 3414) ∨ (¬ p 3919) ∨ (¬ p 4111) :=
  ElevenRUP.step55022 (p 1991) (p 2027) (p 2202) (p 2440) (p 3189) (p 3414) (p 3919) (p 4111) (h 2151) (derived40810 p h) (derived40867 p h) (h 28899)

theorem derived55024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2499) ∨ (¬ p 2946) ∨ (¬ p 3256) ∨ (¬ p 3452) ∨ (¬ p 3692) ∨ (¬ p 3956) ∨ (¬ p 4237) ∨ (¬ p 4433) :=
  ElevenRUP.step55024 (p 2027) (p 2248) (p 2499) (p 2946) (p 3256) (p 3452) (p 3692) (p 3956) (p 4237) (p 4433) (derived40810 p h) (h 28901)

theorem derived55025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 4355) ∨ (¬ p 4702) :=
  ElevenRUP.step55025 (p 2027) (p 2528) (p 3497) (p 3692) (p 4355) (p 4702) (derived40810 p h) (h 28902)

theorem derived55028 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2528) ∨ (¬ p 3857) ∨ (¬ p 4197) ∨ (¬ p 4198) ∨ (¬ p 4434) :=
  ElevenRUP.step55028 (p 2027) (p 2220) (p 2528) (p 3857) (p 4197) (p 4198) (p 4434) (derived40810 p h) (h 28905)

theorem derived55033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2737) ∨ (¬ p 2761) ∨ (¬ p 2807) ∨ (¬ p 2811) :=
  ElevenRUP.step55033 (p 1988) (p 2027) (p 2114) (p 2449) (p 2737) (p 2761) (p 2807) (p 2811) (h 2148) (derived40810 p h) (derived40864 p h) (h 28910)

theorem derived55037 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 3156) ∨ (¬ p 3212) ∨ (¬ p 3452) ∨ (¬ p 3956) ∨ (¬ p 4208) ∨ (¬ p 4433) ∨ (¬ p 4521) :=
  ElevenRUP.step55037 (p 2027) (p 2499) (p 3156) (p 3212) (p 3452) (p 3956) (p 4208) (p 4433) (p 4521) (derived40810 p h) (h 28916)

theorem derived55042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2383) ∨ (¬ p 2829) :=
  ElevenRUP.step55042 (p 1981) (p 2027) (p 2114) (p 2122) (p 2313) (p 2383) (p 2829) (h 2141) (derived40810 p h) (derived40864 p h) (h 28921)

theorem derived55044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 2588) ∨ (¬ p 4347) :=
  ElevenRUP.step55044 (p 2003) (p 2027) (p 2387) (p 2510) (p 2528) (p 2588) (p 2997) (p 4347) (h 2163) (derived40810 p h) (derived40890 p h) (h 28923)

theorem derived55049 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 2982) ∨ (¬ p 4110) ∨ (¬ p 4208) :=
  ElevenRUP.step55049 (p 1991) (p 2027) (p 2765) (p 2952) (p 2982) (p 4110) (p 4208) (h 2151) (derived40810 p h) (derived40883 p h) (h 28930)

theorem derived55051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2534) ∨ (¬ p 2608) ∨ (¬ p 2657) ∨ (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 3950) ∨ (¬ p 4256) :=
  ElevenRUP.step55051 (p 2027) (p 2254) (p 2534) (p 2608) (p 2657) (p 2707) (p 3434) (p 3950) (p 4256) (derived40810 p h) (h 28932)

theorem derived55053 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2498) ∨ (¬ p 3319) ∨ (¬ p 3956) ∨ (¬ p 4033) ∨ (¬ p 4208) :=
  ElevenRUP.step55053 (p 1990) (p 2027) (p 2169) (p 2284) (p 2498) (p 3319) (p 3956) (p 4033) (p 4208) (h 2150) (derived40810 p h) (derived40866 p h) (h 28934)

theorem derived55054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2542) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 2659) ∨ (¬ p 3660) :=
  ElevenRUP.step55054 (p 2027) (p 2313) (p 2542) (p 2553) (p 2577) (p 2659) (p 3660) (derived40810 p h) (h 28935)

theorem derived55056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2528) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3452) ∨ (¬ p 3453) ∨ (¬ p 4261) ∨ (¬ p 4438) ∨ (¬ p 4733) :=
  ElevenRUP.step55056 (p 2027) (p 2132) (p 2528) (p 2870) (p 2881) (p 3452) (p 3453) (p 4261) (p 4438) (p 4733) (derived40810 p h) (h 28937)

theorem derived55057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2630) ∨ (¬ p 4111) ∨ (¬ p 4195) :=
  ElevenRUP.step55057 (p 1984) (p 2027) (p 2247) (p 2287) (p 2630) (p 4111) (p 4195) (h 2144) (derived40810 p h) (derived40869 p h) (h 28938)

theorem derived55061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 4340) ∨ (¬ p 4359) :=
  ElevenRUP.step55061 (p 1990) (p 2027) (p 2699) (p 2860) (p 3073) (p 3449) (p 4340) (p 4359) (h 2150) (derived40810 p h) (derived40881 p h) (h 28942)

theorem derived55065 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3189) ∨ (¬ p 3646) ∨ (¬ p 3744) ∨ (¬ p 4009) ∨ (¬ p 4191) ∨ (¬ p 4524) ∨ (¬ p 5119) :=
  ElevenRUP.step55065 (p 2027) (p 2241) (p 3189) (p 3646) (p 3744) (p 4009) (p 4191) (p 4524) (p 5119) (derived40810 p h) (h 28950)

theorem derived55069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 3292) ∨ (¬ p 4190) :=
  ElevenRUP.step55069 (p 1979) (p 2027) (p 2946) (p 2997) (p 3097) (p 3125) (p 3292) (p 4190) (h 2139) (derived40810 p h) (derived40890 p h) (h 28954)

theorem derived55071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2352) ∨ (¬ p 2584) ∨ (¬ p 2588) ∨ (¬ p 3367) ∨ (¬ p 3759) :=
  ElevenRUP.step55071 (p 1981) (p 2027) (p 2114) (p 2307) (p 2352) (p 2584) (p 2588) (p 3367) (p 3759) (h 2141) (derived40810 p h) (derived40864 p h) (h 28956)

theorem derived55082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 4133) ∨ (¬ p 4242) ∨ (¬ p 4340) ∨ (¬ p 4737) :=
  ElevenRUP.step55082 (p 2027) (p 2459) (p 2641) (p 2668) (p 2696) (p 2742) (p 4133) (p 4242) (p 4340) (p 4737) (derived40810 p h) (h 28972)

theorem derived55084 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3379) ∨ (¬ p 3950) ∨ (¬ p 4347) :=
  ElevenRUP.step55084 (p 2027) (p 2254) (p 2417) (p 2922) (p 2963) (p 3324) (p 3379) (p 3950) (p 4347) (derived40810 p h) (h 28976)

theorem derived55085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2737) ∨ (¬ p 3688) ∨ (¬ p 3822) :=
  ElevenRUP.step55085 (p 1987) (p 2027) (p 2299) (p 2633) (p 2737) (p 3688) (p 3822) (h 2147) (derived40810 p h) (derived40879 p h) (h 28977)

theorem derived55086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2737) ∨ (¬ p 2785) ∨ (¬ p 3688) :=
  ElevenRUP.step55086 (p 1987) (p 2027) (p 2299) (p 2313) (p 2633) (p 2737) (p 2785) (p 3688) (h 2147) (derived40810 p h) (derived40879 p h) (h 28978)

theorem derived55087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3548) ∨ (¬ p 3707) ∨ (¬ p 4425) ∨ (¬ p 5363) :=
  ElevenRUP.step55087 (p 2012) (p 2027) (p 2881) (p 2938) (p 3548) (p 3707) (p 4425) (p 5363) (h 2172) (derived40810 p h) (derived40888 p h) (h 28979)

theorem derived55088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2780) ∨ (¬ p 3323) ∨ (¬ p 3917) :=
  ElevenRUP.step55088 (p 1987) (p 2027) (p 2287) (p 2696) (p 2780) (p 3323) (p 3917) (h 2147) (derived40810 p h) (derived40869 p h) (h 28980)

theorem derived55089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2952) ∨ (¬ p 3379) ∨ (¬ p 3744) ∨ (¬ p 3952) ∨ (¬ p 4604) :=
  ElevenRUP.step55089 (p 2027) (p 2254) (p 2518) (p 2528) (p 2952) (p 3379) (p 3744) (p 3952) (p 4604) (derived40810 p h) (h 28981)

theorem derived55090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3125) ∨ (¬ p 4037) ∨ (¬ p 4235) :=
  ElevenRUP.step55090 (p 1980) (p 2027) (p 2563) (p 2938) (p 3125) (p 4037) (p 4235) (h 2140) (derived40810 p h) (derived40888 p h) (h 28982)

theorem derived55092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 4208) ∨ (¬ p 4315) ∨ (¬ p 4318) ∨ (¬ p 4866) ∨ (¬ p 5059) :=
  ElevenRUP.step55092 (p 2027) (p 2363) (p 3365) (p 3366) (p 3449) (p 3591) (p 4208) (p 4315) (p 4318) (p 4866) (p 5059) (derived40810 p h) (h 28984)

theorem derived55098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3146) ∨ (¬ p 3661) ∨ (¬ p 4118) ∨ (¬ p 4241) ∨ (¬ p 4885) :=
  ElevenRUP.step55098 (p 2027) (p 2619) (p 3146) (p 3661) (p 4118) (p 4241) (p 4885) (derived40810 p h) (h 28990)

theorem derived55100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2230) ∨ (¬ p 2579) ∨ (¬ p 3096) ∨ (¬ p 4632) :=
  ElevenRUP.step55100 (p 2027) (p 2192) (p 2230) (p 2579) (p 3096) (p 4632) (derived40810 p h) (h 28992)

theorem derived55101 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2657) ∨ (¬ p 2946) ∨ (¬ p 3574) :=
  ElevenRUP.step55101 (p 1979) (p 2027) (p 2409) (p 2493) (p 2657) (p 2946) (p 3574) (h 2139) (derived40810 p h) (derived40874 p h) (h 28993)

theorem derived55106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2441) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 4278) :=
  ElevenRUP.step55106 (p 1994) (p 2027) (p 2440) (p 2441) (p 2633) (p 3246) (p 3570) (p 4278) (h 2154) (derived40810 p h) (derived40879 p h) (h 28999)

theorem derived55107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 3742) ∨ (¬ p 4278) :=
  ElevenRUP.step55107 (p 1994) (p 2027) (p 2633) (p 3246) (p 3570) (p 3742) (p 4278) (h 2154) (derived40810 p h) (derived40879 p h) (h 29000)

theorem derived55108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 3238) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 4278) :=
  ElevenRUP.step55108 (p 1995) (p 2027) (p 2441) (p 2633) (p 3238) (p 3246) (p 3570) (p 4278) (h 2155) (derived40810 p h) (derived40879 p h) (h 29001)

theorem derived55116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2307) ∨ (¬ p 2440) ∨ (¬ p 2459) ∨ (¬ p 2657) ∨ (¬ p 2781) ∨ (¬ p 4236) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step55116 (p 2027) (p 2177) (p 2307) (p 2440) (p 2459) (p 2657) (p 2781) (p 4236) (p 4948) (p 5059) (derived40810 p h) (h 29010)

theorem derived55119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2437) ∨ (¬ p 2727) ∨ (¬ p 3876) :=
  ElevenRUP.step55119 (p 1986) (p 2027) (p 2241) (p 2437) (p 2699) (p 2727) (p 3876) (h 2146) (derived40810 p h) (derived40881 p h) (h 29014)

theorem derived55122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2493) ∨ (¬ p 2579) ∨ (¬ p 2860) ∨ (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 3556) ∨ (¬ p 4173) ∨ (¬ p 4885) :=
  ElevenRUP.step55122 (p 1984) (p 2027) (p 2230) (p 2409) (p 2493) (p 2579) (p 2860) (p 2891) (p 3369) (p 3556) (p 4173) (p 4885) (h 2144) (derived40810 p h) (derived40874 p h) (h 29023)

theorem derived55123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 3583) ∨ (¬ p 3698) :=
  ElevenRUP.step55123 (p 1981) (p 2027) (p 2542) (p 2545) (p 2819) (p 2829) (p 3583) (p 3698) (h 2141) (derived40810 p h) (derived40876 p h) (h 29024)

theorem derived55128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3662) ∨ (¬ p 3859) ∨ (¬ p 3878) ∨ (¬ p 4118) ∨ (¬ p 4701) :=
  ElevenRUP.step55128 (p 2027) (p 3073) (p 3662) (p 3859) (p 3878) (p 4118) (p 4701) (derived40810 p h) (h 29029)

theorem derived55129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2901) ∨ (¬ p 2950) ∨ (¬ p 3556) ∨ (¬ p 4701) :=
  ElevenRUP.step55129 (p 2027) (p 2651) (p 2901) (p 2950) (p 3556) (p 4701) (derived40810 p h) (h 29031)

theorem derived55130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3347) ∨ (¬ p 3692) ∨ (¬ p 3880) ∨ (¬ p 3954) ∨ (¬ p 4330) ∨ (¬ p 5216) :=
  ElevenRUP.step55130 (p 2027) (p 2589) (p 3093) (p 3319) (p 3347) (p 3692) (p 3880) (p 3954) (p 4330) (p 5216) (derived40810 p h) (h 29032)

theorem derived55133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 3146) ∨ (¬ p 3324) ∨ (¬ p 4347) ∨ (¬ p 4564) :=
  ElevenRUP.step55133 (p 2027) (p 2190) (p 3146) (p 3324) (p 4347) (p 4564) (derived40810 p h) (h 29036)

theorem derived55138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2748) ∨ (¬ p 3365) ∨ (¬ p 3367) ∨ (¬ p 3662) ∨ (¬ p 3759) ∨ (¬ p 3952) ∨ (¬ p 4558) ∨ (¬ p 4734) :=
  ElevenRUP.step55138 (p 2027) (p 2230) (p 2427) (p 2748) (p 3365) (p 3367) (p 3662) (p 3759) (p 3952) (p 4558) (p 4734) (derived40810 p h) (h 29042)

theorem derived55140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2839) ∨ (¬ p 4436) ∨ (¬ p 4998) :=
  ElevenRUP.step55140 (p 2027) (p 2137) (p 2156) (p 2187) (p 2839) (p 4436) (p 4998) (derived40810 p h) (h 29044)

theorem derived55144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2992) ∨ (¬ p 3989) ∨ (¬ p 4111) ∨ (¬ p 4336) :=
  ElevenRUP.step55144 (p 1990) (p 2027) (p 2545) (p 2668) (p 2992) (p 3989) (p 4111) (p 4336) (h 2150) (derived40810 p h) (derived40876 p h) (h 29048)

theorem derived55146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3325) ∨ (¬ p 3644) ∨ (¬ p 3857) ∨ (¬ p 4276) ∨ (¬ p 4403) :=
  ElevenRUP.step55146 (p 2027) (p 2363) (p 3325) (p 3644) (p 3857) (p 4276) (p 4403) (derived40810 p h) (h 29050)

theorem derived55150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3583) ∨ (¬ p 3954) ∨ (¬ p 4340) ∨ (¬ p 4359) :=
  ElevenRUP.step55150 (p 1984) (p 2027) (p 3146) (p 3578) (p 3583) (p 3954) (p 4340) (p 4359) (h 2144) (derived40810 p h) (derived40900 p h) (h 29054)

theorem derived55152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2608) ∨ (¬ p 2641) ∨ (¬ p 2963) ∨ (¬ p 4111) :=
  ElevenRUP.step55152 (p 1992) (p 2027) (p 2245) (p 2545) (p 2608) (p 2641) (p 2963) (p 4111) (h 2152) (derived40810 p h) (derived40876 p h) (h 29056)

theorem derived55153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4348) ∨ (¬ p 4376) ∨ (¬ p 4503) :=
  ElevenRUP.step55153 (p 2027) (p 2470) (p 2528) (p 2608) (p 3519) (p 3591) (p 3923) (p 4348) (p 4376) (p 4503) (derived40810 p h) (h 29057)

theorem derived55155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2743) ∨ (¬ p 2810) ∨ (¬ p 2839) :=
  ElevenRUP.step55155 (p 1976) (p 2027) (p 2138) (p 2545) (p 2743) (p 2810) (p 2839) (h 2136) (derived40810 p h) (derived40876 p h) (h 29059)

theorem derived55160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3641) ∨ (¬ p 4158) ∨ (¬ p 5107) ∨ (¬ p 5160) ∨ (¬ p 5175) :=
  ElevenRUP.step55160 (p 2027) (p 3146) (p 3641) (p 4158) (p 5107) (p 5160) (p 5175) (derived40810 p h) (h 29064)

theorem derived55162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2901) ∨ (¬ p 3212) ∨ (¬ p 3556) ∨ (¬ p 4135) :=
  ElevenRUP.step55162 (p 1988) (p 2027) (p 2388) (p 2761) (p 2901) (p 3212) (p 3556) (p 4135) (h 2148) (derived40810 p h) (derived40873 p h) (h 29066)

theorem derived55163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3550) ∨ (¬ p 3568) ∨ (¬ p 4260) ∨ (¬ p 5559) :=
  ElevenRUP.step55163 (p 2027) (p 2668) (p 3550) (p 3568) (p 4260) (p 5559) (derived40810 p h) (h 29068)

theorem derived55165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 3755) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4367) ∨ (¬ p 5216) :=
  ElevenRUP.step55165 (p 2027) (p 2331) (p 2753) (p 3347) (p 3540) (p 3644) (p 3755) (p 4117) (p 4195) (p 4330) (p 4348) (p 4367) (p 5216) (derived40810 p h) (h 29070)

theorem derived55166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3054) ∨ (¬ p 3097) ∨ (¬ p 3694) ∨ (¬ p 4110) :=
  ElevenRUP.step55166 (p 1986) (p 2027) (p 2373) (p 2997) (p 3054) (p 3097) (p 3694) (p 4110) (h 2146) (derived40810 p h) (derived40890 p h) (h 29071)

theorem derived55167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2743) ∨ (¬ p 2922) ∨ (¬ p 3172) ∨ (¬ p 3361) ∨ (¬ p 3590) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4737) :=
  ElevenRUP.step55167 (p 2027) (p 2417) (p 2598) (p 2743) (p 2922) (p 3172) (p 3361) (p 3590) (p 3950) (p 4118) (p 4737) (derived40810 p h) (h 29072)

theorem derived55168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2499) ∨ (¬ p 3016) ∨ (¬ p 3742) ∨ (¬ p 4644) :=
  ElevenRUP.step55168 (p 2027) (p 2406) (p 2499) (p 3016) (p 3742) (p 4644) (derived40810 p h) (h 29073)

theorem derived55170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 2534) ∨ (¬ p 3115) ∨ (¬ p 3497) ∨ (¬ p 4158) :=
  ElevenRUP.step55170 (p 2027) (p 2532) (p 2534) (p 3115) (p 3497) (p 4158) (derived40810 p h) (h 29075)

theorem derived55174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2363) ∨ (¬ p 2518) ∨ (¬ p 2928) ∨ (¬ p 2963) ∨ (¬ p 3389) ∨ (¬ p 4079) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4596) :=
  ElevenRUP.step55174 (p 2027) (p 2254) (p 2363) (p 2518) (p 2928) (p 2963) (p 3389) (p 4079) (p 4118) (p 4196) (p 4596) (derived40810 p h) (h 29079)

theorem derived55175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2946) ∨ (¬ p 3412) ∨ (¬ p 3684) ∨ (¬ p 4210) ∨ (¬ p 4750) :=
  ElevenRUP.step55175 (p 2027) (p 2657) (p 2946) (p 3412) (p 3684) (p 4210) (p 4750) (derived40810 p h) (h 29080)

theorem derived55177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2819) ∨ (¬ p 2952) ∨ (¬ p 3093) ∨ (¬ p 3570) ∨ (¬ p 3954) ∨ (¬ p 4024) ∨ (¬ p 4133) ∨ (¬ p 4320) :=
  ElevenRUP.step55177 (p 2027) (p 2252) (p 2750) (p 2819) (p 2952) (p 3093) (p 3570) (p 3954) (p 4024) (p 4133) (p 4320) (derived40810 p h) (h 29082)

theorem derived55180 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 4235) :=
  ElevenRUP.step55180 (p 1997) (p 2027) (p 2114) (p 2737) (p 2811) (p 2901) (p 2946) (p 4235) (h 2157) (derived40810 p h) (derived40864 p h) (h 29086)

theorem derived55182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2657) ∨ (¬ p 2807) ∨ (¬ p 2928) ∨ (¬ p 3579) :=
  ElevenRUP.step55182 (p 1997) (p 2027) (p 2406) (p 2545) (p 2657) (p 2807) (p 2928) (p 3579) (h 2157) (derived40810 p h) (derived40876 p h) (h 29088)

theorem derived55184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2787) ∨ (¬ p 2946) ∨ (¬ p 3005) ∨ (¬ p 3956) ∨ (¬ p 4117) ∨ (¬ p 4315) ∨ (¬ p 4771) :=
  ElevenRUP.step55184 (p 2027) (p 2313) (p 2553) (p 2787) (p 2946) (p 3005) (p 3956) (p 4117) (p 4315) (p 4771) (derived40810 p h) (h 29090)

theorem derived55191 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3323) ∨ (¬ p 3324) ∨ (¬ p 4345) ∨ (¬ p 4596) :=
  ElevenRUP.step55191 (p 2027) (p 2534) (p 3323) (p 3324) (p 4345) (p 4596) (derived40810 p h) (h 29098)

theorem derived55192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2807) ∨ (¬ p 3452) ∨ (¬ p 3475) ∨ (¬ p 3572) ∨ (¬ p 3590) :=
  ElevenRUP.step55192 (p 2027) (p 2248) (p 2807) (p 3452) (p 3475) (p 3572) (p 3590) (derived40810 p h) (h 29099)

theorem derived55195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3171) ∨ (¬ p 3998) ∨ (¬ p 4315) ∨ (¬ p 5693) :=
  ElevenRUP.step55195 (p 2023) (p 2027) (p 2388) (p 3005) (p 3171) (p 3998) (p 4315) (p 5693) (h 2183) (derived40810 p h) (derived40873 p h) (h 29102)

theorem derived55196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2685) ∨ (¬ p 2810) ∨ (¬ p 4066) ∨ (¬ p 4235) ∨ (¬ p 4283) :=
  ElevenRUP.step55196 (p 1990) (p 2027) (p 2545) (p 2563) (p 2685) (p 2810) (p 4066) (p 4235) (p 4283) (h 2150) (derived40810 p h) (derived40876 p h) (h 29103)

theorem derived55197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 2534) ∨ (¬ p 3212) ∨ (¬ p 4120) ∨ (¬ p 4158) :=
  ElevenRUP.step55197 (p 2027) (p 2532) (p 2534) (p 3212) (p 4120) (p 4158) (derived40810 p h) (h 29104)

theorem derived55199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2352) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3032) ∨ (¬ p 3422) ∨ (¬ p 3553) ∨ (¬ p 4133) ∨ (¬ p 4366) :=
  ElevenRUP.step55199 (p 2027) (p 2241) (p 2352) (p 2598) (p 2750) (p 2753) (p 3032) (p 3422) (p 3553) (p 4133) (p 4366) (derived40810 p h) (h 29107)

theorem derived55201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2928) ∨ (¬ p 3359) ∨ (¬ p 3402) ∨ (¬ p 4425) :=
  ElevenRUP.step55201 (p 1977) (p 2027) (p 2437) (p 2764) (p 2928) (p 3359) (p 3402) (p 4425) (h 2137) (derived40810 p h) (derived40882 p h) (h 29109)

theorem derived55202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3440) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 3830) ∨ (¬ p 3954) ∨ (¬ p 4181) ∨ (¬ p 5122) :=
  ElevenRUP.step55202 (p 2027) (p 2252) (p 2750) (p 2952) (p 3440) (p 3497) (p 3692) (p 3830) (p 3954) (p 4181) (p 5122) (derived40810 p h) (h 29110)

theorem derived55205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2743) ∨ (¬ p 3361) ∨ (¬ p 3644) ∨ (¬ p 3742) :=
  ElevenRUP.step55205 (p 1992) (p 2027) (p 2633) (p 2657) (p 2743) (p 3361) (p 3644) (p 3742) (h 2152) (derived40810 p h) (derived40879 p h) (h 29113)

theorem derived55215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 3115) ∨ (¬ p 3952) ∨ (¬ p 4137) ∨ (¬ p 5045) :=
  ElevenRUP.step55215 (p 1981) (p 2027) (p 2352) (p 2765) (p 3115) (p 3952) (p 4137) (p 5045) (h 2141) (derived40810 p h) (derived40883 p h) (h 29124)

theorem derived55218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2951) ∨ (¬ p 3027) ∨ (¬ p 3368) ∨ (¬ p 3413) ∨ (¬ p 4173) ∨ (¬ p 4652) :=
  ElevenRUP.step55218 (p 2027) (p 2156) (p 2951) (p 3027) (p 3368) (p 3413) (p 4173) (p 4652) (derived40810 p h) (h 29127)

theorem derived55220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 3506) ∨ (¬ p 3755) ∨ (¬ p 4191) :=
  ElevenRUP.step55220 (p 1999) (p 2027) (p 2545) (p 2810) (p 3506) (p 3755) (p 4191) (h 2159) (derived40810 p h) (derived40876 p h) (h 29130)

theorem derived55224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4736) ∨ (¬ p 5118) :=
  ElevenRUP.step55224 (p 2027) (p 2166) (p 2210) (p 3055) (p 3146) (p 3874) (p 4286) (p 4736) (p 5118) (derived40810 p h) (h 29134)

theorem derived55228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2743) ∨ (¬ p 2952) ∨ (¬ p 3361) ∨ (¬ p 3497) ∨ (¬ p 3609) ∨ (¬ p 4348) ∨ (¬ p 4737) ∨ (¬ p 4905) :=
  ElevenRUP.step55228 (p 2027) (p 2098) (p 2743) (p 2952) (p 3361) (p 3497) (p 3609) (p 4348) (p 4737) (p 4905) (derived40810 p h) (h 29139)

theorem derived55230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3055) ∨ (¬ p 3969) ∨ (¬ p 4425) ∨ (¬ p 4736) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step55230 (p 2027) (p 2166) (p 2210) (p 3055) (p 3969) (p 4425) (p 4736) (p 5119) (p 5160) (derived40810 p h) (h 29142)

theorem derived55231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3055) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 3876) ∨ (¬ p 4786) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step55231 (p 2027) (p 2331) (p 3055) (p 3323) (p 3461) (p 3876) (p 4786) (p 4831) (p 5503) (derived40810 p h) (h 29143)

theorem derived55233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2533) ∨ (¬ p 3680) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4444) :=
  ElevenRUP.step55233 (p 2027) (p 2533) (p 3680) (p 4134) (p 4347) (p 4444) (derived40810 p h) (h 29145)

theorem derived55235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2589) ∨ (¬ p 2744) ∨ (¬ p 2850) ∨ (¬ p 3286) ∨ (¬ p 3366) ∨ (¬ p 3506) ∨ (¬ p 3905) ∨ (¬ p 4444) ∨ (¬ p 4697) ∨ (¬ p 5160) :=
  ElevenRUP.step55235 (p 2027) (p 2246) (p 2589) (p 2744) (p 2850) (p 3286) (p 3366) (p 3506) (p 3905) (p 4444) (p 4697) (p 5160) (derived40810 p h) (h 29147)

theorem derived55236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 3359) ∨ (¬ p 3483) ∨ (¬ p 4022) ∨ (¬ p 5225) :=
  ElevenRUP.step55236 (p 2027) (p 3016) (p 3359) (p 3483) (p 4022) (p 5225) (derived40810 p h) (h 29148)

theorem derived55246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 3073) ∨ (¬ p 3941) ∨ (¬ p 5693) :=
  ElevenRUP.step55246 (p 1982) (p 2027) (p 2911) (p 2914) (p 3073) (p 3941) (p 5693) (h 2142) (derived40810 p h) (derived40887 p h) (h 29159)

theorem derived55248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 2982) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3880) ∨ (¬ p 3947) ∨ (¬ p 4395) :=
  ElevenRUP.step55248 (p 2027) (p 2139) (p 2220) (p 2982) (p 3365) (p 3572) (p 3880) (p 3947) (p 4395) (derived40810 p h) (h 29162)

theorem derived55249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2717) ∨ (¬ p 3880) ∨ (¬ p 3960) ∨ (¬ p 4115) ∨ (¬ p 4898) :=
  ElevenRUP.step55249 (p 2027) (p 2427) (p 2717) (p 3880) (p 3960) (p 4115) (p 4898) (derived40810 p h) (h 29164)

theorem derived55252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3414) ∨ (¬ p 3644) ∨ (¬ p 3868) ∨ (¬ p 4391) :=
  ElevenRUP.step55252 (p 1991) (p 2027) (p 2633) (p 3414) (p 3644) (p 3868) (p 4391) (h 2151) (derived40810 p h) (derived40879 p h) (h 29167)

theorem derived55257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 3156) ∨ (¬ p 3969) ∨ (¬ p 4425) ∨ (¬ p 4786) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step55257 (p 2027) (p 2946) (p 3055) (p 3156) (p 3969) (p 4425) (p 4786) (p 5119) (p 5160) (derived40810 p h) (h 29173)

theorem derived55260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2588) ∨ (¬ p 3574) ∨ (¬ p 4375) ∨ (¬ p 4753) :=
  ElevenRUP.step55260 (p 2027) (p 2122) (p 2588) (p 3574) (p 4375) (p 4753) (derived40810 p h) (h 29176)

theorem derived55261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2299) ∨ (¬ p 2780) ∨ (¬ p 2946) ∨ (¬ p 3189) ∨ (¬ p 3662) ∨ (¬ p 3822) ∨ (¬ p 4311) ∨ (¬ p 4736) ∨ (¬ p 4902) :=
  ElevenRUP.step55261 (p 2027) (p 2253) (p 2299) (p 2780) (p 2946) (p 3189) (p 3662) (p 3822) (p 4311) (p 4736) (p 4902) (derived40810 p h) (h 29177)

theorem derived55262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2982) ∨ (¬ p 2996) ∨ (¬ p 3680) ∨ (¬ p 4391) ∨ (¬ p 4831) ∨ (¬ p 5190) :=
  ElevenRUP.step55262 (p 2027) (p 2230) (p 2247) (p 2982) (p 2996) (p 3680) (p 4391) (p 4831) (p 5190) (derived40810 p h) (h 29178)

theorem derived55263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4604) ∨ (¬ p 5190) :=
  ElevenRUP.step55263 (p 2027) (p 2230) (p 2247) (p 2373) (p 3146) (p 4037) (p 4154) (p 4604) (p 5190) (derived40810 p h) (h 29179)

theorem derived55269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 3105) ∨ (¬ p 3232) ∨ (¬ p 3359) ∨ (¬ p 3694) ∨ (¬ p 4388) :=
  ElevenRUP.step55269 (p 1997) (p 2027) (p 2542) (p 3105) (p 3232) (p 3359) (p 3578) (p 3694) (p 4388) (h 2157) (derived40810 p h) (derived40900 p h) (h 29186)

theorem derived55272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 3552) ∨ (¬ p 3767) ∨ (¬ p 4036) ∨ (¬ p 4429) ∨ (¬ p 4501) ∨ (¬ p 5284) :=
  ElevenRUP.step55272 (p 2027) (p 2387) (p 3552) (p 3767) (p 4036) (p 4429) (p 4501) (p 5284) (derived40810 p h) (h 29189)

theorem derived55273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2497) ∨ (¬ p 2542) ∨ (¬ p 2573) ∨ (¬ p 3519) ∨ (¬ p 3574) ∨ (¬ p 3923) :=
  ElevenRUP.step55273 (p 1997) (p 2027) (p 2169) (p 2497) (p 2542) (p 2573) (p 3519) (p 3574) (p 3923) (h 2157) (derived40810 p h) (derived40866 p h) (h 29190)

theorem derived55275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 4110) ∨ (¬ p 4441) :=
  ElevenRUP.step55275 (p 1975) (p 2027) (p 2373) (p 2765) (p 3309) (p 3923) (p 4110) (p 4441) (h 2135) (derived40810 p h) (derived40883 p h) (h 29192)

theorem derived55276 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2319) ∨ (¬ p 2781) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3461) ∨ (¬ p 3516) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4396) ∨ (¬ p 4444) ∨ (¬ p 5113) :=
  ElevenRUP.step55276 (p 2027) (p 2319) (p 2781) (p 2952) (p 3136) (p 3461) (p 3516) (p 4035) (p 4236) (p 4396) (p 4444) (p 5113) (derived40810 p h) (h 29193)

theorem derived55280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2241) ∨ (¬ p 2284) ∨ (¬ p 3497) ∨ (¬ p 4365) :=
  ElevenRUP.step55280 (p 1990) (p 2027) (p 2166) (p 2241) (p 2284) (p 2699) (p 3497) (p 4365) (h 2150) (derived40810 p h) (derived40881 p h) (h 29197)

theorem derived55281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 3347) ∨ (¬ p 3365) ∨ (¬ p 3609) ∨ (¬ p 4030) ∨ (¬ p 4137) ∨ (¬ p 4604) ∨ (¬ p 4752) :=
  ElevenRUP.step55281 (p 2027) (p 2098) (p 2313) (p 2553) (p 2577) (p 3347) (p 3365) (p 3609) (p 4030) (p 4137) (p 4604) (p 4752) (derived40810 p h) (h 29198)

theorem derived55285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2748) ∨ (¬ p 3365) ∨ (¬ p 3683) ∨ (¬ p 4154) ∨ (¬ p 4972) :=
  ElevenRUP.step55285 (p 2027) (p 2598) (p 2748) (p 3365) (p 3683) (p 4154) (p 4972) (derived40810 p h) (h 29204)

theorem derived55288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2499) ∨ (¬ p 2589) ∨ (¬ p 3389) ∨ (¬ p 4711) :=
  ElevenRUP.step55288 (p 2027) (p 2406) (p 2499) (p 2589) (p 3389) (p 4711) (derived40810 p h) (h 29208)

theorem derived55289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2608) ∨ (¬ p 3537) ∨ (¬ p 4019) ∨ (¬ p 4322) ∨ (¬ p 4948) ∨ (¬ p 5119) ∨ (¬ p 5193) :=
  ElevenRUP.step55289 (p 2027) (p 2589) (p 2608) (p 3537) (p 4019) (p 4322) (p 4948) (p 5119) (p 5193) (derived40810 p h) (h 29210)

theorem derived55290 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2313) ∨ (¬ p 3136) ∨ (¬ p 3177) ∨ (¬ p 3877) ∨ (¬ p 4114) :=
  ElevenRUP.step55290 (p 1979) (p 2027) (p 2274) (p 2313) (p 2765) (p 3136) (p 3177) (p 3877) (p 4114) (h 2139) (derived40810 p h) (derived40883 p h) (h 29211)

theorem derived55293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2922) ∨ (¬ p 3355) ∨ (¬ p 3540) ∨ (¬ p 4451) :=
  ElevenRUP.step55293 (p 1988) (p 2027) (p 2409) (p 2761) (p 2922) (p 3355) (p 3540) (p 4451) (h 2148) (derived40810 p h) (derived40874 p h) (h 29215)

theorem derived55294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2498) ∨ (¬ p 2753) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 3956) ∨ (¬ p 4117) ∨ (¬ p 4348) ∨ (¬ p 4503) ∨ (¬ p 5216) :=
  ElevenRUP.step55294 (p 2027) (p 2498) (p 2753) (p 3166) (p 3256) (p 3379) (p 3591) (p 3956) (p 4117) (p 4348) (p 4503) (p 5216) (derived40810 p h) (h 29217)

theorem derived55295 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2563) ∨ (¬ p 2807) ∨ (¬ p 3005) ∨ (¬ p 3572) ∨ (¬ p 3646) ∨ (¬ p 3880) ∨ (¬ p 4117) ∨ (¬ p 5063) :=
  ElevenRUP.step55295 (p 2027) (p 2145) (p 2563) (p 2807) (p 3005) (p 3572) (p 3646) (p 3880) (p 4117) (p 5063) (derived40810 p h) (h 29218)

theorem derived55296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 3945) ∨ (¬ p 4107) ∨ (¬ p 4902) ∨ (¬ p 5216) :=
  ElevenRUP.step55296 (p 2027) (p 2098) (p 2579) (p 2588) (p 2753) (p 3347) (p 3609) (p 3692) (p 3945) (p 4107) (p 4902) (p 5216) (derived40810 p h) (h 29219)

theorem derived55297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2753) ∨ (¬ p 2946) ∨ (¬ p 3005) ∨ (¬ p 3347) ∨ (¬ p 3945) ∨ (¬ p 4107) ∨ (¬ p 4117) ∨ (¬ p 4311) ∨ (¬ p 4315) ∨ (¬ p 4902) ∨ (¬ p 5216) :=
  ElevenRUP.step55297 (p 2027) (p 2579) (p 2588) (p 2753) (p 2946) (p 3005) (p 3347) (p 3945) (p 4107) (p 4117) (p 4311) (p 4315) (p 4902) (p 5216) (derived40810 p h) (h 29220)

theorem derived55300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 2928) ∨ (¬ p 4001) ∨ (¬ p 4904) :=
  ElevenRUP.step55300 (p 2027) (p 2373) (p 2406) (p 2928) (p 4001) (p 4904) (derived40810 p h) (h 29225)

theorem derived55303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4668) ∨ (¬ p 4733) :=
  ElevenRUP.step55303 (p 2027) (p 2449) (p 2685) (p 2696) (p 3486) (p 3555) (p 3570) (p 4668) (p 4733) (derived40810 p h) (h 29229)

theorem derived55320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3379) ∨ (¬ p 3555) ∨ (¬ p 4363) ∨ (¬ p 5059) ∨ (¬ p 5216) :=
  ElevenRUP.step55320 (p 2027) (p 2363) (p 2753) (p 2774) (p 2819) (p 3379) (p 3555) (p 4363) (p 5059) (p 5216) (derived40810 p h) (h 29251)

theorem derived55321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3830) ∨ (¬ p 3853) ∨ (¬ p 4035) ∨ (¬ p 4366) :=
  ElevenRUP.step55321 (p 1994) (p 2027) (p 2630) (p 3623) (p 3830) (p 3853) (p 4035) (p 4366) (h 2154) (derived40810 p h) (derived40903 p h) (h 29252)

theorem derived55322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 3660) ∨ (¬ p 3758) ∨ (¬ p 3989) ∨ (¬ p 4882) :=
  ElevenRUP.step55322 (p 2027) (p 2352) (p 3660) (p 3758) (p 3989) (p 4882) (derived40810 p h) (h 29253)

theorem derived55325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2839) ∨ (¬ p 3016) ∨ (¬ p 3688) ∨ (¬ p 4342) :=
  ElevenRUP.step55325 (p 1976) (p 2027) (p 2138) (p 2545) (p 2839) (p 3016) (p 3688) (p 4342) (h 2136) (derived40810 p h) (derived40876 p h) (h 29256)

theorem derived55328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 3585) ∨ (¬ p 4278) :=
  ElevenRUP.step55328 (p 2010) (p 2027) (p 2707) (p 2842) (p 3434) (p 3585) (p 4278) (h 2170) (derived40810 p h) (derived40885 p h) (h 29259)

theorem derived55329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2657) ∨ (¬ p 3105) ∨ (¬ p 3680) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 4789) ∨ (¬ p 5123) :=
  ElevenRUP.step55329 (p 2027) (p 2132) (p 2657) (p 3105) (p 3680) (p 4256) (p 4286) (p 4789) (p 5123) (derived40810 p h) (h 29260)

theorem derived55330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3758) :=
  ElevenRUP.step55330 (p 1975) (p 2027) (p 2299) (p 2765) (p 2870) (p 2881) (p 3758) (h 2135) (derived40810 p h) (derived40883 p h) (h 29261)

theorem derived55332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2954) ∨ (¬ p 3005) ∨ (¬ p 4120) ∨ (¬ p 4311) ∨ (¬ p 4315) :=
  ElevenRUP.step55332 (p 2027) (p 2954) (p 3005) (p 4120) (p 4311) (p 4315) (derived40810 p h) (h 29263)

theorem derived55334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 3212) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 3680) ∨ (¬ p 3742) ∨ (¬ p 4191) ∨ (¬ p 4278) ∨ (¬ p 4621) :=
  ElevenRUP.step55334 (p 2027) (p 2252) (p 2657) (p 2750) (p 3212) (p 3370) (p 3371) (p 3680) (p 3742) (p 4191) (p 4278) (p 4621) (derived40810 p h) (h 29265)

theorem derived55335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 3105) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3758) ∨ (¬ p 4348) ∨ (¬ p 4450) :=
  ElevenRUP.step55335 (p 2027) (p 2156) (p 2252) (p 2750) (p 3105) (p 3370) (p 3371) (p 3414) (p 3553) (p 3758) (p 4348) (p 4450) (derived40810 p h) (h 29266)

theorem derived55336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2811) ∨ (¬ p 3166) ∨ (¬ p 3574) ∨ (¬ p 4360) :=
  ElevenRUP.step55336 (p 1977) (p 2027) (p 2810) (p 2811) (p 3008) (p 3166) (p 3574) (p 4360) (h 2137) (derived40810 p h) (derived40891 p h) (h 29267)

theorem derived55338 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2363) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3051) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4244) ∨ (¬ p 4433) :=
  ElevenRUP.step55338 (p 2027) (p 2144) (p 2252) (p 2363) (p 2619) (p 2750) (p 2753) (p 3051) (p 3172) (p 4118) (p 4244) (p 4433) (derived40810 p h) (h 29269)

theorem derived55339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4256) ∨ (¬ p 4789) :=
  ElevenRUP.step55339 (p 2027) (p 2132) (p 2534) (p 2657) (p 2870) (p 3246) (p 3950) (p 4256) (p 4789) (derived40810 p h) (h 29270)

theorem derived55342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2252) ∨ (¬ p 2741) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 2982) ∨ (¬ p 3324) ∨ (¬ p 3680) ∨ (¬ p 4419) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step55342 (p 2027) (p 2230) (p 2252) (p 2741) (p 2753) (p 2963) (p 2982) (p 3324) (p 3680) (p 4419) (p 5123) (p 5580) (derived40810 p h) (h 29273)

theorem derived55344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3641) ∨ (¬ p 3876) :=
  ElevenRUP.step55344 (p 1982) (p 2027) (p 2528) (p 2611) (p 3362) (p 3389) (p 3641) (p 3876) (h 2142) (derived40810 p h) (derived40877 p h) (h 29275)

theorem derived55346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2341) ∨ (¬ p 2459) ∨ (¬ p 2952) ∨ (¬ p 3027) ∨ (¬ p 3744) ∨ (¬ p 4066) ∨ (¬ p 4173) ∨ (¬ p 4282) ∨ (¬ p 4604) :=
  ElevenRUP.step55346 (p 2027) (p 2249) (p 2341) (p 2459) (p 2952) (p 3027) (p 3744) (p 4066) (p 4173) (p 4282) (p 4604) (derived40810 p h) (h 29277)

theorem derived55348 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2166) ∨ (¬ p 2534) ∨ (¬ p 3696) ∨ (¬ p 4607) ∨ (¬ p 4632) :=
  ElevenRUP.step55348 (p 2027) (p 2088) (p 2166) (p 2534) (p 3696) (p 4607) (p 4632) (derived40810 p h) (h 29279)

theorem derived55349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2641) ∨ (¬ p 2717) ∨ (¬ p 2963) ∨ (¬ p 2996) ∨ (¬ p 3471) ∨ (¬ p 3570) ∨ (¬ p 4362) ∨ (¬ p 4733) :=
  ElevenRUP.step55349 (p 2027) (p 2245) (p 2641) (p 2717) (p 2963) (p 2996) (p 3471) (p 3570) (p 4362) (p 4733) (derived40810 p h) (h 29281)

end ElevenLogic
