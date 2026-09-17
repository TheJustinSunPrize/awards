import SunPrize.Certificate.Derived021
import SunPrize.Certificate.Logic022
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived64108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3549) ∨ (¬ p 3922) ∨ (¬ p 3956) ∨ (¬ p 4195) :=
  ElevenRUP.step64108 (p 1987) (p 2027) (p 2169) (p 2553) (p 3549) (p 3922) (p 3956) (p 4195) (h 2147) (derived40810 p h) (derived40866 p h) (h 39494)

theorem derived64110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 2663) ∨ (¬ p 2811) ∨ (¬ p 2839) ∨ (¬ p 4257) ∨ (¬ p 5052) :=
  ElevenRUP.step64110 (p 2027) (p 2499) (p 2573) (p 2663) (p 2811) (p 2839) (p 4257) (p 5052) (derived40810 p h) (h 39496)

theorem derived64113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3073) ∨ (¬ p 4169) ∨ (¬ p 4189) ∨ (¬ p 4253) ∨ (¬ p 4347) ∨ (¬ p 4442) :=
  ElevenRUP.step64113 (p 1981) (p 2027) (p 2202) (p 2427) (p 3073) (p 4169) (p 4189) (p 4253) (p 4347) (p 4442) (h 2141) (derived40810 p h) (derived40867 p h) (h 39499)

theorem derived64118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3347) ∨ (¬ p 3365) ∨ (¬ p 3540) ∨ (¬ p 3619) ∨ (¬ p 3644) ∨ (¬ p 3670) ∨ (¬ p 4030) ∨ (¬ p 4752) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64118 (p 2027) (p 3347) (p 3365) (p 3540) (p 3619) (p 3644) (p 3670) (p 4030) (p 4752) (p 5123) (p 5558) (derived40810 p h) (h 39505)

theorem derived64120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2299) ∨ (¬ p 2331) ∨ (¬ p 3189) ∨ (¬ p 4154) ∨ (¬ p 4378) :=
  ElevenRUP.step64120 (p 1975) (p 2027) (p 2253) (p 2299) (p 2331) (p 2699) (p 3189) (p 4154) (p 4378) (h 2135) (derived40810 p h) (derived40881 p h) (h 39507)

theorem derived64123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3204) ∨ (¬ p 3309) ∨ (¬ p 3743) ∨ (¬ p 3880) ∨ (¬ p 4501) ∨ (¬ p 4506) :=
  ElevenRUP.step64123 (p 2027) (p 2563) (p 3204) (p 3309) (p 3743) (p 3880) (p 4501) (p 4506) (derived40810 p h) (h 39510)

theorem derived64132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (¬ p 3125) ∨ (¬ p 3848) ∨ (¬ p 4190) :=
  ElevenRUP.step64132 (p 1975) (p 2027) (p 2295) (p 2641) (p 2765) (p 3125) (p 3848) (p 4190) (h 2135) (derived40810 p h) (derived40883 p h) (h 39521)

theorem derived64133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 4187) ∨ (p 4620) :=
  ElevenRUP.step64133 (p 1992) (p 2608) (p 2699) (p 4187) (p 4620) (h 2152) (derived40881 p h) (h 39522)

theorem derived64134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2992) ∨ (¬ p 3745) ∨ (¬ p 4154) ∨ (¬ p 4702) :=
  ElevenRUP.step64134 (p 2027) (p 2563) (p 2992) (p 3745) (p 4154) (p 4702) (derived40810 p h) (h 39523)

theorem derived64136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2440) ∨ (¬ p 3569) ∨ (¬ p 4110) ∨ (¬ p 4558) :=
  ElevenRUP.step64136 (p 2027) (p 2437) (p 2440) (p 3569) (p 4110) (p 4558) (derived40810 p h) (h 39525)

theorem derived64137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2476) ∨ (¬ p 2744) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3641) ∨ (¬ p 3905) ∨ (¬ p 4641) ∨ (¬ p 5160) :=
  ElevenRUP.step64137 (p 2027) (p 2246) (p 2476) (p 2744) (p 2901) (p 2946) (p 3246) (p 3366) (p 3641) (p 3905) (p 4641) (p 5160) (derived40810 p h) (h 39526)

theorem derived64140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 3016) ∨ (¬ p 3266) ∨ (¬ p 3366) ∨ (¬ p 3564) ∨ (¬ p 3820) ∨ (¬ p 3821) ∨ (¬ p 4330) ∨ (¬ p 4381) :=
  ElevenRUP.step64140 (p 2027) (p 2246) (p 2651) (p 2744) (p 3016) (p 3266) (p 3366) (p 3564) (p 3820) (p 3821) (p 4330) (p 4381) (derived40810 p h) (h 39529)

theorem derived64141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 3016) ∨ (¬ p 3366) ∨ (¬ p 3551) ∨ (¬ p 3820) ∨ (¬ p 3888) ∨ (¬ p 4348) ∨ (¬ p 4444) ∨ (¬ p 5250) :=
  ElevenRUP.step64141 (p 2027) (p 2246) (p 2651) (p 2744) (p 3016) (p 3366) (p 3551) (p 3820) (p 3888) (p 4348) (p 4444) (p 5250) (derived40810 p h) (h 39530)

theorem derived64142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3572) ∨ (¬ p 4063) ∨ (¬ p 4104) ∨ (¬ p 4391) ∨ (¬ p 4790) :=
  ElevenRUP.step64142 (p 2027) (p 3572) (p 4063) (p 4104) (p 4391) (p 4790) (derived40810 p h) (h 39531)

theorem derived64144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2459) ∨ (¬ p 2534) ∨ (¬ p 2946) ∨ (¬ p 3005) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 4186) ∨ (¬ p 4311) ∨ (¬ p 4315) ∨ (¬ p 4813) ∨ (¬ p 4902) :=
  ElevenRUP.step64144 (p 2027) (p 2246) (p 2459) (p 2534) (p 2946) (p 3005) (p 3347) (p 3540) (p 4186) (p 4311) (p 4315) (p 4813) (p 4902) (derived40810 p h) (h 39533)

theorem derived64145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2220) ∨ (¬ p 2839) ∨ (¬ p 2928) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 4030) ∨ (¬ p 4278) ∨ (¬ p 4669) ∨ (¬ p 4734) :=
  ElevenRUP.step64145 (p 2027) (p 2137) (p 2220) (p 2839) (p 2928) (p 3055) (p 3146) (p 4030) (p 4278) (p 4669) (p 4734) (derived40810 p h) (h 39534)

theorem derived64146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3016) ∨ (¬ p 3425) ∨ (¬ p 3564) ∨ (¬ p 3659) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4786) :=
  ElevenRUP.step64146 (p 2027) (p 2651) (p 3016) (p 3425) (p 3564) (p 3659) (p 4330) (p 4348) (p 4786) (derived40810 p h) (h 39535)

theorem derived64152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3817) ∨ (¬ p 4228) ∨ (¬ p 4366) ∨ (¬ p 4381) ∨ (¬ p 4733) ∨ (¬ p 5250) :=
  ElevenRUP.step64152 (p 2027) (p 2696) (p 2797) (p 3817) (p 4228) (p 4366) (p 4381) (p 4733) (p 5250) (derived40810 p h) (h 39541)

theorem derived64157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 2553) ∨ (¬ p 3238) ∨ (¬ p 3422) ∨ (¬ p 3874) :=
  ElevenRUP.step64157 (p 1975) (p 2027) (p 2202) (p 2518) (p 2553) (p 3238) (p 3422) (p 3874) (h 2135) (derived40810 p h) (derived40867 p h) (h 39546)

theorem derived64158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2742) ∨ (¬ p 4782) :=
  ElevenRUP.step64158 (p 2027) (p 2247) (p 2608) (p 2707) (p 2742) (p 4782) (derived40810 p h) (h 39547)

theorem derived64160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2810) ∨ (¬ p 3574) ∨ (¬ p 3579) ∨ (¬ p 4711) :=
  ElevenRUP.step64160 (p 2027) (p 2685) (p 2810) (p 3574) (p 3579) (p 4711) (derived40810 p h) (h 39550)

theorem derived64165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3619) ∨ (¬ p 3670) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4444) ∨ (¬ p 4669) ∨ (¬ p 5216) :=
  ElevenRUP.step64165 (p 2027) (p 2753) (p 3379) (p 3619) (p 3670) (p 3817) (p 4366) (p 4444) (p 4669) (p 5216) (derived40810 p h) (h 39558)

theorem derived64167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3564) ∨ (¬ p 3690) ∨ (¬ p 4621) :=
  ElevenRUP.step64167 (p 2027) (p 2248) (p 2651) (p 3016) (p 3486) (p 3555) (p 3564) (p 3690) (p 4621) (derived40810 p h) (h 39560)

theorem derived64168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3038) ∨ (¬ p 3631) ∨ (¬ p 3662) ∨ (¬ p 3947) ∨ (¬ p 4112) ∨ (¬ p 4701) :=
  ElevenRUP.step64168 (p 2027) (p 3038) (p 3631) (p 3662) (p 3947) (p 4112) (p 4701) (derived40810 p h) (h 39561)

theorem derived64170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2459) ∨ (¬ p 2619) ∨ (¬ p 3758) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4521) ∨ (¬ p 4902) :=
  ElevenRUP.step64170 (p 2027) (p 2156) (p 2459) (p 2619) (p 3758) (p 3860) (p 4261) (p 4521) (p 4902) (derived40810 p h) (h 39563)

theorem derived64171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3692) ∨ (¬ p 4173) ∨ (¬ p 4496) ∨ (¬ p 4509) :=
  ElevenRUP.step64171 (p 2027) (p 3073) (p 3692) (p 4173) (p 4496) (p 4509) (derived40810 p h) (h 39564)

theorem derived64174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3542) ∨ (¬ p 3830) ∨ (¬ p 3860) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 5152) :=
  ElevenRUP.step64174 (p 2027) (p 3542) (p 3830) (p 3860) (p 4330) (p 4348) (p 5152) (derived40810 p h) (h 39568)

theorem derived64176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2499) ∨ (¬ p 3452) ∨ (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 3956) ∨ (¬ p 4433) ∨ (¬ p 4733) :=
  ElevenRUP.step64176 (p 2027) (p 2098) (p 2499) (p 3452) (p 3609) (p 3692) (p 3956) (p 4433) (p 4733) (derived40810 p h) (h 39570)

theorem derived64179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3204) ∨ (¬ p 3956) ∨ (¬ p 4433) ∨ (¬ p 4870) :=
  ElevenRUP.step64179 (p 2027) (p 2313) (p 2553) (p 2696) (p 2753) (p 3136) (p 3156) (p 3204) (p 3956) (p 4433) (p 4870) (derived40810 p h) (h 39573)

theorem derived64183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2753) ∨ (¬ p 2927) ∨ (¬ p 3266) ∨ (¬ p 3379) ∨ (¬ p 3609) ∨ (¬ p 4366) ∨ (¬ p 4831) ∨ (¬ p 5216) ∨ (¬ p 5503) :=
  ElevenRUP.step64183 (p 2027) (p 2098) (p 2753) (p 2927) (p 3266) (p 3379) (p 3609) (p 4366) (p 4831) (p 5216) (p 5503) (derived40810 p h) (h 39577)

theorem derived64184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 4195) :=
  ElevenRUP.step64184 (p 2001) (p 2027) (p 2323) (p 2331) (p 3136) (p 3156) (p 4195) (h 2161) (derived40810 p h) (derived40870 p h) (h 39578)

theorem derived64188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 3246) ∨ (¬ p 3821) ∨ (¬ p 4559) :=
  ElevenRUP.step64188 (p 2027) (p 2299) (p 2341) (p 3246) (p 3821) (p 4559) (derived40810 p h) (h 39584)

theorem derived64190 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2449) ∨ (¬ p 2737) ∨ (¬ p 2807) ∨ (¬ p 2811) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4734) :=
  ElevenRUP.step64190 (p 2027) (p 2138) (p 2449) (p 2737) (p 2807) (p 2811) (p 3692) (p 3694) (p 3950) (p 4734) (derived40810 p h) (h 39586)

theorem derived64193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2927) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 3379) ∨ (¬ p 4278) ∨ (¬ p 4366) ∨ (¬ p 4395) ∨ (¬ p 5216) :=
  ElevenRUP.step64193 (p 2027) (p 2696) (p 2753) (p 2927) (p 3115) (p 3136) (p 3379) (p 4278) (p 4366) (p 4395) (p 5216) (derived40810 p h) (h 39590)

theorem derived64194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 2717) ∨ (¬ p 3551) ∨ (¬ p 4195) ∨ (¬ p 4336) ∨ (¬ p 4701) ∨ (¬ p 4781) ∨ (¬ p 5197) :=
  ElevenRUP.step64194 (p 2027) (p 2662) (p 2717) (p 3551) (p 4195) (p 4336) (p 4701) (p 4781) (p 5197) (derived40810 p h) (h 39591)

theorem derived64197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 3136) ∨ (¬ p 3654) ∨ (¬ p 4035) ∨ (¬ p 4190) :=
  ElevenRUP.step64197 (p 1979) (p 2027) (p 2169) (p 2387) (p 3136) (p 3654) (p 4035) (p 4190) (h 2139) (derived40810 p h) (derived40866 p h) (h 39594)

theorem derived64203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 3923) :=
  ElevenRUP.step64203 (p 1995) (p 2027) (p 2187) (p 2765) (p 3379) (p 3591) (p 3923) (h 2155) (derived40810 p h) (derived40883 p h) (h 39602)

theorem derived64204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 2952) ∨ (¬ p 3952) :=
  ElevenRUP.step64204 (p 1987) (p 2027) (p 2651) (p 2765) (p 2810) (p 2952) (p 3952) (h 2147) (derived40810 p h) (derived40883 p h) (h 39603)

theorem derived64207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2667) ∨ (¬ p 3136) ∨ (¬ p 3957) ∨ (¬ p 4195) ∨ (¬ p 4702) ∨ (¬ p 5016) :=
  ElevenRUP.step64207 (p 2027) (p 2563) (p 2667) (p 3136) (p 3957) (p 4195) (p 4702) (p 5016) (derived40810 p h) (h 39607)

theorem derived64210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 3609) ∨ (¬ p 3644) ∨ (¬ p 3692) ∨ (¬ p 4733) ∨ (¬ p 4902) :=
  ElevenRUP.step64210 (p 2027) (p 2098) (p 2928) (p 3452) (p 3609) (p 3644) (p 3692) (p 4733) (p 4902) (derived40810 p h) (h 39610)

theorem derived64211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 2761) ∨ (¬ p 2774) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 4110) ∨ (¬ p 4733) :=
  ElevenRUP.step64211 (p 1988) (p 2027) (p 2122) (p 2396) (p 2761) (p 2765) (p 2774) (p 3238) (p 3452) (p 4110) (p 4733) (h 2148) (derived40810 p h) (derived40883 p h) (h 39611)

theorem derived64215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 3619) ∨ (¬ p 3670) ∨ (¬ p 4026) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 5216) :=
  ElevenRUP.step64215 (p 2027) (p 2753) (p 3379) (p 3591) (p 3619) (p 3670) (p 4026) (p 4444) (p 4604) (p 5216) (derived40810 p h) (h 39616)

theorem derived64219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2788) ∨ (¬ p 3998) ∨ (¬ p 4114) ∨ (¬ p 4358) ∨ (¬ p 5580) :=
  ElevenRUP.step64219 (p 2027) (p 2788) (p 3998) (p 4114) (p 4358) (p 5580) (derived40810 p h) (h 39620)

theorem derived64221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2748) ∨ (¬ p 2839) ∨ (¬ p 2996) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 4668) ∨ (¬ p 4734) :=
  ElevenRUP.step64221 (p 2027) (p 2137) (p 2748) (p 2839) (p 2996) (p 3051) (p 3246) (p 3365) (p 3553) (p 4668) (p 4734) (derived40810 p h) (h 39622)

theorem derived64222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3324) ∨ (¬ p 3998) ∨ (¬ p 4114) ∨ (¬ p 4584) ∨ (¬ p 5580) :=
  ElevenRUP.step64222 (p 2027) (p 3324) (p 3998) (p 4114) (p 4584) (p 5580) (derived40810 p h) (h 39623)

theorem derived64224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2427) ∨ (¬ p 2630) ∨ (¬ p 3556) ∨ (¬ p 4110) ∨ (¬ p 4392) :=
  ElevenRUP.step64224 (p 1994) (p 2027) (p 2143) (p 2427) (p 2630) (p 2765) (p 3556) (p 4110) (p 4392) (h 2154) (derived40810 p h) (derived40883 p h) (h 39625)

theorem derived64225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 2891) ∨ (¬ p 3556) ∨ (¬ p 3904) ∨ (¬ p 4154) ∨ (¬ p 4365) ∨ (¬ p 4972) :=
  ElevenRUP.step64225 (p 2027) (p 2662) (p 2891) (p 3556) (p 3904) (p 4154) (p 4365) (p 4972) (derived40810 p h) (h 39626)

theorem derived64227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2662) ∨ (¬ p 3904) ∨ (¬ p 4120) ∨ (¬ p 4154) ∨ (¬ p 4365) ∨ (¬ p 4972) :=
  ElevenRUP.step64227 (p 2027) (p 2166) (p 2662) (p 3904) (p 4120) (p 4154) (p 4365) (p 4972) (derived40810 p h) (h 39628)

theorem derived64229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2630) ∨ (¬ p 3361) ∨ (¬ p 3414) ∨ (¬ p 3947) :=
  ElevenRUP.step64229 (p 1994) (p 2027) (p 2417) (p 2630) (p 2914) (p 3361) (p 3414) (p 3947) (h 2154) (derived40810 p h) (derived40887 p h) (h 39630)

theorem derived64231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2744) ∨ (¬ p 3323) ∨ (¬ p 3366) ∨ (¬ p 3461) ∨ (¬ p 3694) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64231 (p 2027) (p 2138) (p 2246) (p 2331) (p 2744) (p 3323) (p 3366) (p 3461) (p 3694) (p 5123) (p 5568) (derived40810 p h) (h 39632)

theorem derived64232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2248) ∨ (¬ p 2264) ∨ (¬ p 2299) ∨ (¬ p 2331) ∨ (¬ p 3537) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 4156) ∨ (¬ p 4477) :=
  ElevenRUP.step64232 (p 2027) (p 2104) (p 2248) (p 2264) (p 2299) (p 2331) (p 3537) (p 3588) (p 3873) (p 4156) (p 4477) (derived40810 p h) (h 39633)

theorem derived64233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3366) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 3905) ∨ (¬ p 4330) ∨ (¬ p 4348) :=
  ElevenRUP.step64233 (p 2027) (p 2247) (p 2744) (p 3093) (p 3319) (p 3366) (p 3540) (p 3644) (p 3905) (p 4330) (p 4348) (derived40810 p h) (h 39634)

theorem derived64235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2534) ∨ (¬ p 2744) ∨ (¬ p 3055) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3366) ∨ (¬ p 3874) ∨ (¬ p 4330) :=
  ElevenRUP.step64235 (p 2027) (p 2247) (p 2534) (p 2744) (p 3055) (p 3093) (p 3319) (p 3366) (p 3874) (p 4330) (derived40810 p h) (h 39636)

theorem derived64237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 3204) ∨ (¬ p 3644) ∨ (¬ p 4348) ∨ (¬ p 4450) ∨ (¬ p 4710) ∨ (¬ p 4870) :=
  ElevenRUP.step64237 (p 2027) (p 2313) (p 2696) (p 2753) (p 3115) (p 3136) (p 3204) (p 3644) (p 4348) (p 4450) (p 4710) (p 4870) (derived40810 p h) (h 39638)

theorem derived64238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2247) ∨ (¬ p 2589) ∨ (¬ p 2744) ∨ (¬ p 2850) ∨ (¬ p 2891) ∨ (¬ p 3096) ∨ (¬ p 3366) ∨ (¬ p 3584) ∨ (¬ p 3905) ∨ (¬ p 4558) :=
  ElevenRUP.step64238 (p 2027) (p 2210) (p 2247) (p 2589) (p 2744) (p 2850) (p 2891) (p 3096) (p 3366) (p 3584) (p 3905) (p 4558) (derived40810 p h) (h 39639)

theorem derived64242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2850) ∨ (¬ p 3096) ∨ (¬ p 3584) ∨ (¬ p 4509) :=
  ElevenRUP.step64242 (p 2027) (p 2373) (p 2850) (p 3096) (p 3584) (p 4509) (derived40810 p h) (h 39643)

theorem derived64254 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2132) ∨ (¬ p 2396) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 3985) ∨ (¬ p 4261) ∨ (¬ p 5216) :=
  ElevenRUP.step64254 (p 2027) (p 2122) (p 2132) (p 2396) (p 2753) (p 3379) (p 3860) (p 3950) (p 3985) (p 4261) (p 5216) (derived40810 p h) (h 39655)

theorem derived64256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2476) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3641) ∨ (¬ p 3905) ∨ (¬ p 4641) ∨ (¬ p 5160) :=
  ElevenRUP.step64256 (p 2027) (p 2247) (p 2476) (p 2744) (p 3366) (p 3399) (p 3631) (p 3641) (p 3905) (p 4641) (p 5160) (derived40810 p h) (h 39657)

theorem derived64265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3379) ∨ (¬ p 3690) ∨ (¬ p 4366) ∨ (¬ p 4666) ∨ (¬ p 4909) ∨ (¬ p 5216) :=
  ElevenRUP.step64265 (p 2027) (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 3690) (p 4366) (p 4666) (p 4909) (p 5216) (derived40810 p h) (h 39667)

theorem derived64266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3379) ∨ (¬ p 4366) ∨ (¬ p 4442) ∨ (¬ p 5216) ∨ (¬ p 5559) :=
  ElevenRUP.step64266 (p 2027) (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 4366) (p 4442) (p 5216) (p 5559) (derived40810 p h) (h 39668)

theorem derived64267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3379) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) ∨ (¬ p 5216) :=
  ElevenRUP.step64267 (p 2027) (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 3817) (p 4366) (p 4666) (p 5216) (derived40810 p h) (h 39669)

theorem derived64270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3947) :=
  ElevenRUP.step64270 (p 1998) (p 2027) (p 2202) (p 2264) (p 2427) (p 3246) (p 3947) (h 2158) (derived40810 p h) (derived40867 p h) (h 39676)

theorem derived64271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 3333) ∨ (¬ p 3346) ∨ (¬ p 3874) ∨ (¬ p 3905) ∨ (¬ p 4438) ∨ (¬ p 4786) :=
  ElevenRUP.step64271 (p 2027) (p 2177) (p 2295) (p 2331) (p 3333) (p 3346) (p 3874) (p 3905) (p 4438) (p 4786) (derived40810 p h) (h 39678)

theorem derived64273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 4129) ∨ (¬ p 4425) ∨ (¬ p 4786) ∨ (¬ p 4826) ∨ (¬ p 5160) :=
  ElevenRUP.step64273 (p 2027) (p 2901) (p 2946) (p 3055) (p 4129) (p 4425) (p 4786) (p 4826) (p 5160) (derived40810 p h) (h 39680)

theorem derived64290 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4330) ∨ (¬ p 4348) :=
  ElevenRUP.step64290 (p 2027) (p 2247) (p 2744) (p 3093) (p 3319) (p 3366) (p 3425) (p 3659) (p 4330) (p 4348) (derived40810 p h) (h 39697)

theorem derived64291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 3105) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3347) ∨ (¬ p 3371) ∨ (¬ p 3758) ∨ (¬ p 4425) ∨ (¬ p 4450) ∨ (¬ p 5216) :=
  ElevenRUP.step64291 (p 2027) (p 2192) (p 3105) (p 3266) (p 3346) (p 3347) (p 3371) (p 3758) (p 4425) (p 4450) (p 5216) (derived40810 p h) (h 39699)

theorem derived64292 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4330) ∨ (¬ p 5216) :=
  ElevenRUP.step64292 (p 2027) (p 2696) (p 2753) (p 2797) (p 3323) (p 3379) (p 3860) (p 4261) (p 4330) (p 5216) (derived40810 p h) (h 39700)

theorem derived64294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3506) ∨ (¬ p 3860) ∨ (¬ p 4117) ∨ (¬ p 4191) ∨ (¬ p 4261) ∨ (¬ p 4330) ∨ (¬ p 4421) ∨ (¬ p 5216) :=
  ElevenRUP.step64294 (p 2027) (p 2331) (p 2753) (p 3379) (p 3506) (p 3860) (p 4117) (p 4191) (p 4261) (p 4330) (p 4421) (p 5216) (derived40810 p h) (h 39702)

theorem derived64298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2299) ∨ (¬ p 2531) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 4902) ∨ (¬ p 5190) :=
  ElevenRUP.step64298 (p 2027) (p 2230) (p 2299) (p 2531) (p 3549) (p 3591) (p 3641) (p 3684) (p 4902) (p 5190) (derived40810 p h) (h 39706)

theorem derived64299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 3662) ∨ (¬ p 4208) ∨ (¬ p 5059) ∨ (¬ p 5190) :=
  ElevenRUP.step64299 (p 2027) (p 2247) (p 2352) (p 2363) (p 2573) (p 3662) (p 4208) (p 5059) (p 5190) (derived40810 p h) (h 39707)

theorem derived64303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2563) ∨ (¬ p 3125) ∨ (¬ p 3568) ∨ (¬ p 4154) ∨ (¬ p 4624) ∨ (¬ p 5190) :=
  ElevenRUP.step64303 (p 2027) (p 2230) (p 2247) (p 2563) (p 3125) (p 3568) (p 4154) (p 4624) (p 5190) (derived40810 p h) (h 39711)

theorem derived64306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2383) ∨ (¬ p 2996) ∨ (¬ p 3564) ∨ (¬ p 3947) ∨ (¬ p 3956) ∨ (¬ p 4621) ∨ (¬ p 5017) :=
  ElevenRUP.step64306 (p 2027) (p 2247) (p 2383) (p 2996) (p 3564) (p 3947) (p 3956) (p 4621) (p 5017) (derived40810 p h) (h 39715)

theorem derived64307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2247) ∨ (¬ p 2982) ∨ (¬ p 2996) ∨ (¬ p 3880) ∨ (¬ p 3947) ∨ (¬ p 4395) ∨ (¬ p 4521) :=
  ElevenRUP.step64307 (p 2027) (p 2220) (p 2247) (p 2982) (p 2996) (p 3880) (p 3947) (p 4395) (p 4521) (derived40810 p h) (h 39716)

theorem derived64308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 3585) ∨ (¬ p 4107) :=
  ElevenRUP.step64308 (p 1975) (p 2027) (p 2707) (p 2842) (p 3434) (p 3585) (p 4107) (h 2135) (derived40810 p h) (derived40885 p h) (h 39717)

theorem derived64309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3692) ∨ (¬ p 4902) ∨ (¬ p 5190) :=
  ElevenRUP.step64309 (p 2027) (p 2299) (p 2470) (p 2528) (p 3549) (p 3591) (p 3692) (p 4902) (p 5190) (derived40810 p h) (h 39718)

theorem derived64310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (¬ p 3097) ∨ (¬ p 3662) :=
  ElevenRUP.step64310 (p 1990) (p 2027) (p 2295) (p 2388) (p 2641) (p 3097) (p 3662) (h 2150) (derived40810 p h) (derived40873 p h) (h 39719)

theorem derived64316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3054) ∨ (¬ p 3422) ∨ (¬ p 4244) ∨ (¬ p 4717) :=
  ElevenRUP.step64316 (p 2027) (p 2427) (p 3054) (p 3422) (p 4244) (p 4717) (derived40810 p h) (h 39726)

theorem derived64317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 4777) ∨ (¬ p 5190) :=
  ElevenRUP.step64317 (p 1982) (p 2027) (p 2352) (p 2363) (p 2573) (p 2633) (p 2737) (p 3365) (p 3553) (p 3588) (p 3873) (p 4777) (p 5190) (h 2142) (derived40810 p h) (derived40879 p h) (h 39727)

theorem derived64319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2996) ∨ (¬ p 3641) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step64319 (p 2027) (p 2247) (p 2528) (p 2598) (p 2996) (p 3641) (p 3947) (p 4669) (p 4733) (derived40810 p h) (h 39729)

theorem derived64320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 2598) ∨ (¬ p 3172) ∨ (¬ p 3422) ∨ (¬ p 4118) ∨ (¬ p 4133) ∨ (¬ p 4733) :=
  ElevenRUP.step64320 (p 2027) (p 2245) (p 2352) (p 2459) (p 2598) (p 3172) (p 3422) (p 4118) (p 4133) (p 4733) (derived40810 p h) (h 39730)

theorem derived64323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 4906) :=
  ElevenRUP.step64323 (p 1990) (p 2388) (p 2860) (p 4906) (h 2150) (derived40873 p h) (h 39733)

theorem derived64324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 3590) ∨ (¬ p 4379) ∨ (¬ p 4444) ∨ (¬ p 5346) :=
  ElevenRUP.step64324 (p 1976) (p 2027) (p 2493) (p 2737) (p 2842) (p 3365) (p 3461) (p 3564) (p 3590) (p 4379) (p 4444) (p 5346) (h 2136) (derived40810 p h) (derived40885 p h) (h 39734)

theorem derived64326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 4421) ∨ (¬ p 4976) ∨ (¬ p 5454) :=
  ElevenRUP.step64326 (p 2027) (p 3670) (p 4137) (p 4191) (p 4421) (p 4976) (p 5454) (derived40810 p h) (h 39736)

theorem derived64328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 4111) :=
  ElevenRUP.step64328 (p 2007) (p 2027) (p 2534) (p 2545) (p 3189) (p 3256) (p 4111) (h 2167) (derived40810 p h) (derived40876 p h) (h 39738)

theorem derived64329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3105) ∨ (¬ p 3745) ∨ (¬ p 3822) ∨ (¬ p 4193) ∨ (¬ p 5046) :=
  ElevenRUP.step64329 (p 2027) (p 2295) (p 3105) (p 3745) (p 3822) (p 4193) (p 5046) (derived40810 p h) (h 39739)

theorem derived64332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2383) ∨ (¬ p 2779) ∨ (¬ p 2829) ∨ (¬ p 3585) :=
  ElevenRUP.step64332 (p 1982) (p 2027) (p 2363) (p 2383) (p 2779) (p 2829) (p 2842) (p 3585) (h 2142) (derived40810 p h) (derived40885 p h) (h 39742)

theorem derived64334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2996) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3947) ∨ (¬ p 4444) ∨ (¬ p 4669) ∨ (¬ p 5190) :=
  ElevenRUP.step64334 (p 2027) (p 2247) (p 2996) (p 3276) (p 3355) (p 3947) (p 4444) (p 4669) (p 5190) (derived40810 p h) (h 39744)

theorem derived64337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2528) ∨ (¬ p 3362) ∨ (¬ p 3641) ∨ (¬ p 3684) :=
  ElevenRUP.step64337 (p 1982) (p 2027) (p 2230) (p 2528) (p 2611) (p 3362) (p 3641) (p 3684) (h 2142) (derived40810 p h) (derived40877 p h) (h 39747)

theorem derived64338 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2220) ∨ (¬ p 2363) ∨ (¬ p 3646) ∨ (¬ p 4441) :=
  ElevenRUP.step64338 (p 1982) (p 2027) (p 2192) (p 2220) (p 2363) (p 2873) (p 3646) (p 4441) (h 2142) (derived40810 p h) (derived40886 p h) (h 39748)

theorem derived64339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 4157) :=
  ElevenRUP.step64339 (p 1982) (p 2027) (p 2233) (p 2363) (p 2573) (p 3584) (p 3641) (p 4157) (h 2142) (derived40810 p h) (derived40868 p h) (h 39749)

theorem derived64341 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4733) ∨ (¬ p 4902) :=
  ElevenRUP.step64341 (p 2027) (p 2459) (p 2696) (p 3136) (p 3156) (p 3860) (p 4261) (p 4733) (p 4902) (derived40810 p h) (h 39751)

theorem derived64342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 3590) ∨ (¬ p 3905) ∨ (¬ p 4749) :=
  ElevenRUP.step64342 (p 2027) (p 2696) (p 2922) (p 3540) (p 3590) (p 3905) (p 4749) (derived40810 p h) (h 39752)

theorem derived64343 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3641) ∨ (¬ p 3817) ∨ (¬ p 4149) ∨ (¬ p 4366) ∨ (¬ p 4381) ∨ (¬ p 4733) ∨ (¬ p 5119) :=
  ElevenRUP.step64343 (p 2027) (p 2598) (p 3641) (p 3817) (p 4149) (p 4366) (p 4381) (p 4733) (p 5119) (derived40810 p h) (h 39753)

theorem derived64351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3483) ∨ (¬ p 3588) ∨ (¬ p 4471) ∨ (¬ p 4624) :=
  ElevenRUP.step64351 (p 2027) (p 2829) (p 3483) (p 3588) (p 4471) (p 4624) (derived40810 p h) (h 39761)

theorem derived64353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2528) ∨ (¬ p 3266) ∨ (¬ p 3688) ∨ (¬ p 3954) ∨ (¬ p 4329) ∨ (¬ p 4383) ∨ (¬ p 5207) ∨ (¬ p 5254) :=
  ElevenRUP.step64353 (p 2027) (p 2341) (p 2528) (p 3266) (p 3688) (p 3954) (p 4329) (p 4383) (p 5207) (p 5254) (derived40810 p h) (h 39763)

theorem derived64356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3319) ∨ (p 3366) ∨ (¬ p 3461) ∨ (¬ p 3585) ∨ (¬ p 3918) ∨ (¬ p 4444) ∨ (¬ p 4697) ∨ (¬ p 4842) ∨ (¬ p 5160) :=
  ElevenRUP.step64356 (p 2027) (p 2696) (p 3319) (p 3366) (p 3461) (p 3585) (p 3918) (p 4444) (p 4697) (p 4842) (p 5160) (derived40810 p h) (h 39767)

theorem derived64358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 2881) ∨ (¬ p 3201) ∨ (¬ p 3874) ∨ (¬ p 3960) ∨ (¬ p 4277) :=
  ElevenRUP.step64358 (p 2027) (p 2481) (p 2881) (p 3201) (p 3874) (p 3960) (p 4277) (derived40810 p h) (h 39769)

theorem derived64359 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2417) ∨ (¬ p 2696) ∨ (¬ p 2780) ∨ (¬ p 3644) ∨ (¬ p 3759) ∨ (¬ p 3917) ∨ (¬ p 4625) ∨ (¬ p 4749) ∨ (¬ p 5201) :=
  ElevenRUP.step64359 (p 2027) (p 2341) (p 2417) (p 2696) (p 2780) (p 3644) (p 3759) (p 3917) (p 4625) (p 4749) (p 5201) (derived40810 p h) (h 39770)

theorem derived64364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 3371) ∨ (¬ p 3585) ∨ (¬ p 3758) ∨ (¬ p 4392) ∨ (¬ p 4749) :=
  ElevenRUP.step64364 (p 2027) (p 2192) (p 3371) (p 3585) (p 3758) (p 4392) (p 4749) (derived40810 p h) (h 39776)

theorem derived64371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2440) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3695) :=
  ElevenRUP.step64371 (p 1994) (p 2027) (p 2114) (p 2132) (p 2440) (p 2737) (p 3365) (p 3695) (h 2154) (derived40810 p h) (derived40864 p h) (h 39784)

theorem derived64373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2341) ∨ (¬ p 2459) ∨ (¬ p 2509) ∨ (¬ p 2952) ∨ (¬ p 3027) ∨ (¬ p 4066) ∨ (p 4202) ∨ (¬ p 4282) ∨ (¬ p 4286) ∨ (¬ p 5118) :=
  ElevenRUP.step64373 (p 2027) (p 2249) (p 2341) (p 2459) (p 2509) (p 2952) (p 3027) (p 4066) (p 4202) (p 4282) (p 4286) (p 5118) (derived40810 p h) (h 39786)

theorem derived64375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3005) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4550) ∨ (¬ p 4733) :=
  ElevenRUP.step64375 (p 2027) (p 2331) (p 3005) (p 3486) (p 3555) (p 3570) (p 4117) (p 4195) (p 4550) (p 4733) (derived40810 p h) (h 39789)

theorem derived64376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2957) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3556) ∨ (¬ p 4315) ∨ (¬ p 4343) ∨ (¬ p 4790) ∨ (¬ p 4831) ∨ (¬ p 5660) :=
  ElevenRUP.step64376 (p 2027) (p 2651) (p 2957) (p 3276) (p 3333) (p 3556) (p 4315) (p 4343) (p 4790) (p 4831) (p 5660) (derived40810 p h) (h 39790)

theorem derived64379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3553) ∨ (¬ p 4348) ∨ (¬ p 4590) ∨ (¬ p 4854) :=
  ElevenRUP.step64379 (p 2027) (p 2088) (p 3553) (p 4348) (p 4590) (p 4854) (derived40810 p h) (h 39794)

theorem derived64380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 3821) ∨ (¬ p 4381) :=
  ElevenRUP.step64380 (p 1975) (p 2027) (p 2299) (p 2341) (p 2764) (p 3821) (p 4381) (h 2135) (derived40810 p h) (derived40882 p h) (h 39795)

theorem derived64381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2717) ∨ (¬ p 2744) ∨ (¬ p 3016) ∨ (¬ p 3366) ∨ (¬ p 3551) ∨ (¬ p 3564) ∨ (¬ p 3820) ∨ (¬ p 4324) ∨ (¬ p 4621) :=
  ElevenRUP.step64381 (p 2027) (p 2246) (p 2651) (p 2717) (p 2744) (p 3016) (p 3366) (p 3551) (p 3564) (p 3820) (p 4324) (p 4621) (derived40810 p h) (h 39796)

theorem derived64382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4191) :=
  ElevenRUP.step64382 (p 1999) (p 2027) (p 2247) (p 2688) (p 3707) (p 3830) (p 4191) (h 2159) (derived40810 p h) (derived40880 p h) (h 39797)

theorem derived64385 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2553) ∨ (¬ p 3830) ∨ (¬ p 4137) ∨ (¬ p 5152) :=
  ElevenRUP.step64385 (p 1975) (p 2027) (p 2247) (p 2553) (p 2688) (p 3830) (p 4137) (p 5152) (h 2135) (derived40810 p h) (derived40880 p h) (h 39800)

theorem derived64386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3343) ∨ (¬ p 3461) ∨ (¬ p 3574) ∨ (¬ p 4331) :=
  ElevenRUP.step64386 (p 1988) (p 2027) (p 2233) (p 2573) (p 3343) (p 3461) (p 3574) (p 4331) (h 2148) (derived40810 p h) (derived40868 p h) (h 39801)

theorem derived64387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2608) ∨ (¬ p 3115) ∨ (¬ p 3370) ∨ (¬ p 3860) ∨ (¬ p 3952) ∨ (¬ p 4261) ∨ (¬ p 4377) ∨ (¬ p 4450) :=
  ElevenRUP.step64387 (p 2027) (p 2156) (p 2608) (p 3115) (p 3370) (p 3860) (p 3952) (p 4261) (p 4377) (p 4450) (derived40810 p h) (h 39803)

theorem derived64389 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3486) ∨ (¬ p 3659) ∨ (¬ p 3696) ∨ (¬ p 4403) ∨ (¬ p 4895) :=
  ElevenRUP.step64389 (p 2027) (p 2166) (p 3486) (p 3659) (p 3696) (p 4403) (p 4895) (derived40810 p h) (h 39805)

theorem derived64391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2247) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4181) ∨ (¬ p 4348) ∨ (¬ p 5122) :=
  ElevenRUP.step64391 (p 2027) (p 2136) (p 2247) (p 2744) (p 3366) (p 3449) (p 3556) (p 3570) (p 4181) (p 4348) (p 5122) (derived40810 p h) (h 39807)

theorem derived64393 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4425) :=
  ElevenRUP.step64393 (p 2012) (p 2027) (p 2247) (p 2688) (p 3707) (p 3830) (p 4425) (h 2172) (derived40810 p h) (derived40880 p h) (h 39811)

theorem derived64397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 4385) :=
  ElevenRUP.step64397 (p 1975) (p 2027) (p 2299) (p 2870) (p 2881) (p 3043) (p 4385) (h 2135) (derived40810 p h) (derived40893 p h) (h 39815)

theorem derived64399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2608) ∨ (¬ p 2651) ∨ (¬ p 2744) ∨ (¬ p 3016) ∨ (¬ p 3542) ∨ (¬ p 3564) ∨ (¬ p 3860) ∨ (¬ p 4330) ∨ (¬ p 4348) :=
  ElevenRUP.step64399 (p 2027) (p 2246) (p 2608) (p 2651) (p 2744) (p 3016) (p 3542) (p 3564) (p 3860) (p 4330) (p 4348) (derived40810 p h) (h 39819)

theorem derived64401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2299) ∨ (¬ p 2963) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 3549) ∨ (¬ p 3692) ∨ (¬ p 3922) ∨ (¬ p 4902) :=
  ElevenRUP.step64401 (p 2027) (p 2249) (p 2299) (p 2963) (p 3189) (p 3256) (p 3549) (p 3692) (p 3922) (p 4902) (derived40810 p h) (h 39821)

theorem derived64405 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 2247) ∨ (¬ p 2860) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 4133) ∨ (¬ p 4733) :=
  ElevenRUP.step64405 (p 2027) (p 2132) (p 2187) (p 2247) (p 2860) (p 2996) (p 3553) (p 4133) (p 4733) (derived40810 p h) (h 39825)

theorem derived64413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2573) ∨ (¬ p 3343) ∨ (¬ p 3574) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4332) ∨ (¬ p 4419) :=
  ElevenRUP.step64413 (p 2027) (p 2138) (p 2573) (p 3343) (p 3574) (p 3692) (p 3694) (p 4332) (p 4419) (derived40810 p h) (h 39833)

theorem derived64414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3097) :=
  ElevenRUP.step64414 (p 1990) (p 2027) (p 2553) (p 2573) (p 2656) (p 2688) (p 2727) (p 3097) (h 2150) (derived40810 p h) (derived40880 p h) (h 39834)

theorem derived64416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4237) ∨ (¬ p 4906) :=
  ElevenRUP.step64416 (p 2027) (p 3256) (p 3692) (p 3694) (p 4237) (p 4906) (derived40810 p h) (h 39838)

theorem derived64419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 3323) ∨ (¬ p 3425) ∨ (¬ p 3548) ∨ (¬ p 3576) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4734) :=
  ElevenRUP.step64419 (p 2027) (p 2331) (p 2737) (p 2811) (p 3323) (p 3425) (p 3548) (p 3576) (p 4330) (p 4348) (p 4734) (derived40810 p h) (h 39841)

theorem derived64421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3346) ∨ (¬ p 3363) ∨ (¬ p 3641) ∨ (¬ p 4440) ∨ (¬ p 4596) :=
  ElevenRUP.step64421 (p 2027) (p 2363) (p 3346) (p 3363) (p 3641) (p 4440) (p 4596) (derived40810 p h) (h 39843)

theorem derived64425 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2396) ∨ (¬ p 3201) ∨ (¬ p 3362) ∨ (¬ p 3591) ∨ (¬ p 3684) ∨ (¬ p 3817) ∨ (¬ p 4105) ∨ (¬ p 4276) ∨ (¬ p 4733) :=
  ElevenRUP.step64425 (p 2027) (p 2230) (p 2396) (p 3201) (p 3362) (p 3591) (p 3684) (p 3817) (p 4105) (p 4276) (p 4733) (derived40810 p h) (h 39847)

theorem derived64426 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2563) ∨ (¬ p 2598) ∨ (¬ p 2641) ∨ (¬ p 2850) ∨ (¬ p 2963) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 4733) :=
  ElevenRUP.step64426 (p 1990) (p 2027) (p 2245) (p 2563) (p 2598) (p 2633) (p 2641) (p 2850) (p 2963) (p 2996) (p 3553) (p 4733) (h 2150) (derived40810 p h) (derived40879 p h) (h 39849)

theorem derived64429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 3688) ∨ (¬ p 3954) ∨ (¬ p 4132) ∨ (¬ p 4329) ∨ (¬ p 5207) ∨ (¬ p 5254) :=
  ElevenRUP.step64429 (p 2027) (p 2341) (p 3146) (p 3266) (p 3688) (p 3954) (p 4132) (p 4329) (p 5207) (p 5254) (derived40810 p h) (h 39854)

theorem derived64430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2246) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2396) ∨ (¬ p 2619) ∨ (¬ p 2744) ∨ (¬ p 3366) ∨ (¬ p 3951) ∨ (¬ p 4120) ∨ (¬ p 4385) :=
  ElevenRUP.step64430 (p 2027) (p 2136) (p 2246) (p 2295) (p 2331) (p 2396) (p 2619) (p 2744) (p 3366) (p 3951) (p 4120) (p 4385) (derived40810 p h) (h 39855)

theorem derived64431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2748) ∨ (¬ p 2819) ∨ (¬ p 2829) ∨ (¬ p 3359) ∨ (¬ p 3365) ∨ (¬ p 4111) ∨ (¬ p 4697) ∨ (¬ p 4734) :=
  ElevenRUP.step64431 (p 2027) (p 2363) (p 2748) (p 2819) (p 2829) (p 3359) (p 3365) (p 4111) (p 4697) (p 4734) (derived40810 p h) (h 39856)

theorem derived64432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2406) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 4109) ∨ (¬ p 4116) :=
  ElevenRUP.step64432 (p 1988) (p 2027) (p 2220) (p 2406) (p 2545) (p 3146) (p 3266) (p 4109) (p 4116) (h 2148) (derived40810 p h) (derived40876 p h) (h 39857)

theorem derived64438 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 4078) ∨ (¬ p 4340) ∨ (¬ p 4871) :=
  ElevenRUP.step64438 (p 2027) (p 2363) (p 3063) (p 4078) (p 4340) (p 4871) (derived40810 p h) (h 39863)

theorem derived64439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2248) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4324) ∨ (¬ p 4666) :=
  ElevenRUP.step64439 (p 2027) (p 2177) (p 2248) (p 2295) (p 2331) (p 3588) (p 3954) (p 4324) (p 4666) (derived40810 p h) (h 39865)

theorem derived64442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2881) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4324) ∨ (¬ p 4666) :=
  ElevenRUP.step64442 (p 2027) (p 2248) (p 2881) (p 2901) (p 2946) (p 3588) (p 3954) (p 4324) (p 4666) (derived40810 p h) (h 39868)

theorem derived64444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3309) ∨ (¬ p 4026) ∨ (¬ p 4191) :=
  ElevenRUP.step64444 (p 1990) (p 2027) (p 2764) (p 3097) (p 3309) (p 4026) (p 4191) (h 2150) (derived40810 p h) (derived40882 p h) (h 39871)

theorem derived64448 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3238) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3570) ∨ (¬ p 3740) :=
  ElevenRUP.step64448 (p 1985) (p 2027) (p 2202) (p 2264) (p 3238) (p 3389) (p 3519) (p 3570) (p 3740) (h 2145) (derived40810 p h) (derived40867 p h) (h 39878)

theorem derived64449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2249) ∨ (¬ p 2363) ∨ (¬ p 2383) ∨ (¬ p 2641) ∨ (¬ p 2952) ∨ (¬ p 3567) ∨ (¬ p 4282) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step64449 (p 2027) (p 2191) (p 2249) (p 2363) (p 2383) (p 2641) (p 2952) (p 3567) (p 4282) (p 5118) (p 5568) (derived40810 p h) (h 39879)

theorem derived64451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2972) ∨ (¬ p 3948) ∨ (¬ p 4715) ∨ (¬ p 4948) :=
  ElevenRUP.step64451 (p 2027) (p 2499) (p 2972) (p 3948) (p 4715) (p 4948) (derived40810 p h) (h 39881)

theorem derived64460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 3452) ∨ (¬ p 3755) ∨ (¬ p 4195) ∨ (¬ p 5109) :=
  ElevenRUP.step64460 (p 2027) (p 2248) (p 2331) (p 2509) (p 2534) (p 3452) (p 3755) (p 4195) (p 5109) (derived40810 p h) (h 39896)

theorem derived64461 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3570) ∨ (¬ p 3699) ∨ (¬ p 4315) :=
  ElevenRUP.step64461 (p 1987) (p 2027) (p 2633) (p 2992) (p 2996) (p 3570) (p 3699) (p 4315) (h 2147) (derived40810 p h) (derived40879 p h) (h 39897)

theorem derived64462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3516) ∨ (¬ p 4066) ∨ (¬ p 4111) ∨ (¬ p 4278) :=
  ElevenRUP.step64462 (p 2010) (p 2027) (p 2545) (p 3027) (p 3516) (p 4066) (p 4111) (p 4278) (h 2170) (derived40810 p h) (derived40876 p h) (h 39898)

theorem derived64466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2299) ∨ (¬ p 2774) ∨ (¬ p 3365) ∨ (¬ p 4156) ∨ (¬ p 4328) :=
  ElevenRUP.step64466 (p 1975) (p 2027) (p 2264) (p 2299) (p 2622) (p 2774) (p 3365) (p 4156) (p 4328) (h 2135) (derived40810 p h) (derived40878 p h) (h 39904)

theorem derived64470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 3954) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step64470 (p 2027) (p 2252) (p 2750) (p 2963) (p 3324) (p 3707) (p 3830) (p 3954) (p 5123) (p 5580) (derived40810 p h) (h 39910)

theorem derived64472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3324) :=
  ElevenRUP.step64472 (p 1975) (p 2027) (p 2295) (p 2699) (p 3063) (p 3093) (p 3324) (h 2135) (derived40810 p h) (derived40881 p h) (h 39912)

theorem derived64474 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3426) ∨ (¬ p 3434) ∨ (¬ p 3947) ∨ (¬ p 4386) ∨ (¬ p 4428) ∨ (¬ p 4509) :=
  ElevenRUP.step64474 (p 2027) (p 3156) (p 3426) (p 3434) (p 3947) (p 4386) (p 4428) (p 4509) (derived40810 p h) (h 39914)

theorem derived64475 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (p 2750) :=
  ElevenRUP.step64475 (p 1984) (p 2114) (p 2247) (p 2750) (h 2144) (derived40864 p h) (h 39915)

theorem derived64476 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2440) ∨ (¬ p 2476) ∨ (¬ p 3692) ∨ (¬ p 3693) :=
  ElevenRUP.step64476 (p 1994) (p 2027) (p 2230) (p 2440) (p 2476) (p 2766) (p 3692) (p 3693) (h 2154) (derived40810 p h) (derived40884 p h) (h 39916)

theorem derived64477 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3096) ∨ (¬ p 3156) ∨ (¬ p 3920) ∨ (¬ p 3947) ∨ (¬ p 4386) ∨ (¬ p 4509) :=
  ElevenRUP.step64477 (p 2027) (p 2417) (p 3096) (p 3156) (p 3920) (p 3947) (p 4386) (p 4509) (derived40810 p h) (h 39917)

theorem derived64478 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 4598) ∨ (¬ p 4687) :=
  ElevenRUP.step64478 (p 2027) (p 2499) (p 3449) (p 3452) (p 4598) (p 4687) (derived40810 p h) (h 39918)

theorem derived64480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3222) ∨ (¬ p 3346) ∨ (¬ p 3590) ∨ (¬ p 3684) ∨ (¬ p 4610) :=
  ElevenRUP.step64480 (p 2027) (p 2470) (p 3222) (p 3346) (p 3590) (p 3684) (p 4610) (derived40810 p h) (h 39920)

theorem derived64482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3821) ∨ (¬ p 4533) ∨ (¬ p 4984) :=
  ElevenRUP.step64482 (p 2027) (p 2427) (p 3246) (p 3821) (p 4533) (p 4984) (derived40810 p h) (h 39922)

theorem derived64487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2641) ∨ (¬ p 2657) ∨ (¬ p 3487) ∨ (¬ p 3506) ∨ (¬ p 4191) ∨ (¬ p 4330) ∨ (¬ p 4421) :=
  ElevenRUP.step64487 (p 2027) (p 2249) (p 2509) (p 2534) (p 2641) (p 2657) (p 3487) (p 3506) (p 4191) (p 4330) (p 4421) (derived40810 p h) (h 39927)

theorem derived64488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2509) ∨ (¬ p 2641) ∨ (¬ p 2657) ∨ (¬ p 3323) ∨ (¬ p 3461) ∨ (¬ p 3487) ∨ (¬ p 4286) ∨ (¬ p 5123) :=
  ElevenRUP.step64488 (p 2027) (p 2249) (p 2509) (p 2641) (p 2657) (p 3323) (p 3461) (p 3487) (p 4286) (p 5123) (derived40810 p h) (h 39928)

theorem derived64490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2417) ∨ (¬ p 2881) ∨ (¬ p 3690) ∨ (¬ p 4712) :=
  ElevenRUP.step64490 (p 2027) (p 2299) (p 2417) (p 2881) (p 3690) (p 4712) (derived40810 p h) (h 39930)

theorem derived64491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2245) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2870) ∨ (¬ p 2996) ∨ (¬ p 3758) ∨ (¬ p 4362) ∨ (¬ p 4521) :=
  ElevenRUP.step64491 (p 2027) (p 2156) (p 2245) (p 2657) (p 2727) (p 2870) (p 2996) (p 3758) (p 4362) (p 4521) (derived40810 p h) (h 39931)

theorem derived64492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2995) ∨ (¬ p 3821) ∨ (¬ p 4244) ∨ (¬ p 4283) ∨ (¬ p 4906) :=
  ElevenRUP.step64492 (p 2027) (p 2449) (p 2995) (p 3821) (p 4244) (p 4283) (p 4906) (derived40810 p h) (h 39932)

theorem derived64494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2241) ∨ (¬ p 2396) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4641) :=
  ElevenRUP.step64494 (p 2027) (p 2122) (p 2241) (p 2396) (p 2750) (p 2753) (p 2774) (p 3193) (p 3452) (p 4641) (derived40810 p h) (h 39937)

theorem derived64498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 4129) ∨ (¬ p 4136) ∨ (¬ p 4423) ∨ (¬ p 4882) :=
  ElevenRUP.step64498 (p 2027) (p 2427) (p 4129) (p 4136) (p 4423) (p 4882) (derived40810 p h) (h 39941)

theorem derived64501 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 3222) ∨ (¬ p 3917) ∨ (¬ p 4331) ∨ (¬ p 5222) :=
  ElevenRUP.step64501 (p 2027) (p 2499) (p 3222) (p 3917) (p 4331) (p 5222) (derived40810 p h) (h 39944)

theorem derived64503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2668) ∨ (¬ p 2779) ∨ (¬ p 2829) ∨ (¬ p 3568) :=
  ElevenRUP.step64503 (p 1981) (p 2027) (p 2114) (p 2307) (p 2668) (p 2779) (p 2829) (p 3568) (h 2141) (derived40810 p h) (derived40864 p h) (h 39946)

theorem derived64504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2668) ∨ (¬ p 2737) ∨ (¬ p 2779) ∨ (¬ p 3568) ∨ (¬ p 4426) :=
  ElevenRUP.step64504 (p 1981) (p 2027) (p 2114) (p 2307) (p 2668) (p 2737) (p 2779) (p 3568) (p 4426) (h 2141) (derived40810 p h) (derived40864 p h) (h 39947)

theorem derived64506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 2839) ∨ (¬ p 3688) ∨ (¬ p 4428) ∨ (¬ p 4509) :=
  ElevenRUP.step64506 (p 2027) (p 2619) (p 2839) (p 3688) (p 4428) (p 4509) (derived40810 p h) (h 39949)

theorem derived64511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3359) ∨ (¬ p 4129) ∨ (¬ p 4425) ∨ (¬ p 4826) :=
  ElevenRUP.step64511 (p 2027) (p 2132) (p 2252) (p 2657) (p 2750) (p 2753) (p 2870) (p 3359) (p 4129) (p 4425) (p 4826) (derived40810 p h) (h 39955)

theorem derived64512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2741) ∨ (¬ p 3359) ∨ (¬ p 3399) ∨ (¬ p 3555) ∨ (¬ p 4075) ∨ (¬ p 4377) ∨ (¬ p 4425) ∨ (¬ p 4826) :=
  ElevenRUP.step64512 (p 2027) (p 2252) (p 2657) (p 2741) (p 3359) (p 3399) (p 3555) (p 4075) (p 4377) (p 4425) (p 4826) (derived40810 p h) (h 39956)

theorem derived64513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4256) :=
  ElevenRUP.step64513 (p 2027) (p 2132) (p 2252) (p 2534) (p 2657) (p 2750) (p 2753) (p 2870) (p 3246) (p 3950) (p 4256) (derived40810 p h) (h 39957)

theorem derived64514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2241) ∨ (¬ p 2534) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 4370) :=
  ElevenRUP.step64514 (p 2027) (p 2132) (p 2241) (p 2534) (p 2750) (p 2753) (p 2870) (p 3246) (p 3860) (p 3950) (p 4370) (derived40810 p h) (h 39958)

theorem derived64515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2476) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3083) ∨ (¬ p 3246) ∨ (¬ p 3359) ∨ (¬ p 3950) ∨ (¬ p 4440) :=
  ElevenRUP.step64515 (p 2027) (p 2132) (p 2252) (p 2476) (p 2655) (p 2750) (p 2753) (p 2870) (p 3083) (p 3246) (p 3359) (p 3950) (p 4440) (derived40810 p h) (h 39959)

theorem derived64517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 3414) ∨ (¬ p 3461) ∨ (¬ p 3553) ∨ (¬ p 4789) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64517 (p 2027) (p 2156) (p 3125) (p 3366) (p 3370) (p 3371) (p 3414) (p 3461) (p 3553) (p 4789) (p 5123) (p 5558) (derived40810 p h) (h 39961)

theorem derived64518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 3083) ∨ (¬ p 3212) ∨ (¬ p 3359) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 3680) ∨ (¬ p 4191) ∨ (¬ p 4729) ∨ (¬ p 5325) :=
  ElevenRUP.step64518 (p 2027) (p 2476) (p 3083) (p 3212) (p 3359) (p 3366) (p 3370) (p 3371) (p 3680) (p 4191) (p 4729) (p 5325) (derived40810 p h) (h 39962)

theorem derived64521 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2252) ∨ (¬ p 2396) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3950) ∨ (¬ p 4256) :=
  ElevenRUP.step64521 (p 2027) (p 2122) (p 2252) (p 2396) (p 2534) (p 2657) (p 2750) (p 2753) (p 2774) (p 3950) (p 4256) (derived40810 p h) (h 39965)

theorem derived64522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 2476) ∨ (¬ p 2774) ∨ (¬ p 3083) ∨ (¬ p 3359) ∨ (¬ p 4641) ∨ (¬ p 4729) :=
  ElevenRUP.step64522 (p 2027) (p 2122) (p 2396) (p 2476) (p 2774) (p 3083) (p 3359) (p 4641) (p 4729) (derived40810 p h) (h 39966)

theorem derived64525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2307) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2962) ∨ (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 4236) ∨ (¬ p 4256) ∨ (¬ p 4330) :=
  ElevenRUP.step64525 (p 2027) (p 2139) (p 2307) (p 2534) (p 2657) (p 2962) (p 3097) (p 3125) (p 4236) (p 4256) (p 4330) (derived40810 p h) (h 39969)

theorem derived64528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4129) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step64528 (p 2027) (p 2132) (p 2252) (p 2750) (p 2753) (p 2870) (p 3172) (p 4118) (p 4129) (p 4444) (p 4826) (derived40810 p h) (h 39972)

theorem derived64533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 3125) ∨ (p 3366) ∨ (¬ p 3414) ∨ (¬ p 3461) ∨ (¬ p 3553) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64533 (p 2027) (p 2144) (p 2156) (p 2252) (p 2750) (p 3125) (p 3366) (p 3414) (p 3461) (p 3553) (p 5123) (p 5558) (derived40810 p h) (h 39977)

theorem derived64534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2437) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 3212) ∨ (¬ p 3359) ∨ (p 3366) ∨ (¬ p 3540) ∨ (¬ p 3680) ∨ (¬ p 4191) ∨ (¬ p 5325) :=
  ElevenRUP.step64534 (p 2027) (p 2144) (p 2252) (p 2437) (p 2655) (p 2750) (p 3212) (p 3359) (p 3366) (p 3540) (p 3680) (p 4191) (p 5325) (derived40810 p h) (h 39978)

theorem derived64538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2220) ∨ (¬ p 2252) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3016) ∨ (¬ p 3146) ∨ (¬ p 4256) ∨ (¬ p 4348) ∨ (¬ p 4438) :=
  ElevenRUP.step64538 (p 2027) (p 2144) (p 2220) (p 2252) (p 2579) (p 2655) (p 2750) (p 2753) (p 3016) (p 3146) (p 4256) (p 4348) (p 4438) (derived40810 p h) (h 39983)

theorem derived64540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2499) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 3016) ∨ (¬ p 3051) ∨ (¬ p 4244) ∨ (¬ p 4256) ∨ (¬ p 4434) ∨ (¬ p 5216) :=
  ElevenRUP.step64540 (p 2027) (p 2144) (p 2499) (p 2619) (p 2753) (p 3016) (p 3051) (p 4244) (p 4256) (p 4434) (p 5216) (derived40810 p h) (h 39985)

theorem derived64541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3574) ∨ (¬ p 4137) ∨ (¬ p 4191) :=
  ElevenRUP.step64541 (p 1991) (p 2027) (p 2657) (p 2764) (p 3574) (p 4137) (p 4191) (h 2151) (derived40810 p h) (derived40882 p h) (h 39986)

theorem derived64543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2474) ∨ (¬ p 2850) ∨ (¬ p 3363) ∨ (¬ p 4149) ∨ (¬ p 4608) ∨ (¬ p 5590) :=
  ElevenRUP.step64543 (p 2027) (p 2474) (p 2850) (p 3363) (p 4149) (p 4608) (p 5590) (derived40810 p h) (h 39988)

theorem derived64547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2963) ∨ (¬ p 3093) ∨ (¬ p 3922) ∨ (¬ p 3954) :=
  ElevenRUP.step64547 (p 2027) (p 2252) (p 2750) (p 2963) (p 3093) (p 3922) (p 3954) (derived40810 p h) (h 39992)

theorem derived64549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 3016) ∨ (¬ p 3246) ∨ (¬ p 3359) ∨ (¬ p 4022) ∨ (¬ p 4625) :=
  ElevenRUP.step64549 (p 2027) (p 2132) (p 2252) (p 2579) (p 2655) (p 2750) (p 2753) (p 2870) (p 3016) (p 3246) (p 3359) (p 4022) (p 4625) (derived40810 p h) (h 39994)

theorem derived64551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2311) ∨ (¬ p 2383) ∨ (¬ p 2427) ∨ (¬ p 3691) ∨ (¬ p 4193) ∨ (¬ p 4358) ∨ (¬ p 4882) :=
  ElevenRUP.step64551 (p 2027) (p 2311) (p 2383) (p 2427) (p 3691) (p 4193) (p 4358) (p 4882) (derived40810 p h) (h 39996)

theorem derived64552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 3051) ∨ (¬ p 3105) ∨ (¬ p 3324) ∨ (¬ p 4244) ∨ (¬ p 4347) ∨ (¬ p 4450) :=
  ElevenRUP.step64552 (p 2027) (p 2144) (p 2252) (p 2750) (p 2753) (p 2963) (p 3051) (p 3105) (p 3324) (p 4244) (p 4347) (p 4450) (derived40810 p h) (h 39997)

theorem derived64553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step64553 (p 2027) (p 2252) (p 2750) (p 2753) (p 2761) (p 2963) (p 3324) (p 3434) (p 3471) (p 5123) (p 5580) (derived40810 p h) (h 39998)

theorem derived64554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 3038) ∨ (¬ p 3292) ∨ (¬ p 3707) ∨ (¬ p 5284) ∨ (¬ p 5363) :=
  ElevenRUP.step64554 (p 2027) (p 2249) (p 3038) (p 3292) (p 3707) (p 5284) (p 5363) (derived40810 p h) (h 39999)

theorem derived64555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3016) ∨ (¬ p 3212) ∨ (¬ p 3359) ∨ (¬ p 3680) ∨ (¬ p 4381) ∨ (¬ p 4641) :=
  ElevenRUP.step64555 (p 2027) (p 2144) (p 2252) (p 2579) (p 2655) (p 2750) (p 2753) (p 3016) (p 3212) (p 3359) (p 3680) (p 4381) (p 4641) (derived40810 p h) (h 40000)

theorem derived64557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3574) ∨ (¬ p 3609) ∨ (¬ p 3956) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64557 (p 2027) (p 2098) (p 2252) (p 2657) (p 2750) (p 2753) (p 3574) (p 3609) (p 3956) (p 4348) (p 4503) (derived40810 p h) (h 40002)

theorem derived64558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2707) ∨ (¬ p 2750) ∨ (¬ p 2761) ∨ (¬ p 3434) ∨ (¬ p 3591) ∨ (¬ p 4435) ∨ (¬ p 5254) :=
  ElevenRUP.step64558 (p 2027) (p 2241) (p 2707) (p 2750) (p 2761) (p 3434) (p 3591) (p 4435) (p 5254) (derived40810 p h) (h 40003)

theorem derived64559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2619) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3051) ∨ (¬ p 3574) ∨ (¬ p 3956) ∨ (¬ p 4042) ∨ (¬ p 4244) ∨ (¬ p 4503) :=
  ElevenRUP.step64559 (p 2027) (p 2144) (p 2252) (p 2619) (p 2657) (p 2750) (p 2753) (p 3051) (p 3574) (p 3956) (p 4042) (p 4244) (p 4503) (derived40810 p h) (h 40004)

theorem derived64560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2146) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 4136) ∨ (¬ p 4324) :=
  ElevenRUP.step64560 (p 2027) (p 2146) (p 3051) (p 3246) (p 4136) (p 4324) (derived40810 p h) (h 40005)

theorem derived64561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2588) ∨ (¬ p 2963) ∨ (¬ p 3324) :=
  ElevenRUP.step64561 (p 1991) (p 2027) (p 2352) (p 2588) (p 2963) (p 2997) (p 3324) (h 2151) (derived40810 p h) (derived40890 p h) (h 40006)

theorem derived64562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 3599) ∨ (¬ p 3670) ∨ (¬ p 3950) ∨ (¬ p 4256) ∨ (¬ p 4381) :=
  ElevenRUP.step64562 (p 2027) (p 2252) (p 2534) (p 2657) (p 2750) (p 3599) (p 3670) (p 3950) (p 4256) (p 4381) (derived40810 p h) (h 40007)

theorem derived64563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2657) ∨ (¬ p 3212) ∨ (¬ p 3574) ∨ (¬ p 3680) ∨ (¬ p 4137) ∨ (¬ p 4789) ∨ (¬ p 5267) ∨ (¬ p 5387) :=
  ElevenRUP.step64563 (p 2027) (p 2144) (p 2657) (p 3212) (p 3574) (p 3680) (p 4137) (p 4789) (p 5267) (p 5387) (derived40810 p h) (h 40008)

theorem derived64564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2761) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3574) ∨ (¬ p 4236) ∨ (¬ p 4377) ∨ (¬ p 5254) ∨ (¬ p 5514) :=
  ElevenRUP.step64564 (p 2027) (p 2657) (p 2761) (p 3051) (p 3246) (p 3366) (p 3370) (p 3574) (p 4236) (p 4377) (p 5254) (p 5514) (derived40810 p h) (h 40011)

theorem derived64565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2797) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3370) ∨ (¬ p 3953) ∨ (¬ p 4228) ∨ (¬ p 4315) ∨ (¬ p 4377) ∨ (¬ p 4435) :=
  ElevenRUP.step64565 (p 1988) (p 2027) (p 2388) (p 2761) (p 2797) (p 3051) (p 3246) (p 3370) (p 3953) (p 4228) (p 4315) (p 4377) (p 4435) (h 2148) (derived40810 p h) (derived40873 p h) (h 40012)

theorem derived64566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3555) ∨ (¬ p 3571) ∨ (¬ p 3574) ∨ (¬ p 4137) ∨ (¬ p 4236) ∨ (¬ p 4377) ∨ (¬ p 4625) :=
  ElevenRUP.step64566 (p 2027) (p 2657) (p 3246) (p 3366) (p 3399) (p 3555) (p 3571) (p 3574) (p 4137) (p 4236) (p 4377) (p 4625) (derived40810 p h) (h 40013)

theorem derived64570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2761) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 3574) ∨ (¬ p 4789) ∨ (¬ p 5254) ∨ (¬ p 5514) :=
  ElevenRUP.step64570 (p 2027) (p 2657) (p 2761) (p 3434) (p 3471) (p 3574) (p 4789) (p 5254) (p 5514) (derived40810 p h) (h 40017)

theorem derived64571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2528) ∨ (¬ p 3083) ∨ (¬ p 3324) ∨ (¬ p 3365) ∨ (¬ p 4195) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64571 (p 1976) (p 2027) (p 2202) (p 2440) (p 2528) (p 3083) (p 3324) (p 3365) (p 4195) (p 4348) (p 4503) (h 2136) (derived40810 p h) (derived40867 p h) (h 40018)

theorem derived64572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2528) ∨ (¬ p 3324) ∨ (¬ p 3365) ∨ (¬ p 3641) ∨ (¬ p 4195) ∨ (¬ p 4343) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64572 (p 1976) (p 2027) (p 2202) (p 2440) (p 2528) (p 3324) (p 3365) (p 3641) (p 4195) (p 4343) (p 4348) (p 4503) (h 2136) (derived40810 p h) (derived40867 p h) (h 40019)

theorem derived64574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3073) ∨ (¬ p 3365) ∨ (¬ p 3449) ∨ (¬ p 4195) ∨ (¬ p 4445) ∨ (¬ p 4736) ∨ (¬ p 5254) ∨ (¬ p 5717) :=
  ElevenRUP.step64574 (p 2027) (p 2761) (p 3073) (p 3365) (p 3449) (p 4195) (p 4445) (p 4736) (p 5254) (p 5717) (derived40810 p h) (h 40021)

theorem derived64577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 4236) ∨ (¬ p 4340) ∨ (¬ p 4364) :=
  ElevenRUP.step64577 (p 1976) (p 2027) (p 2528) (p 2630) (p 2657) (p 3498) (p 4236) (p 4340) (p 4364) (h 2136) (derived40810 p h) (derived40899 p h) (h 40026)

theorem derived64582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2641) ∨ (¬ p 3567) ∨ (¬ p 3998) ∨ (¬ p 4114) ∨ (¬ p 5580) :=
  ElevenRUP.step64582 (p 1982) (p 2027) (p 2363) (p 2641) (p 2688) (p 3567) (p 3998) (p 4114) (p 5580) (h 2142) (derived40810 p h) (derived40880 p h) (h 40031)

theorem derived64584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3414) ∨ (¬ p 3422) ∨ (¬ p 3553) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4348) :=
  ElevenRUP.step64584 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 3414) (p 3422) (p 3553) (p 3564) (p 4330) (p 4348) (derived40810 p h) (h 40035)

theorem derived64585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3641) ∨ (¬ p 3876) ∨ (¬ p 3952) ∨ (¬ p 3989) ∨ (¬ p 4596) ∨ (¬ p 4789) :=
  ElevenRUP.step64585 (p 2027) (p 2952) (p 3362) (p 3389) (p 3641) (p 3876) (p 3952) (p 3989) (p 4596) (p 4789) (derived40810 p h) (h 40036)

theorem derived64586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) :=
  ElevenRUP.step64586 (p 1998) (p 2027) (p 2177) (p 2553) (p 2573) (p 2656) (p 2688) (p 2727) (h 2158) (derived40810 p h) (derived40880 p h) (h 40037)

theorem derived64589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2881) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 4559) :=
  ElevenRUP.step64589 (p 2027) (p 2249) (p 2553) (p 2573) (p 2656) (p 2727) (p 2881) (p 3414) (p 3553) (p 4559) (derived40810 p h) (h 40041)

theorem derived64592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 3005) ∨ (¬ p 3361) ∨ (¬ p 3573) ∨ (¬ p 4346) :=
  ElevenRUP.step64592 (p 1975) (p 2027) (p 2553) (p 2657) (p 2688) (p 2727) (p 3005) (p 3361) (p 3573) (p 4346) (h 2135) (derived40810 p h) (derived40880 p h) (h 40047)

theorem derived64593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 4111) :=
  ElevenRUP.step64593 (p 1982) (p 2027) (p 2363) (p 2545) (p 2641) (p 2668) (p 4111) (h 2142) (derived40810 p h) (derived40876 p h) (h 40048)

theorem derived64594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 3369) ∨ (¬ p 3371) ∨ (¬ p 4120) :=
  ElevenRUP.step64594 (p 2027) (p 2166) (p 2241) (p 2750) (p 3369) (p 3371) (p 4120) (derived40810 p h) (h 40049)

theorem derived64595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3343) ∨ (¬ p 3422) ∨ (¬ p 5160) :=
  ElevenRUP.step64595 (p 1975) (p 2027) (p 2545) (p 2553) (p 3343) (p 3422) (p 5160) (h 2135) (derived40810 p h) (derived40876 p h) (h 40050)

theorem derived64596 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 2751) ∨ (¬ p 2807) ∨ (¬ p 3572) :=
  ElevenRUP.step64596 (p 2027) (p 2657) (p 2727) (p 2751) (p 2807) (p 3572) (derived40810 p h) (h 40051)

theorem derived64597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2274) ∨ (¬ p 2563) ∨ (¬ p 2656) ∨ (¬ p 2727) :=
  ElevenRUP.step64597 (p 1975) (p 2027) (p 2230) (p 2274) (p 2563) (p 2656) (p 2688) (p 2727) (h 2135) (derived40810 p h) (derived40880 p h) (h 40052)

theorem derived64599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2751) ∨ (¬ p 3564) ∨ (¬ p 3692) ∨ (¬ p 4282) ∨ (¬ p 4315) ∨ (¬ p 4330) :=
  ElevenRUP.step64599 (p 2027) (p 2191) (p 2573) (p 2656) (p 2727) (p 2751) (p 3564) (p 3692) (p 4282) (p 4315) (p 4330) (derived40810 p h) (h 40054)

theorem derived64600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3555) ∨ (¬ p 3564) ∨ (¬ p 3692) ∨ (¬ p 4330) ∨ (¬ p 4733) :=
  ElevenRUP.step64600 (p 2027) (p 2191) (p 2598) (p 3422) (p 3555) (p 3564) (p 3692) (p 4330) (p 4733) (derived40810 p h) (h 40055)

theorem derived64601 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3497) ∨ (¬ p 4789) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64601 (p 2027) (p 2598) (p 2952) (p 3276) (p 3333) (p 3497) (p 4789) (p 5123) (p 5568) (derived40810 p h) (h 40056)

theorem derived64602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3461) ∨ (¬ p 3564) :=
  ElevenRUP.step64602 (p 1988) (p 2027) (p 2573) (p 2656) (p 2688) (p 2727) (p 3461) (p 3564) (h 2148) (derived40810 p h) (derived40880 p h) (h 40057)

theorem derived64603 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3568) ∨ (¬ p 4107) ∨ (¬ p 4322) ∨ (¬ p 4395) ∨ (¬ p 4789) :=
  ElevenRUP.step64603 (p 2027) (p 2963) (p 3276) (p 3355) (p 3362) (p 3568) (p 4107) (p 4322) (p 4395) (p 4789) (derived40810 p h) (h 40058)

theorem derived64604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3684) ∨ (¬ p 4332) ∨ (¬ p 4348) ∨ (¬ p 4789) :=
  ElevenRUP.step64604 (p 2027) (p 2230) (p 3333) (p 3362) (p 3414) (p 3553) (p 3684) (p 4332) (p 4348) (p 4789) (derived40810 p h) (h 40059)

theorem derived64605 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 2753) ∨ (¬ p 2963) ∨ (¬ p 2982) ∨ (¬ p 3324) ∨ (¬ p 3519) ∨ (¬ p 3680) ∨ (¬ p 4236) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step64605 (p 2027) (p 2230) (p 2753) (p 2963) (p 2982) (p 3324) (p 3519) (p 3680) (p 4236) (p 4376) (p 5123) (p 5580) (derived40810 p h) (h 40060)

theorem derived64607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2299) ∨ (¬ p 2563) ∨ (¬ p 2881) ∨ (¬ p 3365) ∨ (¬ p 3872) ∨ (¬ p 3877) ∨ (¬ p 4118) ∨ (¬ p 4419) :=
  ElevenRUP.step64607 (p 1975) (p 2027) (p 2230) (p 2299) (p 2563) (p 2766) (p 2881) (p 3365) (p 3872) (p 3877) (p 4118) (p 4419) (h 2135) (derived40810 p h) (derived40884 p h) (h 40062)

theorem derived64608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4330) :=
  ElevenRUP.step64608 (p 2027) (p 2241) (p 2598) (p 2750) (p 2753) (p 3422) (p 3564) (p 3860) (p 4261) (p 4330) (derived40810 p h) (h 40063)

theorem derived64610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2534) ∨ (¬ p 2553) ∨ (¬ p 3573) ∨ (¬ p 4170) ∨ (¬ p 4501) :=
  ElevenRUP.step64610 (p 2027) (p 2088) (p 2534) (p 2553) (p 3573) (p 4170) (p 4501) (derived40810 p h) (h 40065)

theorem derived64613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 4035) ∨ (¬ p 4075) ∨ (¬ p 4376) ∨ (¬ p 4826) ∨ (¬ p 5284) :=
  ElevenRUP.step64613 (p 2027) (p 3365) (p 3366) (p 3399) (p 3452) (p 4035) (p 4075) (p 4376) (p 4826) (p 5284) (derived40810 p h) (h 40068)

theorem derived64616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2957) ∨ (¬ p 3556) ∨ (¬ p 4111) ∨ (¬ p 4365) ∨ (¬ p 4704) :=
  ElevenRUP.step64616 (p 2027) (p 2891) (p 2957) (p 3556) (p 4111) (p 4365) (p 4704) (derived40810 p h) (h 40073)

theorem derived64618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 3414) ∨ (¬ p 3631) ∨ (¬ p 3947) ∨ (¬ p 4365) ∨ (¬ p 4431) :=
  ElevenRUP.step64618 (p 2027) (p 2249) (p 3414) (p 3631) (p 3947) (p 4365) (p 4431) (derived40810 p h) (h 40075)

theorem derived64619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2563) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3519) ∨ (¬ p 3659) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4376) :=
  ElevenRUP.step64619 (p 2027) (p 2230) (p 2563) (p 3125) (p 3366) (p 3425) (p 3519) (p 3659) (p 4330) (p 4348) (p 4376) (derived40810 p h) (h 40076)

theorem derived64621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2352) ∨ (¬ p 2588) ∨ (¬ p 3292) ∨ (¬ p 3366) ∨ (¬ p 3755) ∨ (¬ p 3877) ∨ (¬ p 4236) ∨ (¬ p 4774) ∨ (¬ p 4866) ∨ (¬ p 5016) :=
  ElevenRUP.step64621 (p 2027) (p 2307) (p 2352) (p 2588) (p 3292) (p 3366) (p 3755) (p 3877) (p 4236) (p 4774) (p 4866) (p 5016) (derived40810 p h) (h 40078)

theorem derived64623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2427) ∨ (¬ p 2590) ∨ (¬ p 2727) ∨ (¬ p 3019) ∨ (¬ p 3567) ∨ (¬ p 3956) :=
  ElevenRUP.step64623 (p 1985) (p 2027) (p 2383) (p 2427) (p 2590) (p 2688) (p 2727) (p 3019) (p 3567) (p 3956) (h 2145) (derived40810 p h) (derived40880 p h) (h 40080)

theorem derived64624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3256) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4041) ∨ (¬ p 4340) ∨ (¬ p 4376) :=
  ElevenRUP.step64624 (p 2027) (p 2104) (p 2230) (p 2427) (p 2881) (p 3256) (p 3366) (p 3519) (p 4041) (p 4340) (p 4376) (derived40810 p h) (h 40081)

theorem derived64625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2797) ∨ (¬ p 2881) ∨ (¬ p 2963) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3877) ∨ (¬ p 4041) ∨ (¬ p 4236) ∨ (¬ p 4376) :=
  ElevenRUP.step64625 (p 2027) (p 2230) (p 2427) (p 2797) (p 2881) (p 2963) (p 3366) (p 3519) (p 3877) (p 4041) (p 4236) (p 4376) (derived40810 p h) (h 40082)

theorem derived64626 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3549) ∨ (¬ p 4037) ∨ (¬ p 4245) ∨ (¬ p 4322) ∨ (¬ p 4397) :=
  ElevenRUP.step64626 (p 2027) (p 2295) (p 2750) (p 2753) (p 3276) (p 3355) (p 3362) (p 3549) (p 4037) (p 4245) (p 4322) (p 4397) (derived40810 p h) (h 40083)

theorem derived64631 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2751) ∨ (¬ p 3364) ∨ (¬ p 3584) :=
  ElevenRUP.step64631 (p 2027) (p 2573) (p 2656) (p 2727) (p 2751) (p 3364) (p 3584) (derived40810 p h) (h 40089)

theorem derived64633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3519) ∨ (¬ p 3659) ∨ (¬ p 3680) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64633 (p 2027) (p 2230) (p 2982) (p 3366) (p 3425) (p 3519) (p 3659) (p 3680) (p 4376) (p 5123) (p 5558) (derived40810 p h) (h 40091)

theorem derived64634 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3969) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4376) ∨ (¬ p 4446) ∨ (¬ p 5122) :=
  ElevenRUP.step64634 (p 2027) (p 2780) (p 3366) (p 3449) (p 3452) (p 3969) (p 4347) (p 4358) (p 4376) (p 4446) (p 5122) (derived40810 p h) (h 40092)

theorem derived64636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 4330) ∨ (¬ p 4348) :=
  ElevenRUP.step64636 (p 2027) (p 2132) (p 2252) (p 2750) (p 2753) (p 2860) (p 3125) (p 3414) (p 3553) (p 4330) (p 4348) (derived40810 p h) (h 40094)

theorem derived64640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2264) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3551) ∨ (¬ p 3947) ∨ (¬ p 4621) ∨ (¬ p 4789) ∨ (¬ p 4849) :=
  ElevenRUP.step64640 (p 2027) (p 2132) (p 2264) (p 2860) (p 3125) (p 3551) (p 3947) (p 4621) (p 4789) (p 4849) (derived40810 p h) (h 40098)

theorem derived64641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3201) ∨ (¬ p 3874) ∨ (¬ p 4383) ∨ (¬ p 4653) :=
  ElevenRUP.step64641 (p 2027) (p 2264) (p 3201) (p 3874) (p 4383) (p 4653) (derived40810 p h) (h 40099)

theorem derived64646 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3582) ∨ (¬ p 3876) ∨ (¬ p 4110) :=
  ElevenRUP.step64646 (p 1997) (p 2027) (p 2611) (p 2860) (p 3362) (p 3389) (p 3582) (p 3876) (p 4110) (h 2157) (derived40810 p h) (derived40877 p h) (h 40104)

theorem derived64648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2753) ∨ (¬ p 3609) ∨ (¬ p 4129) ∨ (¬ p 4261) ∨ (¬ p 4419) ∨ (¬ p 4436) ∨ (¬ p 4963) ∨ (¬ p 5560) ∨ (¬ p 5600) :=
  ElevenRUP.step64648 (p 2027) (p 2230) (p 2427) (p 2753) (p 3609) (p 4129) (p 4261) (p 4419) (p 4436) (p 4963) (p 5560) (p 5600) (derived40810 p h) (h 40106)

theorem derived64650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2553) ∨ (¬ p 3125) ∨ (¬ p 4137) :=
  ElevenRUP.step64650 (p 1998) (p 2027) (p 2177) (p 2553) (p 2765) (p 3125) (p 4137) (h 2158) (derived40810 p h) (derived40883 p h) (h 40108)

theorem derived64651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3105) ∨ (¬ p 3362) ∨ (¬ p 3680) ∨ (¬ p 3698) ∨ (¬ p 3860) ∨ (¬ p 5123) ∨ (¬ p 5693) :=
  ElevenRUP.step64651 (p 2027) (p 2230) (p 2241) (p 2750) (p 2753) (p 3105) (p 3362) (p 3680) (p 3698) (p 3860) (p 5123) (p 5693) (derived40810 p h) (h 40109)

theorem derived64653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2982) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4110) ∨ (¬ p 4348) ∨ (¬ p 4450) :=
  ElevenRUP.step64653 (p 2027) (p 2139) (p 2156) (p 2982) (p 3425) (p 3659) (p 4110) (p 4348) (p 4450) (derived40810 p h) (h 40111)

theorem derived64655 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2963) ∨ (¬ p 2992) ∨ (¬ p 3506) ∨ (¬ p 3549) ∨ (¬ p 3922) ∨ (¬ p 4107) ∨ (¬ p 4322) ∨ (¬ p 4395) ∨ (¬ p 5038) :=
  ElevenRUP.step64655 (p 2027) (p 2249) (p 2963) (p 2992) (p 3506) (p 3549) (p 3922) (p 4107) (p 4322) (p 4395) (p 5038) (derived40810 p h) (h 40113)

theorem derived64656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2588) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3888) ∨ (¬ p 4035) ∨ (¬ p 4866) ∨ (¬ p 5016) ∨ (¬ p 5250) ∨ (¬ p 5284) :=
  ElevenRUP.step64656 (p 2027) (p 2307) (p 2588) (p 3365) (p 3366) (p 3888) (p 4035) (p 4866) (p 5016) (p 5250) (p 5284) (derived40810 p h) (h 40114)

theorem derived64661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3551) ∨ (¬ p 3564) ∨ (¬ p 3947) ∨ (¬ p 4621) ∨ (¬ p 4789) ∨ (¬ p 4849) :=
  ElevenRUP.step64661 (p 2027) (p 2264) (p 2598) (p 3422) (p 3551) (p 3564) (p 3947) (p 4621) (p 4789) (p 4849) (derived40810 p h) (h 40119)

theorem derived64662 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3266) ∨ (¬ p 3292) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3684) ∨ (¬ p 4332) ∨ (¬ p 5284) :=
  ElevenRUP.step64662 (p 2027) (p 2230) (p 2252) (p 2750) (p 2753) (p 3266) (p 3292) (p 3333) (p 3362) (p 3684) (p 4332) (p 5284) (derived40810 p h) (h 40120)

theorem derived64664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 3817) ∨ (¬ p 5206) :=
  ElevenRUP.step64664 (p 1977) (p 2027) (p 2241) (p 2462) (p 3527) (p 3551) (p 3817) (p 5206) (h 2137) (derived40810 p h) (derived40875 p h) (h 40122)

theorem derived64667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4376) :=
  ElevenRUP.step64667 (p 2027) (p 2230) (p 2427) (p 3246) (p 3365) (p 3366) (p 3519) (p 3877) (p 3950) (p 4118) (p 4376) (derived40810 p h) (h 40125)

theorem derived64674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2685) ∨ (¬ p 3096) ∨ (¬ p 3276) ∨ (¬ p 3414) ∨ (¬ p 4035) ∨ (¬ p 4191) ∨ (¬ p 4236) ∨ (¬ p 4422) ∨ (¬ p 5279) :=
  ElevenRUP.step64674 (p 2027) (p 2139) (p 2156) (p 2685) (p 3096) (p 3276) (p 3414) (p 4035) (p 4191) (p 4236) (p 4422) (p 5279) (derived40810 p h) (h 40132)

theorem derived64678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 3346) ∨ (¬ p 3422) ∨ (¬ p 3684) :=
  ElevenRUP.step64678 (p 2005) (p 2027) (p 2230) (p 2964) (p 3346) (p 3422) (p 3684) (h 2165) (derived40810 p h) (derived40889 p h) (h 40139)

theorem derived64681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3172) ∨ (¬ p 3422) ∨ (¬ p 3888) ∨ (¬ p 4118) ∨ (¬ p 4444) ∨ (¬ p 4789) ∨ (¬ p 5250) :=
  ElevenRUP.step64681 (p 2027) (p 2598) (p 3172) (p 3422) (p 3888) (p 4118) (p 4444) (p 4789) (p 5250) (derived40810 p h) (h 40142)

theorem derived64682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2954) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4336) :=
  ElevenRUP.step64682 (p 2027) (p 2668) (p 2954) (p 3646) (p 3989) (p 4336) (derived40810 p h) (h 40143)

theorem derived64683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3365) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4419) :=
  ElevenRUP.step64683 (p 2027) (p 2396) (p 2553) (p 2573) (p 3365) (p 3877) (p 3950) (p 4118) (p 4419) (derived40810 p h) (h 40144)

theorem derived64688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2870) ∨ (¬ p 2963) ∨ (¬ p 3246) ∨ (¬ p 3324) ∨ (¬ p 3362) ∨ (¬ p 3698) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4789) :=
  ElevenRUP.step64688 (p 2027) (p 2230) (p 2870) (p 2963) (p 3246) (p 3324) (p 3362) (p 3698) (p 3950) (p 4347) (p 4789) (derived40810 p h) (h 40149)

theorem derived64689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 3096) ∨ (¬ p 3425) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 3659) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64689 (p 2027) (p 2139) (p 2156) (p 3096) (p 3425) (p 3461) (p 3564) (p 3659) (p 5123) (p 5558) (derived40810 p h) (h 40150)

theorem derived64693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3822) ∨ (¬ p 4019) ∨ (¬ p 4405) ∨ (¬ p 4861) ∨ (¬ p 5580) :=
  ElevenRUP.step64693 (p 2027) (p 3822) (p 4019) (p 4405) (p 4861) (p 5580) (derived40810 p h) (h 40154)

theorem derived64694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2427) ∨ (¬ p 3880) ∨ (¬ p 4132) ∨ (¬ p 4362) :=
  ElevenRUP.step64694 (p 2027) (p 2264) (p 2427) (p 3880) (p 4132) (p 4362) (derived40810 p h) (h 40155)

theorem derived64695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2264) ∨ (¬ p 2427) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4110) ∨ (¬ p 4362) :=
  ElevenRUP.step64695 (p 2027) (p 2139) (p 2156) (p 2264) (p 2427) (p 3425) (p 3659) (p 4110) (p 4362) (derived40810 p h) (h 40156)

theorem derived64697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 3548) ∨ (¬ p 4366) :=
  ElevenRUP.step64697 (p 1977) (p 2027) (p 2241) (p 2264) (p 2355) (p 3548) (p 4366) (h 2137) (derived40810 p h) (derived40872 p h) (h 40158)

theorem derived64698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2982) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3877) ∨ (¬ p 4110) ∨ (¬ p 4118) ∨ (¬ p 4330) ∨ (¬ p 4377) ∨ (¬ p 5045) :=
  ElevenRUP.step64698 (p 2027) (p 2156) (p 2982) (p 3365) (p 3366) (p 3370) (p 3877) (p 4110) (p 4118) (p 4330) (p 4377) (p 5045) (derived40810 p h) (h 40159)

theorem derived64699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2668) ∨ (¬ p 2787) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3568) ∨ (¬ p 3868) ∨ (¬ p 4556) ∨ (¬ p 5660) :=
  ElevenRUP.step64699 (p 2027) (p 2387) (p 2668) (p 2787) (p 3362) (p 3389) (p 3568) (p 3868) (p 4556) (p 5660) (derived40810 p h) (h 40160)

theorem derived64700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 4347) ∨ (¬ p 4444) :=
  ElevenRUP.step64700 (p 1991) (p 2027) (p 2764) (p 2963) (p 3324) (p 4347) (p 4444) (h 2151) (derived40810 p h) (derived40882 p h) (h 40161)

theorem derived64702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3684) ∨ (¬ p 4332) ∨ (¬ p 4347) ∨ (¬ p 4789) :=
  ElevenRUP.step64702 (p 2027) (p 2230) (p 2963) (p 3324) (p 3333) (p 3362) (p 3684) (p 4332) (p 4347) (p 4789) (derived40810 p h) (h 40164)

theorem derived64704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2284) ∨ (¬ p 3646) ∨ (¬ p 3694) ∨ (¬ p 4906) :=
  ElevenRUP.step64704 (p 2027) (p 2220) (p 2284) (p 3646) (p 3694) (p 4906) (derived40810 p h) (h 40166)

theorem derived64705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3877) ∨ (¬ p 4118) ∨ (¬ p 4191) ∨ (¬ p 4330) ∨ (¬ p 4376) :=
  ElevenRUP.step64705 (p 2027) (p 3276) (p 3355) (p 3365) (p 3366) (p 3519) (p 3877) (p 4118) (p 4191) (p 4330) (p 4376) (derived40810 p h) (h 40167)

theorem derived64708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3860) ∨ (¬ p 5123) ∨ (¬ p 5693) :=
  ElevenRUP.step64708 (p 2027) (p 2241) (p 2598) (p 2750) (p 2753) (p 3276) (p 3333) (p 3860) (p 5123) (p 5693) (derived40810 p h) (h 40170)

theorem derived64709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3641) ∨ (¬ p 4347) :=
  ElevenRUP.step64709 (p 1981) (p 2027) (p 2528) (p 2598) (p 2611) (p 3641) (p 4347) (h 2141) (derived40810 p h) (derived40877 p h) (h 40171)

theorem derived64716 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3324) ∨ (¬ p 4154) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step64716 (p 2027) (p 2132) (p 2247) (p 2870) (p 2881) (p 3324) (p 4154) (p 4503) (p 4733) (derived40810 p h) (h 40178)

theorem derived64718 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3969) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4377) ∨ (¬ p 4446) ∨ (¬ p 5122) :=
  ElevenRUP.step64718 (p 2027) (p 2780) (p 3366) (p 3449) (p 3555) (p 3969) (p 4347) (p 4358) (p 4377) (p 4446) (p 5122) (derived40810 p h) (h 40180)

theorem derived64719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2608) ∨ (¬ p 2761) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3591) ∨ (¬ p 3918) ∨ (¬ p 4329) ∨ (¬ p 4376) ∨ (¬ p 5254) :=
  ElevenRUP.step64719 (p 2027) (p 2417) (p 2608) (p 2761) (p 3389) (p 3519) (p 3591) (p 3918) (p 4329) (p 4376) (p 5254) (derived40810 p h) (h 40181)

theorem derived64721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2584) ∨ (¬ p 2588) ∨ (¬ p 3266) ∨ (¬ p 3519) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4376) ∨ (¬ p 4379) ∨ (¬ p 5387) :=
  ElevenRUP.step64721 (p 2027) (p 2307) (p 2584) (p 2588) (p 3266) (p 3519) (p 3564) (p 4330) (p 4376) (p 4379) (p 5387) (derived40810 p h) (h 40184)

theorem derived64725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2952) ∨ (¬ p 3027) ∨ (¬ p 3256) ∨ (¬ p 3989) ∨ (¬ p 4044) ∨ (¬ p 4173) ∨ (¬ p 4282) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64725 (p 2027) (p 2249) (p 2952) (p 3027) (p 3256) (p 3989) (p 4044) (p 4173) (p 4282) (p 4348) (p 4503) (derived40810 p h) (h 40188)

theorem derived64726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3684) ∨ (¬ p 3948) ∨ (¬ p 4031) ∨ (¬ p 4120) ∨ (¬ p 5217) :=
  ElevenRUP.step64726 (p 2027) (p 2166) (p 3684) (p 3948) (p 4031) (p 4120) (p 5217) (derived40810 p h) (h 40189)

theorem derived64727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2619) ∨ (¬ p 3146) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4604) ∨ (¬ p 4733) :=
  ElevenRUP.step64727 (p 2027) (p 2132) (p 2247) (p 2619) (p 3146) (p 4037) (p 4154) (p 4604) (p 4733) (derived40810 p h) (h 40190)

theorem derived64728 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2641) ∨ (¬ p 3031) ∨ (¬ p 3548) ∨ (¬ p 4195) :=
  ElevenRUP.step64728 (p 1987) (p 2027) (p 2177) (p 2641) (p 2997) (p 3031) (p 3548) (p 4195) (h 2147) (derived40810 p h) (derived40890 p h) (h 40191)

theorem derived64730 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2192) ∨ (¬ p 3737) ∨ (¬ p 4506) ∨ (¬ p 5586) :=
  ElevenRUP.step64730 (p 2027) (p 2191) (p 2192) (p 3737) (p 4506) (p 5586) (derived40810 p h) (h 40193)

theorem derived64732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 3319) ∨ (¬ p 3486) ∨ (¬ p 3946) ∨ (¬ p 4185) ∨ (¬ p 4338) ∨ (¬ p 4555) :=
  ElevenRUP.step64732 (p 2027) (p 2785) (p 3319) (p 3486) (p 3946) (p 4185) (p 4338) (p 4555) (derived40810 p h) (h 40195)

theorem derived64740 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3073) ∨ (¬ p 3695) ∨ (¬ p 4340) ∨ (¬ p 4359) ∨ (¬ p 4644) ∨ (¬ p 4688) :=
  ElevenRUP.step64740 (p 2027) (p 2928) (p 3073) (p 3695) (p 4340) (p 4359) (p 4644) (p 4688) (derived40810 p h) (h 40205)

theorem derived64741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2655) ∨ (¬ p 2946) ∨ (¬ p 3540) ∨ (¬ p 4704) :=
  ElevenRUP.step64741 (p 2027) (p 2437) (p 2655) (p 2946) (p 3540) (p 4704) (derived40810 p h) (h 40206)

theorem derived64742 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3941) ∨ (¬ p 3956) ∨ (¬ p 5580) :=
  ElevenRUP.step64742 (p 1975) (p 2027) (p 2553) (p 2633) (p 3941) (p 3956) (p 5580) (h 2135) (derived40810 p h) (derived40879 p h) (h 40207)

theorem derived64744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2352) ∨ (¬ p 2598) ∨ (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 3422) ∨ (¬ p 3556) ∨ (¬ p 4134) ∨ (¬ p 4733) :=
  ElevenRUP.step64744 (p 2027) (p 2191) (p 2352) (p 2598) (p 2891) (p 3369) (p 3422) (p 3556) (p 4134) (p 4733) (derived40810 p h) (h 40209)

theorem derived64746 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 4235) ∨ (¬ p 4363) ∨ (¬ p 4381) ∨ (¬ p 4382) :=
  ElevenRUP.step64746 (p 1997) (p 2027) (p 2764) (p 2891) (p 4235) (p 4363) (p 4381) (p 4382) (h 2157) (derived40810 p h) (derived40882 p h) (h 40211)

theorem derived64748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2373) ∨ (¬ p 3848) ∨ (¬ p 3969) ∨ (¬ p 5119) ∨ (¬ p 5190) ∨ (¬ p 5284) :=
  ElevenRUP.step64748 (p 2027) (p 2230) (p 2247) (p 2373) (p 3848) (p 3969) (p 5119) (p 5190) (p 5284) (derived40810 p h) (h 40213)

theorem derived64749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3361) ∨ (¬ p 3585) ∨ (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 3821) ∨ (¬ p 4749) ∨ (¬ p 4849) :=
  ElevenRUP.step64749 (p 2027) (p 3361) (p 3585) (p 3631) (p 3687) (p 3821) (p 4749) (p 4849) (derived40810 p h) (h 40214)

theorem derived64750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 3324) ∨ (¬ p 4154) ∨ (¬ p 4501) ∨ (¬ p 4733) :=
  ElevenRUP.step64750 (p 2027) (p 2132) (p 2247) (p 2274) (p 2860) (p 3324) (p 4154) (p 4501) (p 4733) (derived40810 p h) (h 40215)

theorem derived64753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3434) ∨ (¬ p 3585) ∨ (¬ p 3690) :=
  ElevenRUP.step64753 (p 1985) (p 2027) (p 2707) (p 2842) (p 3434) (p 3585) (p 3690) (h 2145) (derived40810 p h) (derived40885 p h) (h 40218)

theorem derived64756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2850) ∨ (¬ p 4340) ∨ (¬ p 4608) ∨ (¬ p 5368) :=
  ElevenRUP.step64756 (p 2027) (p 2528) (p 2850) (p 4340) (p 4608) (p 5368) (derived40810 p h) (h 40221)

theorem derived64757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2727) ∨ (¬ p 2901) ∨ (¬ p 2950) ∨ (¬ p 3413) ∨ (¬ p 3556) :=
  ElevenRUP.step64757 (p 2027) (p 2249) (p 2727) (p 2901) (p 2950) (p 3413) (p 3556) (derived40810 p h) (h 40222)

theorem derived64758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 2751) ∨ (¬ p 2901) ∨ (¬ p 3413) ∨ (¬ p 4244) ∨ (¬ p 4392) :=
  ElevenRUP.step64758 (p 2027) (p 2727) (p 2751) (p 2901) (p 3413) (p 4244) (p 4392) (derived40810 p h) (h 40223)

theorem derived64760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 2284) ∨ (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 4607) ∨ (¬ p 4705) :=
  ElevenRUP.step64760 (p 2027) (p 2190) (p 2284) (p 2534) (p 3146) (p 4607) (p 4705) (derived40810 p h) (h 40226)

theorem derived64762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2573) ∨ (¬ p 2996) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 4391) ∨ (¬ p 4831) ∨ (¬ p 5190) :=
  ElevenRUP.step64762 (p 2027) (p 2247) (p 2573) (p 2996) (p 3461) (p 3564) (p 4391) (p 4831) (p 5190) (derived40810 p h) (h 40229)

theorem derived64768 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2459) ∨ (¬ p 3555) ∨ (¬ p 3692) :=
  ElevenRUP.step64768 (p 1984) (p 2027) (p 2191) (p 2459) (p 2633) (p 3555) (p 3692) (h 2144) (derived40810 p h) (derived40879 p h) (h 40235)

theorem derived64769 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2459) ∨ (¬ p 3949) ∨ (¬ p 4363) ∨ (¬ p 4902) :=
  ElevenRUP.step64769 (p 2027) (p 2166) (p 2459) (p 3949) (p 4363) (p 4902) (derived40810 p h) (h 40238)

theorem derived64770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3369) ∨ (¬ p 3692) ∨ (¬ p 4120) ∨ (¬ p 4503) ∨ (¬ p 4733) :=
  ElevenRUP.step64770 (p 2027) (p 2363) (p 2598) (p 2911) (p 3201) (p 3369) (p 3692) (p 4120) (p 4503) (p 4733) (derived40810 p h) (h 40239)

theorem derived64779 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2656) ∨ (¬ p 2685) ∨ (¬ p 3758) ∨ (¬ p 4392) ∨ (¬ p 4399) ∨ (¬ p 4652) :=
  ElevenRUP.step64779 (p 2027) (p 2156) (p 2656) (p 2685) (p 3758) (p 4392) (p 4399) (p 4652) (derived40810 p h) (h 40248)

theorem derived64783 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3860) ∨ (¬ p 4133) ∨ (¬ p 4261) ∨ (¬ p 4733) :=
  ElevenRUP.step64783 (p 2027) (p 2352) (p 2459) (p 2598) (p 3422) (p 3860) (p 4133) (p 4261) (p 4733) (derived40810 p h) (h 40252)

theorem derived64784 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2245) ∨ (¬ p 2619) ∨ (¬ p 3027) ∨ (¬ p 3414) ∨ (¬ p 3758) ∨ (¬ p 4043) ∨ (¬ p 4360) ∨ (¬ p 4521) :=
  ElevenRUP.step64784 (p 2027) (p 2156) (p 2245) (p 2619) (p 3027) (p 3414) (p 3758) (p 4043) (p 4360) (p 4521) (derived40810 p h) (h 40254)

theorem derived64787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3857) ∨ (¬ p 3961) ∨ (¬ p 4173) ∨ (¬ p 4283) ∨ (¬ p 4496) ∨ (¬ p 4558) :=
  ElevenRUP.step64787 (p 2027) (p 3073) (p 3857) (p 3961) (p 4173) (p 4283) (p 4496) (p 4558) (derived40810 p h) (h 40258)

theorem derived64788 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2249) ∨ (¬ p 2373) ∨ (¬ p 2459) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3037) ∨ (¬ p 3414) ∨ (¬ p 3544) ∨ (¬ p 4261) ∨ (¬ p 4902) :=
  ElevenRUP.step64788 (p 2027) (p 2230) (p 2249) (p 2373) (p 2459) (p 2656) (p 2727) (p 3037) (p 3414) (p 3544) (p 4261) (p 4902) (derived40810 p h) (h 40261)

theorem derived64789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3238) ∨ (¬ p 3519) :=
  ElevenRUP.step64789 (p 1998) (p 2027) (p 2177) (p 2202) (p 2553) (p 2573) (p 3238) (p 3519) (h 2158) (derived40810 p h) (derived40867 p h) (h 40262)

theorem derived64793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3193) ∨ (¬ p 3519) ∨ (¬ p 3584) ∨ (¬ p 4022) ∨ (¬ p 4191) :=
  ElevenRUP.step64793 (p 1986) (p 2027) (p 2573) (p 2764) (p 3193) (p 3519) (p 3584) (p 4022) (p 4191) (h 2146) (derived40810 p h) (derived40882 p h) (h 40266)

theorem derived64794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2751) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3364) ∨ (¬ p 3584) ∨ (¬ p 3904) :=
  ElevenRUP.step64794 (p 2027) (p 2573) (p 2751) (p 2951) (p 2992) (p 3364) (p 3584) (p 3904) (derived40810 p h) (h 40267)

theorem derived64798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2249) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3037) ∨ (¬ p 3414) ∨ (¬ p 3548) ∨ (¬ p 3969) ∨ (¬ p 4348) ∨ (¬ p 5122) :=
  ElevenRUP.step64798 (p 2027) (p 2220) (p 2249) (p 2951) (p 2992) (p 3037) (p 3414) (p 3548) (p 3969) (p 4348) (p 5122) (derived40810 p h) (h 40272)

theorem derived64799 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3172) ∨ (¬ p 3941) ∨ (¬ p 4348) ∨ (¬ p 5600) :=
  ElevenRUP.step64799 (p 1991) (p 2027) (p 2766) (p 3172) (p 3941) (p 4348) (p 5600) (h 2151) (derived40810 p h) (derived40884 p h) (h 40273)

theorem derived64801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2383) ∨ (¬ p 2493) ∨ (¬ p 2578) ∨ (¬ p 3989) :=
  ElevenRUP.step64801 (p 1975) (p 2027) (p 2274) (p 2383) (p 2409) (p 2493) (p 2578) (p 3989) (h 2135) (derived40810 p h) (derived40874 p h) (h 40277)

theorem derived64802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 3662) ∨ (¬ p 3879) ∨ (¬ p 4610) :=
  ElevenRUP.step64802 (p 2027) (p 2470) (p 2656) (p 2727) (p 3662) (p 3879) (p 4610) (derived40810 p h) (h 40278)

theorem derived64805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 4111) :=
  ElevenRUP.step64805 (p 1982) (p 2027) (p 2202) (p 2440) (p 3189) (p 3256) (p 4111) (h 2142) (derived40810 p h) (derived40867 p h) (h 40283)

theorem derived64808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2274) ∨ (¬ p 3549) ∨ (¬ p 3591) :=
  ElevenRUP.step64808 (p 1977) (p 2027) (p 2241) (p 2274) (p 2765) (p 3549) (p 3591) (h 2137) (derived40810 p h) (derived40883 p h) (h 40288)

theorem derived64809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3097) ∨ (¬ p 3555) ∨ (¬ p 4173) :=
  ElevenRUP.step64809 (p 1977) (p 2027) (p 2241) (p 2997) (p 3097) (p 3555) (p 4173) (h 2137) (derived40810 p h) (derived40890 p h) (h 40289)

theorem derived64810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2850) ∨ (¬ p 2922) ∨ (¬ p 2952) ∨ (¬ p 3266) ∨ (¬ p 3497) ∨ (¬ p 3541) ∨ (¬ p 3876) ∨ (¬ p 4322) ∨ (¬ p 4335) :=
  ElevenRUP.step64810 (p 1997) (p 2027) (p 2252) (p 2750) (p 2766) (p 2850) (p 2922) (p 2952) (p 3266) (p 3497) (p 3541) (p 3876) (p 4322) (p 4335) (h 2157) (derived40810 p h) (derived40884 p h) (h 40290)

theorem derived64811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2952) ∨ (¬ p 3609) ∨ (¬ p 3952) ∨ (¬ p 3989) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64811 (p 2027) (p 2098) (p 2252) (p 2750) (p 2753) (p 2952) (p 3609) (p 3952) (p 3989) (p 4348) (p 4503) (derived40810 p h) (h 40291)

theorem derived64812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2950) ∨ (¬ p 3156) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 4120) ∨ (¬ p 4208) ∨ (¬ p 4368) :=
  ElevenRUP.step64812 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2950) (p 3156) (p 3422) (p 3564) (p 4120) (p 4208) (p 4368) (derived40810 p h) (h 40292)

theorem derived64813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 3873) :=
  ElevenRUP.step64813 (p 2027) (p 2241) (p 2750) (p 3055) (p 3367) (p 3873) (derived40810 p h) (h 40293)

theorem derived64816 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2963) ∨ (¬ p 2972) ∨ (¬ p 3324) ∨ (¬ p 3954) ∨ (¬ p 4347) ∨ (¬ p 4450) :=
  ElevenRUP.step64816 (p 2027) (p 2210) (p 2252) (p 2750) (p 2963) (p 2972) (p 3324) (p 3954) (p 4347) (p 4450) (derived40810 p h) (h 40296)

theorem derived64830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3516) ∨ (¬ p 3591) ∨ (¬ p 3819) ∨ (¬ p 4026) ∨ (¬ p 4444) ∨ (¬ p 4604) :=
  ElevenRUP.step64830 (p 2027) (p 2241) (p 2750) (p 2753) (p 2761) (p 3516) (p 3591) (p 3819) (p 4026) (p 4444) (p 4604) (derived40810 p h) (h 40310)

theorem derived64831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2341) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2860) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3659) ∨ (¬ p 3819) ∨ (¬ p 4136) ∨ (¬ p 4555) :=
  ElevenRUP.step64831 (p 2027) (p 2241) (p 2341) (p 2750) (p 2753) (p 2860) (p 3486) (p 3555) (p 3659) (p 3819) (p 4136) (p 4555) (derived40810 p h) (h 40311)

theorem derived64832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) :=
  ElevenRUP.step64832 (p 1977) (p 2027) (p 2241) (p 2633) (p 3486) (p 3555) (p 3570) (h 2137) (derived40810 p h) (derived40879 p h) (h 40312)

theorem derived64833 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2881) ∨ (¬ p 3548) ∨ (¬ p 4366) :=
  ElevenRUP.step64833 (p 1977) (p 2027) (p 2241) (p 2881) (p 2938) (p 3548) (p 4366) (h 2137) (derived40810 p h) (derived40888 p h) (h 40313)

theorem derived64836 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2482) ∨ (¬ p 3874) ∨ (¬ p 3998) ∨ (¬ p 4286) ∨ (¬ p 4730) :=
  ElevenRUP.step64836 (p 2027) (p 2482) (p 3874) (p 3998) (p 4286) (p 4730) (derived40810 p h) (h 40316)

theorem derived64842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4181) ∨ (¬ p 4376) ∨ (¬ p 5122) :=
  ElevenRUP.step64842 (p 2027) (p 2138) (p 3366) (p 3449) (p 3452) (p 3692) (p 3694) (p 4181) (p 4376) (p 5122) (derived40810 p h) (h 40323)

theorem derived64843 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (¬ p 4324) ∨ (¬ p 4366) ∨ (¬ p 4797) ∨ (¬ p 5362) :=
  ElevenRUP.step64843 (p 2027) (p 3830) (p 4324) (p 4366) (p 4797) (p 5362) (derived40810 p h) (h 40324)

theorem derived64844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3690) ∨ (¬ p 3954) ∨ (¬ p 4320) ∨ (¬ p 4666) :=
  ElevenRUP.step64844 (p 2027) (p 2252) (p 2750) (p 2952) (p 3399) (p 3527) (p 3690) (p 3954) (p 4320) (p 4666) (derived40810 p h) (h 40326)

theorem derived64846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3591) ∨ (¬ p 4037) ∨ (¬ p 4319) ∨ (¬ p 4381) ∨ (¬ p 4625) :=
  ElevenRUP.step64846 (p 2027) (p 2241) (p 2750) (p 2753) (p 3276) (p 3355) (p 3362) (p 3591) (p 4037) (p 4319) (p 4381) (p 4625) (derived40810 p h) (h 40328)

theorem derived64847 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2417) ∨ (¬ p 2933) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4376) :=
  ElevenRUP.step64847 (p 2027) (p 2138) (p 2417) (p 2933) (p 3366) (p 3399) (p 3452) (p 3692) (p 3694) (p 3950) (p 4376) (derived40810 p h) (h 40329)

theorem derived64848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3366) ∨ (¬ p 3452) ∨ (¬ p 3694) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64848 (p 2027) (p 2138) (p 3366) (p 3452) (p 3694) (p 3707) (p 3830) (p 4376) (p 5123) (p 5568) (derived40810 p h) (h 40330)

theorem derived64851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3591) ∨ (¬ p 3876) ∨ (¬ p 4037) ∨ (¬ p 4319) ∨ (¬ p 5322) :=
  ElevenRUP.step64851 (p 2027) (p 2241) (p 2750) (p 2753) (p 3333) (p 3362) (p 3389) (p 3591) (p 3876) (p 4037) (p 4319) (p 5322) (derived40810 p h) (h 40334)

theorem derived64852 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 3541) ∨ (¬ p 4108) :=
  ElevenRUP.step64852 (p 2027) (p 2241) (p 2750) (p 2922) (p 3540) (p 3541) (p 4108) (derived40810 p h) (h 40335)

theorem derived64855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3452) ∨ (¬ p 3516) ∨ (¬ p 3545) ∨ (¬ p 3817) ∨ (¬ p 4376) ∨ (¬ p 4400) :=
  ElevenRUP.step64855 (p 2027) (p 3452) (p 3516) (p 3545) (p 3817) (p 4376) (p 4400) (derived40810 p h) (h 40339)

theorem derived64857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2252) ∨ (¬ p 2396) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2952) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 3950) :=
  ElevenRUP.step64857 (p 2027) (p 2122) (p 2252) (p 2396) (p 2750) (p 2753) (p 2774) (p 2952) (p 3497) (p 3692) (p 3950) (derived40810 p h) (h 40341)

theorem derived64859 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2952) ∨ (¬ p 3422) ∨ (¬ p 3497) ∨ (¬ p 3564) ∨ (¬ p 3692) ∨ (¬ p 4330) :=
  ElevenRUP.step64859 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2952) (p 3422) (p 3497) (p 3564) (p 3692) (p 4330) (derived40810 p h) (h 40343)

theorem derived64860 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3877) ∨ (¬ p 4236) ∨ (¬ p 4312) ∨ (¬ p 5568) :=
  ElevenRUP.step64860 (p 1976) (p 2027) (p 2952) (p 3136) (p 3877) (p 3982) (p 4236) (p 4312) (p 5568) (h 2136) (derived40810 p h) (derived40909 p h) (h 40344)

theorem derived64862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2911) ∨ (¬ p 2933) ∨ (¬ p 3093) ∨ (¬ p 3452) ∨ (¬ p 4452) :=
  ElevenRUP.step64862 (p 1975) (p 2027) (p 2299) (p 2409) (p 2911) (p 2933) (p 3093) (p 3452) (p 4452) (h 2135) (derived40810 p h) (derived40874 p h) (h 40347)

theorem derived64863 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2241) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3051) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4244) ∨ (¬ p 4433) :=
  ElevenRUP.step64863 (p 2027) (p 2144) (p 2241) (p 2619) (p 2750) (p 2753) (p 3051) (p 3591) (p 3923) (p 4244) (p 4433) (derived40810 p h) (h 40348)

theorem derived64864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2299) ∨ (¬ p 2741) ∨ (¬ p 2810) ∨ (¬ p 3005) ∨ (¬ p 3172) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3527) ∨ (¬ p 4376) :=
  ElevenRUP.step64864 (p 1975) (p 2027) (p 2252) (p 2299) (p 2545) (p 2741) (p 2810) (p 3005) (p 3172) (p 3399) (p 3452) (p 3527) (p 4376) (h 2135) (derived40810 p h) (derived40876 p h) (h 40349)

theorem derived64867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2441) ∨ (¬ p 3426) ∨ (¬ p 3434) ∨ (¬ p 4278) ∨ (¬ p 4428) ∨ (¬ p 4509) :=
  ElevenRUP.step64867 (p 2027) (p 2373) (p 2441) (p 3426) (p 3434) (p 4278) (p 4428) (p 4509) (derived40810 p h) (h 40352)

theorem derived64871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2810) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 3579) ∨ (¬ p 3581) :=
  ElevenRUP.step64871 (p 1988) (p 2027) (p 2545) (p 2685) (p 2810) (p 3461) (p 3564) (p 3579) (p 3581) (h 2148) (derived40810 p h) (derived40876 p h) (h 40358)

theorem derived64872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 2588) ∨ (¬ p 2781) ∨ (¬ p 3564) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 4330) :=
  ElevenRUP.step64872 (p 2027) (p 2138) (p 2307) (p 2588) (p 2781) (p 3564) (p 3692) (p 3694) (p 4330) (derived40810 p h) (h 40359)

theorem derived64875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 3156) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 4120) ∨ (¬ p 4191) ∨ (¬ p 4208) ∨ (¬ p 4368) :=
  ElevenRUP.step64875 (p 2027) (p 2145) (p 3156) (p 3276) (p 3355) (p 3362) (p 4120) (p 4191) (p 4208) (p 4368) (derived40810 p h) (h 40362)

theorem derived64881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2573) ∨ (¬ p 3156) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 4120) ∨ (¬ p 4208) ∨ (¬ p 4950) :=
  ElevenRUP.step64881 (p 2027) (p 2145) (p 2573) (p 3156) (p 3333) (p 3362) (p 3584) (p 4120) (p 4208) (p 4950) (derived40810 p h) (h 40371)

theorem derived64885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3452) ∨ (¬ p 4210) :=
  ElevenRUP.step64885 (p 1998) (p 2027) (p 2210) (p 2409) (p 2427) (p 2881) (p 3452) (p 4210) (h 2158) (derived40810 p h) (derived40874 p h) (h 40375)

theorem derived64887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2563) ∨ (¬ p 3379) ∨ (¬ p 3954) :=
  ElevenRUP.step64887 (p 1990) (p 2027) (p 2114) (p 2406) (p 2563) (p 3379) (p 3954) (h 2150) (derived40810 p h) (derived40864 p h) (h 40377)

theorem derived64888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3641) ∨ (¬ p 4149) ∨ (¬ p 5558) :=
  ElevenRUP.step64888 (p 1998) (p 2027) (p 2598) (p 2611) (p 3641) (p 4149) (p 5558) (h 2158) (derived40810 p h) (derived40877 p h) (h 40378)

theorem derived64892 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2781) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3461) ∨ (¬ p 4035) ∨ (¬ p 4187) ∨ (¬ p 4236) ∨ (¬ p 4381) ∨ (¬ p 4663) :=
  ElevenRUP.step64892 (p 2027) (p 2307) (p 2781) (p 2952) (p 3136) (p 3461) (p 4035) (p 4187) (p 4236) (p 4381) (p 4663) (derived40810 p h) (h 40382)

theorem derived64893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2933) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4376) :=
  ElevenRUP.step64893 (p 2027) (p 2417) (p 2933) (p 3365) (p 3366) (p 3399) (p 3452) (p 3877) (p 3950) (p 4118) (p 4376) (derived40810 p h) (h 40383)

theorem derived64894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2850) ∨ (¬ p 3379) ∨ (¬ p 3954) ∨ (¬ p 4030) :=
  ElevenRUP.step64894 (p 1990) (p 2027) (p 2114) (p 2563) (p 2850) (p 3379) (p 3954) (p 4030) (h 2150) (derived40810 p h) (derived40864 p h) (h 40384)

theorem derived64899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3659) ∨ (¬ p 3692) ∨ (¬ p 4042) ∨ (¬ p 4181) ∨ (¬ p 4376) ∨ (¬ p 5122) :=
  ElevenRUP.step64899 (p 2027) (p 3366) (p 3425) (p 3449) (p 3452) (p 3659) (p 3692) (p 4042) (p 4181) (p 4376) (p 5122) (derived40810 p h) (h 40389)

theorem derived64902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 3365) ∨ (¬ p 3389) ∨ (¬ p 3877) ∨ (¬ p 4419) ∨ (¬ p 5123) ∨ (¬ p 5600) :=
  ElevenRUP.step64902 (p 2027) (p 2417) (p 2761) (p 3365) (p 3389) (p 3877) (p 4419) (p 5123) (p 5600) (derived40810 p h) (h 40392)

theorem derived64907 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3414) ∨ (¬ p 3452) ∨ (¬ p 3553) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4810) :=
  ElevenRUP.step64907 (p 2027) (p 2252) (p 3093) (p 3319) (p 3414) (p 3452) (p 3553) (p 4330) (p 4348) (p 4810) (derived40810 p h) (h 40397)

theorem derived64908 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2504) ∨ (¬ p 3093) ∨ (¬ p 3414) ∨ (¬ p 3452) ∨ (¬ p 3553) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4810) :=
  ElevenRUP.step64908 (p 2027) (p 2252) (p 2504) (p 3093) (p 3414) (p 3452) (p 3553) (p 3564) (p 4330) (p 4348) (p 4810) (derived40810 p h) (h 40398)

theorem derived64909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2192) ∨ (¬ p 3256) ∨ (¬ p 3857) ∨ (¬ p 4115) ∨ (¬ p 4237) :=
  ElevenRUP.step64909 (p 1990) (p 2027) (p 2191) (p 2192) (p 2388) (p 3256) (p 3857) (p 4115) (p 4237) (h 2150) (derived40810 p h) (derived40873 p h) (h 40399)

theorem derived64910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2470) ∨ (¬ p 2745) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 3414) ∨ (¬ p 3659) ∨ (¬ p 3904) ∨ (¬ p 4149) ∨ (¬ p 4325) ∨ (¬ p 4348) ∨ (¬ p 5122) :=
  ElevenRUP.step64910 (p 2027) (p 2252) (p 2470) (p 2745) (p 2951) (p 3136) (p 3414) (p 3659) (p 3904) (p 4149) (p 4325) (p 4348) (p 5122) (derived40810 p h) (h 40400)

theorem derived64911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3172) ∨ (¬ p 3791) ∨ (¬ p 4118) ∨ (¬ p 4444) ∨ (¬ p 4789) ∨ (¬ p 4826) :=
  ElevenRUP.step64911 (p 2027) (p 2122) (p 2774) (p 3172) (p 3791) (p 4118) (p 4444) (p 4789) (p 4826) (derived40810 p h) (h 40401)

theorem derived64912 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3399) ∨ (¬ p 3497) ∨ (¬ p 3631) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 3954) :=
  ElevenRUP.step64912 (p 2027) (p 2252) (p 2750) (p 2952) (p 3399) (p 3497) (p 3631) (p 3692) (p 3950) (p 3954) (derived40810 p h) (h 40402)

theorem derived64913 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 3389) ∨ (¬ p 3758) ∨ (¬ p 4393) ∨ (¬ p 4419) ∨ (¬ p 5254) :=
  ElevenRUP.step64913 (p 2027) (p 2138) (p 2417) (p 2761) (p 3389) (p 3758) (p 4393) (p 4419) (p 5254) (derived40810 p h) (h 40403)

theorem derived64914 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 3969) ∨ (¬ p 4134) ∨ (¬ p 5514) ∨ (¬ p 5579) :=
  ElevenRUP.step64914 (p 2027) (p 2352) (p 3969) (p 4134) (p 5514) (p 5579) (derived40810 p h) (h 40404)

theorem derived64915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3591) ∨ (¬ p 3918) ∨ (¬ p 4428) ∨ (¬ p 4509) :=
  ElevenRUP.step64915 (p 2027) (p 2166) (p 2210) (p 3591) (p 3918) (p 4428) (p 4509) (derived40810 p h) (h 40405)

theorem derived64916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2274) ∨ (¬ p 3452) :=
  ElevenRUP.step64916 (p 1975) (p 2027) (p 2192) (p 2210) (p 2274) (p 2409) (p 3452) (h 2135) (derived40810 p h) (derived40874 p h) (h 40406)

theorem derived64917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 2952) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 3497) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64917 (p 2027) (p 2252) (p 2750) (p 2753) (p 2761) (p 2952) (p 3434) (p 3471) (p 3497) (p 5123) (p 5568) (derived40810 p h) (h 40407)

theorem derived64919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 2588) ∨ (¬ p 2781) ∨ (¬ p 3888) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 5250) :=
  ElevenRUP.step64919 (p 2027) (p 2138) (p 2307) (p 2588) (p 2781) (p 3888) (p 4322) (p 4385) (p 5250) (derived40810 p h) (h 40409)

theorem derived64921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2761) ∨ (¬ p 3034) ∨ (¬ p 3440) ∨ (¬ p 3544) ∨ (¬ p 4321) :=
  ElevenRUP.step64921 (p 2027) (p 2449) (p 2761) (p 3034) (p 3440) (p 3544) (p 4321) (derived40810 p h) (h 40411)

theorem derived64922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2573) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3266) ∨ (¬ p 3292) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 3950) ∨ (¬ p 4331) ∨ (¬ p 4623) ∨ (¬ p 5284) :=
  ElevenRUP.step64922 (p 2027) (p 2252) (p 2573) (p 2750) (p 2753) (p 3266) (p 3292) (p 3333) (p 3362) (p 3584) (p 3950) (p 4331) (p 4623) (p 5284) (derived40810 p h) (h 40412)

theorem derived64925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2781) ∨ (¬ p 3365) ∨ (¬ p 3461) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4187) ∨ (¬ p 4381) :=
  ElevenRUP.step64925 (p 2027) (p 2307) (p 2781) (p 3365) (p 3461) (p 3877) (p 3950) (p 4118) (p 4187) (p 4381) (derived40810 p h) (h 40415)

theorem derived64926 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3055) ∨ (¬ p 4129) ∨ (¬ p 4425) ∨ (¬ p 4736) ∨ (¬ p 4826) ∨ (¬ p 5160) :=
  ElevenRUP.step64926 (p 2027) (p 2210) (p 2891) (p 3055) (p 4129) (p 4425) (p 4736) (p 4826) (p 5160) (derived40810 p h) (h 40416)

theorem derived64927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2954) ∨ (¬ p 4009) ∨ (¬ p 4120) ∨ (¬ p 4237) ∨ (¬ p 5568) :=
  ElevenRUP.step64927 (p 2027) (p 2954) (p 4009) (p 4120) (p 4237) (p 5568) (derived40810 p h) (h 40417)

theorem derived64928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2952) ∨ (¬ p 3791) ∨ (¬ p 4208) ∨ (¬ p 4322) ∨ (¬ p 4826) :=
  ElevenRUP.step64928 (p 2027) (p 2122) (p 2252) (p 2750) (p 2753) (p 2774) (p 2952) (p 3791) (p 4208) (p 4322) (p 4826) (derived40810 p h) (h 40418)

theorem derived64932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2373) ∨ (¬ p 3591) ∨ (¬ p 3918) ∨ (¬ p 4210) ∨ (¬ p 4428) ∨ (¬ p 4509) :=
  ElevenRUP.step64932 (p 2027) (p 2210) (p 2373) (p 3591) (p 3918) (p 4210) (p 4428) (p 4509) (derived40810 p h) (h 40422)

theorem derived64936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 3461) ∨ (¬ p 3519) ∨ (¬ p 3564) ∨ (¬ p 3694) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64936 (p 2027) (p 2138) (p 2573) (p 3366) (p 3461) (p 3519) (p 3564) (p 3694) (p 4376) (p 5123) (p 5568) (derived40810 p h) (h 40426)

theorem derived64939 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2588) ∨ (¬ p 2781) ∨ (¬ p 3365) ∨ (¬ p 3564) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4623) :=
  ElevenRUP.step64939 (p 2027) (p 2307) (p 2588) (p 2781) (p 3365) (p 3564) (p 3877) (p 3950) (p 4118) (p 4623) (derived40810 p h) (h 40430)

theorem derived64940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4376) :=
  ElevenRUP.step64940 (p 2027) (p 2138) (p 2396) (p 2553) (p 2573) (p 3366) (p 3519) (p 3692) (p 3694) (p 3950) (p 4376) (derived40810 p h) (h 40431)

theorem derived64944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3877) ∨ (¬ p 4041) ∨ (¬ p 4236) ∨ (¬ p 4348) ∨ (¬ p 4419) :=
  ElevenRUP.step64944 (p 2027) (p 2470) (p 2528) (p 2952) (p 3136) (p 3877) (p 4041) (p 4236) (p 4348) (p 4419) (derived40810 p h) (h 40435)

theorem derived64946 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3366) ∨ (¬ p 3425) ∨ (¬ p 3452) ∨ (¬ p 3659) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4042) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64946 (p 2027) (p 3366) (p 3425) (p 3452) (p 3659) (p 3707) (p 3830) (p 4042) (p 4376) (p 5123) (p 5568) (derived40810 p h) (h 40438)

theorem derived64947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3365) ∨ (¬ p 3497) ∨ (¬ p 4315) ∨ (¬ p 4348) ∨ (¬ p 4419) ∨ (¬ p 4905) :=
  ElevenRUP.step64947 (p 2027) (p 2470) (p 2528) (p 3365) (p 3497) (p 4315) (p 4348) (p 4419) (p 4905) (derived40810 p h) (h 40439)

theorem derived64950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 2509) ∨ (¬ p 3256) ∨ (¬ p 3857) ∨ (¬ p 4121) ∨ (¬ p 4811) :=
  ElevenRUP.step64950 (p 2027) (p 2481) (p 2509) (p 3256) (p 3857) (p 4121) (p 4811) (derived40810 p h) (h 40442)

theorem derived64951 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2745) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 4261) ∨ (¬ p 4262) ∨ (¬ p 4590) ∨ (¬ p 4988) :=
  ElevenRUP.step64951 (p 2027) (p 2088) (p 2745) (p 2951) (p 3136) (p 4261) (p 4262) (p 4590) (p 4988) (derived40810 p h) (h 40443)

theorem derived64952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3452) :=
  ElevenRUP.step64952 (p 1998) (p 2027) (p 2210) (p 2409) (p 2881) (p 2891) (p 3452) (h 2158) (derived40810 p h) (derived40874 p h) (h 40444)

theorem derived64954 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2952) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3497) ∨ (¬ p 3584) ∨ (¬ p 3692) ∨ (¬ p 4330) ∨ (¬ p 4331) ∨ (¬ p 4789) :=
  ElevenRUP.step64954 (p 2027) (p 2573) (p 2952) (p 3333) (p 3362) (p 3497) (p 3584) (p 3692) (p 4330) (p 4331) (p 4789) (derived40810 p h) (h 40446)

theorem derived64961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4376) :=
  ElevenRUP.step64961 (p 2027) (p 2396) (p 2553) (p 2573) (p 3365) (p 3366) (p 3519) (p 3877) (p 3950) (p 4118) (p 4376) (derived40810 p h) (h 40453)

theorem derived64962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2252) ∨ (¬ p 2313) ∨ (¬ p 2750) ∨ (¬ p 2972) ∨ (¬ p 3552) ∨ (¬ p 3553) ∨ (¬ p 3954) ∨ (¬ p 3983) ∨ (¬ p 4348) ∨ (¬ p 4450) :=
  ElevenRUP.step64962 (p 2027) (p 2210) (p 2252) (p 2313) (p 2750) (p 2972) (p 3552) (p 3553) (p 3954) (p 3983) (p 4348) (p 4450) (derived40810 p h) (h 40454)

theorem derived64963 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2982) ∨ (¬ p 3452) ∨ (¬ p 3680) ∨ (¬ p 4210) :=
  ElevenRUP.step64963 (p 1988) (p 2027) (p 2210) (p 2409) (p 2982) (p 3452) (p 3680) (p 4210) (h 2148) (derived40810 p h) (derived40874 p h) (h 40455)

theorem derived64965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2750) ∨ (¬ p 3541) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4348) ∨ (¬ p 4503) :=
  ElevenRUP.step64965 (p 2027) (p 2241) (p 2518) (p 2528) (p 2750) (p 3541) (p 3591) (p 3923) (p 4348) (p 4503) (derived40810 p h) (h 40458)

theorem derived64966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 4191) ∨ (¬ p 4330) ∨ (¬ p 4789) :=
  ElevenRUP.step64966 (p 2027) (p 2952) (p 3276) (p 3355) (p 3362) (p 3497) (p 3692) (p 4191) (p 4330) (p 4789) (derived40810 p h) (h 40459)

theorem derived64971 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3201) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 4261) :=
  ElevenRUP.step64971 (p 2027) (p 2241) (p 2417) (p 2598) (p 2750) (p 2753) (p 3201) (p 3860) (p 3950) (p 4261) (derived40810 p h) (h 40464)

theorem derived64977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 4381) :=
  ElevenRUP.step64977 (p 1983) (p 2027) (p 2233) (p 2573) (p 3461) (p 3564) (p 4381) (h 2143) (derived40810 p h) (derived40868 p h) (h 40471)

theorem derived64978 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 3389) ∨ (¬ p 3694) ∨ (¬ p 4419) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step64978 (p 2027) (p 2138) (p 2417) (p 2761) (p 3389) (p 3694) (p 4419) (p 5123) (p 5568) (derived40810 p h) (h 40472)

theorem derived64980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2417) ∨ (¬ p 3791) ∨ (¬ p 5503) :=
  ElevenRUP.step64980 (p 1983) (p 2027) (p 2274) (p 2417) (p 2765) (p 3791) (p 5503) (h 2143) (derived40810 p h) (derived40883 p h) (h 40475)

theorem derived64983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2264) ∨ (¬ p 2750) ∨ (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3551) ∨ (¬ p 3947) ∨ (¬ p 3954) ∨ (¬ p 4621) ∨ (¬ p 4849) :=
  ElevenRUP.step64983 (p 2027) (p 2252) (p 2264) (p 2750) (p 3093) (p 3319) (p 3551) (p 3947) (p 3954) (p 4621) (p 4849) (derived40810 p h) (h 40478)

theorem derived64987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3346) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4440) :=
  ElevenRUP.step64987 (p 2027) (p 2573) (p 3346) (p 3564) (p 4330) (p 4440) (derived40810 p h) (h 40483)

theorem derived64988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 3564) ∨ (¬ p 3581) ∨ (¬ p 3791) ∨ (¬ p 4623) ∨ (¬ p 5503) :=
  ElevenRUP.step64988 (p 1983) (p 2027) (p 2274) (p 2765) (p 3564) (p 3581) (p 3791) (p 4623) (p 5503) (h 2143) (derived40810 p h) (derived40883 p h) (h 40484)

theorem derived64992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 3366) ∨ (¬ p 3414) ∨ (¬ p 3452) ∨ (¬ p 3553) ∨ (¬ p 4236) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4376) :=
  ElevenRUP.step64992 (p 2027) (p 3093) (p 3319) (p 3366) (p 3414) (p 3452) (p 3553) (p 4236) (p 4330) (p 4348) (p 4376) (derived40810 p h) (h 40489)

theorem derived64995 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3362) ∨ (¬ p 3414) ∨ (¬ p 3461) ∨ (¬ p 3553) ∨ (¬ p 3564) ∨ (¬ p 4789) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step64995 (p 2027) (p 2573) (p 3362) (p 3414) (p 3461) (p 3553) (p 3564) (p 4789) (p 5123) (p 5558) (derived40810 p h) (h 40492)

theorem derived64996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 2952) ∨ (¬ p 3201) ∨ (¬ p 3690) ∨ (¬ p 4320) ∨ (¬ p 4666) :=
  ElevenRUP.step64996 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2911) (p 2952) (p 3201) (p 3690) (p 4320) (p 4666) (derived40810 p h) (h 40493)

theorem derived64997 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2952) ∨ (¬ p 3201) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 3950) :=
  ElevenRUP.step64997 (p 2027) (p 2252) (p 2417) (p 2598) (p 2750) (p 2753) (p 2952) (p 3201) (p 3497) (p 3692) (p 3950) (derived40810 p h) (h 40494)

theorem derived64998 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3553) ∨ (¬ p 3556) ∨ (¬ p 4191) ∨ (¬ p 4330) ∨ (¬ p 4333) ∨ (¬ p 4348) :=
  ElevenRUP.step64998 (p 2027) (p 2145) (p 3276) (p 3355) (p 3362) (p 3553) (p 3556) (p 4191) (p 4330) (p 4333) (p 4348) (derived40810 p h) (h 40495)

theorem derived64999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 3641) ∨ (¬ p 4425) ∨ (¬ p 5160) :=
  ElevenRUP.step64999 (p 2007) (p 2027) (p 2766) (p 3266) (p 3641) (p 4425) (p 5160) (h 2167) (derived40810 p h) (derived40884 p h) (h 40496)

theorem derived65001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3584) ∨ (¬ p 4332) ∨ (¬ p 4348) ∨ (¬ p 4789) :=
  ElevenRUP.step65001 (p 2027) (p 2573) (p 3333) (p 3362) (p 3414) (p 3553) (p 3584) (p 4332) (p 4348) (p 4789) (derived40810 p h) (h 40498)

theorem derived65003 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3019) ∨ (¬ p 3591) ∨ (¬ p 4228) ∨ (¬ p 4435) :=
  ElevenRUP.step65003 (p 1984) (p 2027) (p 2202) (p 2440) (p 3019) (p 3591) (p 4228) (p 4435) (h 2144) (derived40810 p h) (derived40867 p h) (h 40500)

theorem derived65010 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3032) ∨ (¬ p 3201) ∨ (¬ p 4366) ∨ (¬ p 4391) ∨ (¬ p 5559) :=
  ElevenRUP.step65010 (p 2027) (p 2241) (p 2598) (p 2750) (p 2753) (p 2911) (p 3032) (p 3201) (p 4366) (p 4391) (p 5559) (derived40810 p h) (h 40507)

theorem derived65011 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3266) ∨ (¬ p 3834) ∨ (¬ p 4321) :=
  ElevenRUP.step65011 (p 1977) (p 2027) (p 2241) (p 2766) (p 3266) (p 3834) (p 4321) (h 2137) (derived40810 p h) (derived40884 p h) (h 40508)

theorem derived65012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2584) ∨ (¬ p 3584) ∨ (¬ p 3654) ∨ (¬ p 4137) ∨ (¬ p 4730) :=
  ElevenRUP.step65012 (p 2027) (p 2584) (p 3584) (p 3654) (p 4137) (p 4730) (derived40810 p h) (h 40509)

theorem derived65013 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3692) ∨ (¬ p 3860) ∨ (¬ p 3906) ∨ (¬ p 3979) ∨ (¬ p 5122) :=
  ElevenRUP.step65013 (p 2027) (p 2241) (p 2750) (p 2753) (p 2774) (p 2819) (p 3692) (p 3860) (p 3906) (p 3979) (p 5122) (derived40810 p h) (h 40510)

theorem derived65017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3684) ∨ (¬ p 4375) :=
  ElevenRUP.step65017 (p 1991) (p 2027) (p 2202) (p 2819) (p 2963) (p 3324) (p 3684) (p 4375) (h 2151) (derived40810 p h) (derived40867 p h) (h 40515)

theorem derived65021 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 4195) ∨ (¬ p 4376) ∨ (¬ p 5254) ∨ (¬ p 5717) :=
  ElevenRUP.step65021 (p 2027) (p 2417) (p 2761) (p 3365) (p 3366) (p 3389) (p 3519) (p 4195) (p 4376) (p 5254) (p 5717) (derived40810 p h) (h 40519)

theorem derived65024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2284) ∨ (¬ p 2753) ∨ (¬ p 3497) ∨ (¬ p 3609) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 4348) ∨ (¬ p 4877) ∨ (¬ p 4905) :=
  ElevenRUP.step65024 (p 2027) (p 2098) (p 2284) (p 2753) (p 3497) (p 3609) (p 3645) (p 3646) (p 4348) (p 4877) (p 4905) (derived40810 p h) (h 40522)

theorem derived65025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2761) ∨ (¬ p 2933) ∨ (¬ p 3399) ∨ (¬ p 3452) :=
  ElevenRUP.step65025 (p 1988) (p 2027) (p 2409) (p 2417) (p 2761) (p 2933) (p 3399) (p 3452) (h 2148) (derived40810 p h) (derived40874 p h) (h 40523)

theorem derived65027 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2753) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3497) ∨ (¬ p 3641) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3876) ∨ (¬ p 4158) ∨ (¬ p 4877) :=
  ElevenRUP.step65027 (p 2027) (p 2284) (p 2753) (p 3362) (p 3389) (p 3497) (p 3641) (p 3645) (p 3646) (p 3876) (p 4158) (p 4877) (derived40810 p h) (h 40525)

theorem derived65029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2963) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3641) ∨ (¬ p 3876) ∨ (¬ p 4118) ∨ (¬ p 4196) ∨ (¬ p 4596) ∨ (¬ p 4789) :=
  ElevenRUP.step65029 (p 2027) (p 2363) (p 2963) (p 3362) (p 3389) (p 3641) (p 3876) (p 4118) (p 4196) (p 4596) (p 4789) (derived40810 p h) (h 40527)

theorem derived65031 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2284) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3646) ∨ (¬ p 3951) ∨ (¬ p 4208) :=
  ElevenRUP.step65031 (p 2027) (p 2145) (p 2284) (p 2417) (p 2598) (p 3201) (p 3646) (p 3951) (p 4208) (derived40810 p h) (h 40529)

theorem derived65032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3834) ∨ (¬ p 4666) ∨ (¬ p 5358) :=
  ElevenRUP.step65032 (p 2027) (p 3399) (p 3527) (p 3834) (p 4666) (p 5358) (derived40810 p h) (h 40530)

theorem derived65034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 4236) ∨ (¬ p 4503) ∨ (¬ p 4804) :=
  ElevenRUP.step65034 (p 2027) (p 2098) (p 2963) (p 3324) (p 4236) (p 4503) (p 4804) (derived40810 p h) (h 40532)

theorem derived65035 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2911) ∨ (¬ p 4278) ∨ (¬ p 4445) ∨ (¬ p 4503) :=
  ElevenRUP.step65035 (p 2027) (p 2363) (p 2911) (p 4278) (p 4445) (p 4503) (derived40810 p h) (h 40533)

theorem derived65044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2459) ∨ (¬ p 2657) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3574) ∨ (¬ p 4137) ∨ (¬ p 4604) :=
  ElevenRUP.step65044 (p 2027) (p 2252) (p 2459) (p 2657) (p 2717) (p 2750) (p 2753) (p 3471) (p 3574) (p 4137) (p 4604) (derived40810 p h) (h 40542)

theorem derived65045 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 3860) ∨ (¬ p 4261) :=
  ElevenRUP.step65045 (p 1977) (p 2027) (p 2241) (p 2459) (p 2633) (p 3860) (p 4261) (h 2137) (derived40810 p h) (derived40879 p h) (h 40544)

theorem derived65046 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3097) ∨ (¬ p 3266) ∨ (¬ p 4025) ∨ (¬ p 4191) :=
  ElevenRUP.step65046 (p 1990) (p 2027) (p 2459) (p 2633) (p 3097) (p 3266) (p 4025) (p 4191) (h 2150) (derived40810 p h) (derived40879 p h) (h 40545)

theorem derived65047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2518) ∨ (¬ p 4149) ∨ (¬ p 5558) :=
  ElevenRUP.step65047 (p 1982) (p 2027) (p 2409) (p 2459) (p 2518) (p 4149) (p 5558) (h 2142) (derived40810 p h) (derived40874 p h) (h 40546)

theorem derived65048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 3032) ∨ (¬ p 3919) ∨ (¬ p 4118) ∨ (¬ p 4366) :=
  ElevenRUP.step65048 (p 1977) (p 2027) (p 2241) (p 2459) (p 2633) (p 3032) (p 3919) (p 4118) (p 4366) (h 2137) (derived40810 p h) (derived40879 p h) (h 40547)

theorem derived65049 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2315) ∨ (¬ p 2459) ∨ (¬ p 3857) ∨ (¬ p 3961) :=
  ElevenRUP.step65049 (p 2027) (p 2177) (p 2315) (p 2459) (p 3857) (p 3961) (derived40810 p h) (h 40548)

theorem derived65051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 3073) ∨ (¬ p 3414) ∨ (¬ p 3449) ∨ (¬ p 3553) ∨ (¬ p 3954) ∨ (¬ p 5118) ∨ (¬ p 5558) :=
  ElevenRUP.step65051 (p 2027) (p 2252) (p 2750) (p 3073) (p 3414) (p 3449) (p 3553) (p 3954) (p 5118) (p 5558) (derived40810 p h) (h 40550)

theorem derived65052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3146) ∨ (¬ p 3941) ∨ (¬ p 4188) ∨ (¬ p 4988) ∨ (¬ p 5612) :=
  ElevenRUP.step65052 (p 1982) (p 2027) (p 2148) (p 2341) (p 3146) (p 3941) (p 4188) (p 4988) (p 5612) (h 2142) (derived40810 p h) (derived40865 p h) (h 40551)

theorem derived65056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3051) ∨ (¬ p 3146) ∨ (¬ p 4244) :=
  ElevenRUP.step65056 (p 1982) (p 2027) (p 2148) (p 2619) (p 3051) (p 3146) (p 4244) (h 2142) (derived40810 p h) (derived40865 p h) (h 40555)

theorem derived65060 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3876) ∨ (¬ p 3954) :=
  ElevenRUP.step65060 (p 1986) (p 2027) (p 2114) (p 2922) (p 3379) (p 3876) (p 3954) (h 2146) (derived40810 p h) (derived40864 p h) (h 40561)

theorem derived65061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2579) ∨ (¬ p 2619) ∨ (¬ p 2655) ∨ (¬ p 3016) ∨ (¬ p 3146) ∨ (¬ p 3359) ∨ (¬ p 4022) ∨ (¬ p 4604) ∨ (¬ p 4789) :=
  ElevenRUP.step65061 (p 2027) (p 2132) (p 2579) (p 2619) (p 2655) (p 3016) (p 3146) (p 3359) (p 4022) (p 4604) (p 4789) (derived40810 p h) (h 40563)

theorem derived65062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2717) ∨ (¬ p 3359) ∨ (¬ p 3471) ∨ (¬ p 3941) ∨ (¬ p 4425) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65062 (p 2027) (p 2657) (p 2717) (p 3359) (p 3471) (p 3941) (p 4425) (p 4789) (p 5119) (derived40810 p h) (h 40564)

theorem derived65064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2459) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3016) ∨ (¬ p 3359) ∨ (¬ p 3471) ∨ (¬ p 4697) :=
  ElevenRUP.step65064 (p 2027) (p 2252) (p 2459) (p 2579) (p 2655) (p 2717) (p 2750) (p 2753) (p 3016) (p 3359) (p 3471) (p 4697) (derived40810 p h) (h 40566)

theorem derived65065 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2579) ∨ (¬ p 2655) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3941) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 5119) :=
  ElevenRUP.step65065 (p 2027) (p 2252) (p 2579) (p 2655) (p 2717) (p 2750) (p 2753) (p 3471) (p 3941) (p 4137) (p 4191) (p 5119) (derived40810 p h) (h 40567)

theorem derived65066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3051) ∨ (¬ p 3105) ∨ (¬ p 3292) ∨ (¬ p 3461) ∨ (¬ p 4244) ∨ (¬ p 4397) ∨ (¬ p 5284) :=
  ElevenRUP.step65066 (p 2027) (p 2144) (p 2252) (p 2750) (p 2753) (p 3051) (p 3105) (p 3292) (p 3461) (p 4244) (p 4397) (p 5284) (derived40810 p h) (h 40568)

theorem derived65068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2341) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3434) ∨ (¬ p 3574) ∨ (¬ p 3659) ∨ (¬ p 3819) ∨ (¬ p 4137) ∨ (¬ p 4625) :=
  ElevenRUP.step65068 (p 2027) (p 2252) (p 2341) (p 2657) (p 2750) (p 2753) (p 3434) (p 3574) (p 3659) (p 3819) (p 4137) (p 4625) (derived40810 p h) (h 40570)

theorem derived65069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2619) ∨ (¬ p 3146) ∨ (¬ p 3954) ∨ (¬ p 4243) :=
  ElevenRUP.step65069 (p 1982) (p 2027) (p 2114) (p 2210) (p 2619) (p 3146) (p 3954) (p 4243) (h 2142) (derived40810 p h) (derived40864 p h) (h 40571)

theorem derived65073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3659) ∨ (¬ p 4366) ∨ (¬ p 4797) ∨ (¬ p 5307) :=
  ElevenRUP.step65073 (p 2027) (p 3449) (p 3659) (p 4366) (p 4797) (p 5307) (derived40810 p h) (h 40575)

theorem derived65074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3516) ∨ (¬ p 3574) ∨ (¬ p 3819) ∨ (¬ p 4137) ∨ (¬ p 4444) ∨ (¬ p 4604) :=
  ElevenRUP.step65074 (p 2027) (p 2252) (p 2657) (p 2750) (p 2753) (p 2761) (p 3516) (p 3574) (p 3819) (p 4137) (p 4444) (p 4604) (derived40810 p h) (h 40576)

theorem derived65075 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2341) ∨ (¬ p 2459) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3266) ∨ (¬ p 3574) ∨ (¬ p 3819) ∨ (¬ p 5254) ∨ (¬ p 5514) :=
  ElevenRUP.step65075 (p 2027) (p 2252) (p 2341) (p 2459) (p 2657) (p 2750) (p 2753) (p 3266) (p 3574) (p 3819) (p 5254) (p 5514) (derived40810 p h) (h 40578)

theorem derived65077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2341) ∨ (¬ p 2459) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3266) ∨ (¬ p 3591) ∨ (¬ p 3819) ∨ (¬ p 4435) ∨ (¬ p 5254) :=
  ElevenRUP.step65077 (p 2027) (p 2241) (p 2341) (p 2459) (p 2750) (p 2753) (p 3266) (p 3591) (p 3819) (p 4435) (p 5254) (derived40810 p h) (h 40580)

theorem derived65078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2341) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3434) ∨ (¬ p 3591) ∨ (¬ p 3659) ∨ (¬ p 3819) ∨ (¬ p 4026) ∨ (¬ p 4625) :=
  ElevenRUP.step65078 (p 2027) (p 2241) (p 2341) (p 2750) (p 2753) (p 3434) (p 3591) (p 3659) (p 3819) (p 4026) (p 4625) (derived40810 p h) (h 40581)

theorem derived65080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3156) ∨ (¬ p 3879) ∨ (¬ p 3904) ∨ (¬ p 4120) ∨ (¬ p 4717) :=
  ElevenRUP.step65080 (p 2027) (p 2573) (p 3156) (p 3879) (p 3904) (p 4120) (p 4717) (derived40810 p h) (h 40583)

theorem derived65082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 4181) ∨ (¬ p 4416) ∨ (¬ p 5316) ∨ (¬ p 5590) :=
  ElevenRUP.step65082 (p 2027) (p 2241) (p 2750) (p 4181) (p 4416) (p 5316) (p 5590) (derived40810 p h) (h 40585)

theorem derived65083 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3266) ∨ (¬ p 3609) ∨ (¬ p 4366) ∨ (¬ p 4442) ∨ (¬ p 4831) :=
  ElevenRUP.step65083 (p 2027) (p 2098) (p 2241) (p 2750) (p 2753) (p 3266) (p 3609) (p 4366) (p 4442) (p 4831) (derived40810 p h) (h 40586)

theorem derived65085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3692) ∨ (¬ p 3954) :=
  ElevenRUP.step65085 (p 2001) (p 2027) (p 2114) (p 3073) (p 3449) (p 3692) (p 3954) (h 2161) (derived40810 p h) (derived40864 p h) (h 40588)

theorem derived65087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3860) ∨ (¬ p 5118) ∨ (¬ p 5693) :=
  ElevenRUP.step65087 (p 2027) (p 2241) (p 2459) (p 2717) (p 2750) (p 2753) (p 3471) (p 3860) (p 5118) (p 5693) (derived40810 p h) (h 40590)

theorem derived65088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3591) ∨ (¬ p 4026) ∨ (¬ p 4604) :=
  ElevenRUP.step65088 (p 2027) (p 2241) (p 2459) (p 2717) (p 2750) (p 2753) (p 3471) (p 3591) (p 4026) (p 4604) (derived40810 p h) (h 40591)

theorem derived65089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2753) ∨ (¬ p 2901) ∨ (¬ p 3497) ∨ (¬ p 3556) ∨ (¬ p 3609) ∨ (¬ p 3645) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4877) :=
  ElevenRUP.step65089 (p 2027) (p 2098) (p 2753) (p 2901) (p 3497) (p 3556) (p 3609) (p 3645) (p 4134) (p 4347) (p 4877) (derived40810 p h) (h 40592)

theorem derived65092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3156) ∨ (¬ p 3860) ∨ (¬ p 3906) ∨ (¬ p 4957) :=
  ElevenRUP.step65092 (p 2027) (p 2210) (p 3156) (p 3860) (p 3906) (p 4957) (derived40810 p h) (h 40598)

theorem derived65096 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3105) ∨ (¬ p 3680) ∨ (¬ p 4444) :=
  ElevenRUP.step65096 (p 1982) (p 2027) (p 2132) (p 2611) (p 3105) (p 3680) (p 4444) (h 2142) (derived40810 p h) (derived40877 p h) (h 40602)

theorem derived65100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2761) ∨ (¬ p 3073) ∨ (¬ p 3292) ∨ (¬ p 3449) ∨ (¬ p 3954) ∨ (¬ p 4669) ∨ (¬ p 5284) :=
  ElevenRUP.step65100 (p 2027) (p 2252) (p 2750) (p 2761) (p 3073) (p 3292) (p 3449) (p 3954) (p 4669) (p 5284) (derived40810 p h) (h 40607)

theorem derived65102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3414) ∨ (¬ p 3737) ∨ (¬ p 3947) ∨ (¬ p 4381) ∨ (¬ p 4789) ∨ (¬ p 5250) :=
  ElevenRUP.step65102 (p 2027) (p 2132) (p 2860) (p 3414) (p 3737) (p 3947) (p 4381) (p 4789) (p 5250) (derived40810 p h) (h 40609)

theorem derived65103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 3969) ∨ (¬ p 4037) ∨ (¬ p 4191) ∨ (¬ p 5119) :=
  ElevenRUP.step65103 (p 2027) (p 2132) (p 2252) (p 2619) (p 2750) (p 2753) (p 2963) (p 3969) (p 4037) (p 4191) (p 5119) (derived40810 p h) (h 40610)

theorem derived65104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2952) ∨ (¬ p 3471) ∨ (¬ p 3941) ∨ (¬ p 4208) ∨ (¬ p 4322) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65104 (p 2027) (p 2717) (p 2952) (p 3471) (p 3941) (p 4208) (p 4322) (p 4789) (p 5119) (derived40810 p h) (h 40611)

theorem derived65105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2952) ∨ (¬ p 3570) ∨ (¬ p 3609) ∨ (¬ p 4133) ∨ (¬ p 4320) ∨ (¬ p 4347) ∨ (¬ p 4789) :=
  ElevenRUP.step65105 (p 2027) (p 2098) (p 2952) (p 3570) (p 3609) (p 4133) (p 4320) (p 4347) (p 4789) (derived40810 p h) (h 40612)

theorem derived65107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2963) ∨ (¬ p 3568) ∨ (¬ p 3641) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4789) :=
  ElevenRUP.step65107 (p 2027) (p 2528) (p 2598) (p 2963) (p 3568) (p 3641) (p 4107) (p 4669) (p 4789) (derived40810 p h) (h 40614)

theorem derived65108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2761) ∨ (¬ p 2787) ∨ (¬ p 3641) ∨ (¬ p 3946) ∨ (¬ p 4191) ∨ (¬ p 4669) :=
  ElevenRUP.step65108 (p 2027) (p 2528) (p 2598) (p 2761) (p 2787) (p 3641) (p 3946) (p 4191) (p 4669) (derived40810 p h) (h 40615)

theorem derived65110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2963) ∨ (¬ p 3362) ∨ (¬ p 3568) ∨ (¬ p 3692) ∨ (¬ p 4789) ∨ (¬ p 4902) :=
  ElevenRUP.step65110 (p 2027) (p 2299) (p 2470) (p 2528) (p 2963) (p 3362) (p 3568) (p 3692) (p 4789) (p 4902) (derived40810 p h) (h 40617)

theorem derived65111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 3553) ∨ (¬ p 3631) ∨ (¬ p 3692) ∨ (¬ p 4443) ∨ (¬ p 4902) :=
  ElevenRUP.step65111 (p 2027) (p 3032) (p 3553) (p 3631) (p 3692) (p 4443) (p 4902) (derived40810 p h) (h 40618)

theorem derived65112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2241) ∨ (¬ p 2373) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3362) ∨ (¬ p 3860) ∨ (¬ p 5118) ∨ (¬ p 5693) :=
  ElevenRUP.step65112 (p 2027) (p 2230) (p 2241) (p 2373) (p 2750) (p 2753) (p 3146) (p 3362) (p 3860) (p 5118) (p 5693) (derived40810 p h) (h 40619)

theorem derived65113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2252) ∨ (¬ p 2373) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 3146) ∨ (¬ p 3362) ∨ (¬ p 3568) ∨ (¬ p 4107) ∨ (¬ p 4669) :=
  ElevenRUP.step65113 (p 2027) (p 2230) (p 2252) (p 2373) (p 2750) (p 2753) (p 2963) (p 3146) (p 3362) (p 3568) (p 4107) (p 4669) (derived40810 p h) (h 40620)

theorem derived65114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 3201) ∨ (¬ p 3874) ∨ (¬ p 3941) ∨ (¬ p 5590) :=
  ElevenRUP.step65114 (p 2010) (p 2027) (p 2481) (p 2633) (p 3201) (p 3874) (p 3941) (p 5590) (h 2170) (derived40810 p h) (derived40879 p h) (h 40621)

theorem derived65117 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2952) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3690) ∨ (¬ p 3874) ∨ (¬ p 4320) ∨ (¬ p 4638) ∨ (¬ p 4789) :=
  ElevenRUP.step65117 (p 2027) (p 2470) (p 2952) (p 3333) (p 3362) (p 3690) (p 3874) (p 4320) (p 4638) (p 4789) (derived40810 p h) (h 40624)

theorem derived65118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 5158) ∨ (¬ p 5387) :=
  ElevenRUP.step65118 (p 2010) (p 2027) (p 2611) (p 3201) (p 3276) (p 3355) (p 3362) (p 5158) (p 5387) (h 2170) (derived40810 p h) (derived40877 p h) (h 40625)

theorem derived65120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2449) ∨ (¬ p 2470) ∨ (¬ p 3201) ∨ (¬ p 3362) ∨ (¬ p 3556) ∨ (¬ p 3690) ∨ (¬ p 3874) ∨ (¬ p 4653) :=
  ElevenRUP.step65120 (p 2027) (p 2145) (p 2449) (p 2470) (p 3201) (p 3362) (p 3556) (p 3690) (p 3874) (p 4653) (derived40810 p h) (h 40628)

theorem derived65123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 4118) ∨ (¬ p 4120) ∨ (¬ p 4133) ∨ (¬ p 4311) :=
  ElevenRUP.step65123 (p 2027) (p 2145) (p 2352) (p 2459) (p 2598) (p 3422) (p 4118) (p 4120) (p 4133) (p 4311) (derived40810 p h) (h 40631)

theorem derived65124 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2459) ∨ (¬ p 2573) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 4118) ∨ (¬ p 4120) ∨ (¬ p 4311) ∨ (¬ p 4420) :=
  ElevenRUP.step65124 (p 2027) (p 2145) (p 2459) (p 2573) (p 3362) (p 3584) (p 3641) (p 4118) (p 4120) (p 4311) (p 4420) (derived40810 p h) (h 40632)

theorem derived65125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3422) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4320) ∨ (¬ p 4789) :=
  ElevenRUP.step65125 (p 2027) (p 2352) (p 2598) (p 2952) (p 3422) (p 3570) (p 4133) (p 4320) (p 4789) (derived40810 p h) (h 40633)

theorem derived65126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2553) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3422) ∨ (¬ p 3923) ∨ (¬ p 4366) ∨ (¬ p 4452) ∨ (¬ p 4501) :=
  ElevenRUP.step65126 (p 2027) (p 2241) (p 2553) (p 2598) (p 2750) (p 2753) (p 3422) (p 3923) (p 4366) (p 4452) (p 4501) (derived40810 p h) (h 40634)

theorem derived65127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2573) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3362) ∨ (¬ p 3548) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 4366) ∨ (¬ p 4420) :=
  ElevenRUP.step65127 (p 2027) (p 2241) (p 2573) (p 2750) (p 2753) (p 3362) (p 3548) (p 3584) (p 3641) (p 4366) (p 4420) (derived40810 p h) (h 40635)

theorem derived65129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3641) ∨ (¬ p 3834) ∨ (¬ p 3847) ∨ (¬ p 4149) ∨ (¬ p 5119) ∨ (¬ p 5284) :=
  ElevenRUP.step65129 (p 2027) (p 2241) (p 2598) (p 2750) (p 2753) (p 3641) (p 3834) (p 3847) (p 4149) (p 5119) (p 5284) (derived40810 p h) (h 40637)

theorem derived65133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3641) ∨ (¬ p 3690) ∨ (¬ p 4320) ∨ (¬ p 4669) ∨ (¬ p 4789) :=
  ElevenRUP.step65133 (p 2027) (p 2528) (p 2598) (p 2952) (p 3641) (p 3690) (p 4320) (p 4669) (p 4789) (derived40810 p h) (h 40641)

theorem derived65134 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2761) ∨ (¬ p 3292) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 4621) ∨ (¬ p 4789) ∨ (¬ p 5284) :=
  ElevenRUP.step65134 (p 2027) (p 2598) (p 2761) (p 3292) (p 3422) (p 3564) (p 4621) (p 4789) (p 5284) (derived40810 p h) (h 40642)

theorem derived65135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2573) ∨ (¬ p 3362) ∨ (¬ p 3584) ∨ (¬ p 3641) :=
  ElevenRUP.step65135 (p 1982) (p 2027) (p 2528) (p 2573) (p 2611) (p 3362) (p 3584) (p 3641) (h 2142) (derived40810 p h) (derived40877 p h) (h 40643)

theorem derived65136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3414) ∨ (¬ p 3641) ∨ (¬ p 3947) ∨ (¬ p 4149) ∨ (¬ p 4381) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65136 (p 2027) (p 2598) (p 3414) (p 3641) (p 3947) (p 4149) (p 4381) (p 4789) (p 5119) (derived40810 p h) (h 40644)

theorem derived65138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2241) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4697) :=
  ElevenRUP.step65138 (p 2027) (p 2132) (p 2241) (p 2619) (p 2750) (p 2753) (p 3146) (p 3193) (p 3452) (p 4697) (derived40810 p h) (h 40646)

theorem derived65139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2950) ∨ (¬ p 3449) ∨ (¬ p 3609) ∨ (¬ p 3646) ∨ (¬ p 3954) ∨ (¬ p 3989) ∨ (¬ p 5118) ∨ (¬ p 5315) ∨ (¬ p 5580) :=
  ElevenRUP.step65139 (p 2027) (p 2252) (p 2750) (p 2950) (p 3449) (p 3609) (p 3646) (p 3954) (p 3989) (p 5118) (p 5315) (p 5580) (derived40810 p h) (h 40647)

theorem derived65140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2787) ∨ (¬ p 3641) ∨ (¬ p 4037) ∨ (¬ p 4396) ∨ (¬ p 4669) :=
  ElevenRUP.step65140 (p 2027) (p 2295) (p 2313) (p 2528) (p 2598) (p 2787) (p 3641) (p 4037) (p 4396) (p 4669) (derived40810 p h) (h 40648)

theorem derived65141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2761) ∨ (¬ p 4286) ∨ (¬ p 4669) ∨ (¬ p 5117) :=
  ElevenRUP.step65141 (p 2027) (p 2528) (p 2761) (p 4286) (p 4669) (p 5117) (derived40810 p h) (h 40649)

theorem derived65142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 2449) ∨ (¬ p 2860) ∨ (¬ p 3553) ∨ (¬ p 3821) ∨ (¬ p 4133) ∨ (¬ p 5260) :=
  ElevenRUP.step65142 (p 2027) (p 2132) (p 2187) (p 2449) (p 2860) (p 3553) (p 3821) (p 4133) (p 5260) (derived40810 p h) (h 40650)

theorem derived65143 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 4381) :=
  ElevenRUP.step65143 (p 1983) (p 2027) (p 2997) (p 3097) (p 3125) (p 3461) (p 4381) (h 2143) (derived40810 p h) (derived40890 p h) (h 40652)

theorem derived65144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2952) ∨ (¬ p 3516) ∨ (¬ p 3744) ∨ (¬ p 3819) ∨ (¬ p 3952) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 4789) :=
  ElevenRUP.step65144 (p 2027) (p 2761) (p 2952) (p 3516) (p 3744) (p 3819) (p 3952) (p 4444) (p 4604) (p 4789) (derived40810 p h) (h 40653)

theorem derived65148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2753) ∨ (¬ p 2901) ∨ (¬ p 3362) ∨ (¬ p 3497) ∨ (¬ p 3556) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 3645) ∨ (¬ p 4158) ∨ (¬ p 4877) :=
  ElevenRUP.step65148 (p 2027) (p 2573) (p 2753) (p 2901) (p 3362) (p 3497) (p 3556) (p 3584) (p 3641) (p 3645) (p 4158) (p 4877) (derived40810 p h) (h 40657)

theorem derived65149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2901) ∨ (¬ p 2950) ∨ (¬ p 3422) ∨ (¬ p 3556) ∨ (¬ p 3564) ∨ (¬ p 4208) ∨ (¬ p 4368) ∨ (¬ p 4789) :=
  ElevenRUP.step65149 (p 2027) (p 2598) (p 2901) (p 2950) (p 3422) (p 3556) (p 3564) (p 4208) (p 4368) (p 4789) (derived40810 p h) (h 40658)

theorem derived65150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2901) ∨ (¬ p 3556) ∨ (¬ p 3641) ∨ (¬ p 4208) ∨ (¬ p 5059) :=
  ElevenRUP.step65150 (p 2027) (p 2145) (p 2528) (p 2598) (p 2901) (p 3556) (p 3641) (p 4208) (p 5059) (derived40810 p h) (h 40659)

theorem derived65151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3548) ∨ (¬ p 3609) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4366) :=
  ElevenRUP.step65151 (p 2027) (p 2098) (p 2241) (p 2750) (p 2753) (p 3548) (p 3609) (p 4133) (p 4347) (p 4366) (derived40810 p h) (h 40660)

theorem derived65153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3549) ∨ (¬ p 3954) ∨ (¬ p 4870) ∨ (¬ p 5020) :=
  ElevenRUP.step65153 (p 2027) (p 2307) (p 3549) (p 3954) (p 4870) (p 5020) (derived40810 p h) (h 40663)

theorem derived65154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2299) ∨ (¬ p 2963) ∨ (¬ p 3362) ∨ (¬ p 3568) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 4420) ∨ (¬ p 4789) :=
  ElevenRUP.step65154 (p 2027) (p 2230) (p 2299) (p 2963) (p 3362) (p 3568) (p 3641) (p 3684) (p 4420) (p 4789) (derived40810 p h) (h 40664)

theorem derived65155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2753) ∨ (¬ p 3204) ∨ (¬ p 3324) ∨ (¬ p 3362) ∨ (¬ p 3692) ∨ (¬ p 4433) ∨ (¬ p 4870) :=
  ElevenRUP.step65155 (p 2027) (p 2295) (p 2313) (p 2470) (p 2528) (p 2753) (p 3204) (p 3324) (p 3362) (p 3692) (p 4433) (p 4870) (derived40810 p h) (h 40665)

theorem derived65157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 2952) ∨ (¬ p 3471) ∨ (¬ p 3744) ∨ (¬ p 3952) ∨ (¬ p 4604) ∨ (¬ p 4789) :=
  ElevenRUP.step65157 (p 2027) (p 2459) (p 2717) (p 2952) (p 3471) (p 3744) (p 3952) (p 4604) (p 4789) (derived40810 p h) (h 40667)

theorem derived65160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 3690) ∨ (¬ p 3954) ∨ (¬ p 4181) ∨ (¬ p 4381) ∨ (¬ p 4877) ∨ (¬ p 5119) :=
  ElevenRUP.step65160 (p 2027) (p 3449) (p 3556) (p 3645) (p 3690) (p 3954) (p 4181) (p 4381) (p 4877) (p 5119) (derived40810 p h) (h 40670)

theorem derived65161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4695) ∨ (¬ p 5118) :=
  ElevenRUP.step65161 (p 2027) (p 3333) (p 3874) (p 4286) (p 4695) (p 5118) (derived40810 p h) (h 40671)

theorem derived65162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2787) ∨ (¬ p 3324) ∨ (¬ p 3362) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 4596) :=
  ElevenRUP.step65162 (p 2027) (p 2230) (p 2295) (p 2313) (p 2787) (p 3324) (p 3362) (p 3641) (p 3684) (p 4596) (derived40810 p h) (h 40672)

theorem derived65164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2373) ∨ (¬ p 2598) ∨ (¬ p 2787) ∨ (¬ p 2850) ∨ (¬ p 3324) ∨ (¬ p 4433) :=
  ElevenRUP.step65164 (p 2027) (p 2295) (p 2313) (p 2373) (p 2598) (p 2787) (p 2850) (p 3324) (p 4433) (derived40810 p h) (h 40674)

theorem derived65165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 3553) ∨ (¬ p 3556) ∨ (¬ p 4333) :=
  ElevenRUP.step65165 (p 1990) (p 2027) (p 2156) (p 2177) (p 2997) (p 3553) (p 3556) (p 4333) (h 2150) (derived40810 p h) (derived40890 p h) (h 40676)

theorem derived65167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3641) ∨ (¬ p 4149) ∨ (¬ p 4208) ∨ (¬ p 4322) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65167 (p 2027) (p 2598) (p 2952) (p 3641) (p 4149) (p 4208) (p 4322) (p 4789) (p 5119) (derived40810 p h) (h 40678)

theorem derived65168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3452) ∨ (¬ p 3644) ∨ (¬ p 3742) ∨ (¬ p 4116) :=
  ElevenRUP.step65168 (p 1977) (p 2027) (p 2241) (p 2633) (p 3452) (p 3644) (p 3742) (p 4116) (h 2137) (derived40810 p h) (derived40879 p h) (h 40679)

theorem derived65171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3414) ∨ (¬ p 3422) ∨ (¬ p 3888) ∨ (¬ p 3947) ∨ (¬ p 4381) ∨ (¬ p 4789) ∨ (¬ p 5250) :=
  ElevenRUP.step65171 (p 2027) (p 2598) (p 3414) (p 3422) (p 3888) (p 3947) (p 4381) (p 4789) (p 5250) (derived40810 p h) (h 40682)

theorem derived65172 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 3544) ∨ (¬ p 4261) ∨ (¬ p 4366) :=
  ElevenRUP.step65172 (p 1977) (p 2027) (p 2241) (p 2459) (p 2633) (p 3544) (p 4261) (p 4366) (h 2137) (derived40810 p h) (derived40879 p h) (h 40683)

theorem derived65176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2963) ∨ (¬ p 3073) ∨ (¬ p 3324) ∨ (¬ p 3449) ∨ (¬ p 3954) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step65176 (p 2027) (p 2252) (p 2750) (p 2963) (p 3073) (p 3324) (p 3449) (p 3954) (p 5118) (p 5580) (derived40810 p h) (h 40687)

theorem derived65177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2901) ∨ (¬ p 2950) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3556) ∨ (¬ p 3954) ∨ (¬ p 4208) ∨ (¬ p 5059) :=
  ElevenRUP.step65177 (p 2027) (p 2252) (p 2750) (p 2901) (p 2950) (p 3073) (p 3449) (p 3556) (p 3954) (p 4208) (p 5059) (derived40810 p h) (h 40688)

theorem derived65182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2470) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3817) ∨ (¬ p 3874) ∨ (¬ p 4366) ∨ (¬ p 4638) :=
  ElevenRUP.step65182 (p 2027) (p 2241) (p 2470) (p 2750) (p 2753) (p 3333) (p 3362) (p 3817) (p 3874) (p 4366) (p 4638) (derived40810 p h) (h 40693)

theorem derived65190 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2952) ∨ (¬ p 3979) ∨ (¬ p 4208) ∨ (¬ p 4322) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65190 (p 2027) (p 2774) (p 2819) (p 2952) (p 3979) (p 4208) (p 4322) (p 4789) (p 5119) (derived40810 p h) (h 40701)

theorem derived65192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2553) ∨ (¬ p 3573) ∨ (¬ p 3998) ∨ (¬ p 4170) ∨ (¬ p 4286) :=
  ElevenRUP.step65192 (p 1975) (p 2027) (p 2187) (p 2553) (p 2765) (p 3573) (p 3998) (p 4170) (p 4286) (h 2135) (derived40810 p h) (derived40883 p h) (h 40703)

theorem derived65194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2373) ∨ (¬ p 2459) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2850) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4902) :=
  ElevenRUP.step65194 (p 2027) (p 2252) (p 2373) (p 2459) (p 2598) (p 2750) (p 2753) (p 2850) (p 3172) (p 4118) (p 4902) (derived40810 p h) (h 40705)

theorem derived65195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3744) ∨ (¬ p 3952) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 4789) :=
  ElevenRUP.step65195 (p 2027) (p 2952) (p 3276) (p 3355) (p 3362) (p 3744) (p 3952) (p 4444) (p 4604) (p 4789) (derived40810 p h) (h 40706)

theorem derived65198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2363) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4669) :=
  ElevenRUP.step65198 (p 2027) (p 2241) (p 2363) (p 2750) (p 2753) (p 2774) (p 2819) (p 3817) (p 4366) (p 4669) (derived40810 p h) (h 40709)

theorem derived65199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3204) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3874) ∨ (¬ p 3946) ∨ (¬ p 4191) ∨ (¬ p 4638) ∨ (¬ p 4870) :=
  ElevenRUP.step65199 (p 2027) (p 2470) (p 2753) (p 2761) (p 3204) (p 3333) (p 3362) (p 3874) (p 3946) (p 4191) (p 4638) (p 4870) (derived40810 p h) (h 40711)

theorem derived65203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3204) ∨ (¬ p 4037) ∨ (¬ p 4604) ∨ (¬ p 4870) :=
  ElevenRUP.step65203 (p 2027) (p 2132) (p 2295) (p 2313) (p 2619) (p 2753) (p 3146) (p 3204) (p 4037) (p 4604) (p 4870) (derived40810 p h) (h 40715)

theorem derived65207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2952) ∨ (¬ p 3362) ∨ (¬ p 3570) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 4320) ∨ (¬ p 4420) ∨ (¬ p 4789) :=
  ElevenRUP.step65207 (p 2027) (p 2573) (p 2952) (p 3362) (p 3570) (p 3584) (p 3641) (p 4320) (p 4420) (p 4789) (derived40810 p h) (h 40719)

theorem derived65209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2312) ∨ (¬ p 3324) ∨ (¬ p 3516) ∨ (¬ p 4138) ∨ (¬ p 4668) :=
  ElevenRUP.step65209 (p 2027) (p 2295) (p 2312) (p 3324) (p 3516) (p 4138) (p 4668) (derived40810 p h) (h 40722)

theorem derived65210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2553) ∨ (¬ p 3573) ∨ (¬ p 3979) ∨ (¬ p 4286) :=
  ElevenRUP.step65210 (p 1975) (p 2027) (p 2187) (p 2553) (p 2765) (p 3573) (p 3979) (p 4286) (h 2135) (derived40810 p h) (derived40883 p h) (h 40723)

end ElevenLogic
