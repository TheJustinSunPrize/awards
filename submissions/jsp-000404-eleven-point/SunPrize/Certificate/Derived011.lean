import SunPrize.Certificate.Derived010
import SunPrize.Certificate.Logic011
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived50110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2396) ∨ (¬ p 2881) ∨ (¬ p 4277) ∨ (¬ p 4278) :=
  ElevenRUP.step50110 (p 2027) (p 2299) (p 2396) (p 2881) (p 4277) (p 4278) (derived40810 p h) (h 22955)

theorem derived50111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3880) ∨ (¬ p 3998) ∨ (¬ p 4238) ∨ (¬ p 4539) ∨ (¬ p 5568) :=
  ElevenRUP.step50111 (p 2027) (p 3880) (p 3998) (p 4238) (p 4539) (p 5568) (derived40810 p h) (h 22960)

theorem derived50112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3551) ∨ (¬ p 3580) ∨ (¬ p 3876) ∨ (¬ p 4279) ∨ (¬ p 4750) :=
  ElevenRUP.step50112 (p 2027) (p 2264) (p 3551) (p 3580) (p 3876) (p 4279) (p 4750) (derived40810 p h) (h 22961)

theorem derived50113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2839) ∨ (¬ p 2952) ∨ (¬ p 4787) ∨ (¬ p 5051) :=
  ElevenRUP.step50113 (p 2027) (p 2743) (p 2839) (p 2952) (p 4787) (p 5051) (derived40810 p h) (h 22962)

theorem derived50114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3684) ∨ (¬ p 4111) ∨ (¬ p 4241) ∨ (¬ p 4750) :=
  ElevenRUP.step50114 (p 2027) (p 2992) (p 3684) (p 4111) (p 4241) (p 4750) (derived40810 p h) (h 22963)

theorem derived50115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4668) ∨ (¬ p 4733) :=
  ElevenRUP.step50115 (p 2027) (p 2417) (p 2598) (p 3201) (p 3486) (p 3555) (p 3570) (p 4668) (p 4733) (derived40810 p h) (h 22964)

theorem derived50116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2417) ∨ (¬ p 3367) ∨ (¬ p 3389) ∨ (¬ p 3486) ∨ (¬ p 3570) ∨ (¬ p 3759) ∨ (¬ p 4243) ∨ (¬ p 4668) ∨ (¬ p 4734) :=
  ElevenRUP.step50116 (p 2027) (p 2138) (p 2417) (p 3367) (p 3389) (p 3486) (p 3570) (p 3759) (p 4243) (p 4668) (p 4734) (derived40810 p h) (h 22965)

theorem derived50117 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3555) ∨ (¬ p 3641) ∨ (¬ p 3744) ∨ (¬ p 4173) ∨ (¬ p 4604) ∨ (¬ p 4733) :=
  ElevenRUP.step50117 (p 2027) (p 2528) (p 2598) (p 3555) (p 3641) (p 3744) (p 4173) (p 4604) (p 4733) (derived40810 p h) (h 22966)

theorem derived50118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2298) ∨ (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 3323) ∨ (¬ p 4624) :=
  ElevenRUP.step50118 (p 2027) (p 2298) (p 2641) (p 2996) (p 3323) (p 4624) (derived40810 p h) (h 22967)

theorem derived50119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2934) ∨ (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 3876) ∨ (¬ p 4279) ∨ (¬ p 5217) :=
  ElevenRUP.step50119 (p 2027) (p 2934) (p 3527) (p 3551) (p 3876) (p 4279) (p 5217) (derived40810 p h) (h 22968)

theorem derived50120 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3876) ∨ (¬ p 4066) ∨ (¬ p 4111) ∨ (¬ p 4279) ∨ (¬ p 4750) :=
  ElevenRUP.step50120 (p 2027) (p 3027) (p 3876) (p 4066) (p 4111) (p 4279) (p 4750) (derived40810 p h) (h 22969)

theorem derived50121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 4733) :=
  ElevenRUP.step50121 (p 2027) (p 2191) (p 2417) (p 2598) (p 3201) (p 3555) (p 3692) (p 3950) (p 4733) (derived40810 p h) (h 22970)

theorem derived50125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2598) ∨ (¬ p 3097) ∨ (¬ p 3422) ∨ (¬ p 3555) ∨ (¬ p 4173) ∨ (¬ p 4405) ∨ (¬ p 4733) :=
  ElevenRUP.step50125 (p 2027) (p 2352) (p 2598) (p 3097) (p 3422) (p 3555) (p 4173) (p 4405) (p 4733) (derived40810 p h) (h 22974)

theorem derived50128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3156) ∨ (¬ p 3745) ∨ (¬ p 4154) ∨ (¬ p 4509) :=
  ElevenRUP.step50128 (p 2027) (p 2992) (p 3156) (p 3745) (p 4154) (p 4509) (derived40810 p h) (h 22978)

theorem derived50130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3309) ∨ (¬ p 3822) ∨ (¬ p 4193) ∨ (¬ p 4734) ∨ (¬ p 4869) :=
  ElevenRUP.step50130 (p 2027) (p 2138) (p 3309) (p 3822) (p 4193) (p 4734) (p 4869) (derived40810 p h) (h 22982)

theorem derived50131 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 3097) ∨ (¬ p 3367) ∨ (¬ p 3758) ∨ (¬ p 3759) ∨ (¬ p 4405) ∨ (¬ p 4734) :=
  ElevenRUP.step50131 (p 2027) (p 2138) (p 2352) (p 2573) (p 3097) (p 3367) (p 3758) (p 3759) (p 4405) (p 4734) (derived40810 p h) (h 22983)

theorem derived50136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2192) ∨ (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3369) ∨ (¬ p 3646) ∨ (¬ p 4733) ∨ (¬ p 4905) :=
  ElevenRUP.step50136 (p 2027) (p 2191) (p 2192) (p 2598) (p 2911) (p 3201) (p 3369) (p 3646) (p 4733) (p 4905) (derived40810 p h) (h 22991)

theorem derived50137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3413) ∨ (¬ p 3684) ∨ (¬ p 4031) ∨ (¬ p 4120) ∨ (¬ p 4750) :=
  ElevenRUP.step50137 (p 2027) (p 3156) (p 3413) (p 3684) (p 4031) (p 4120) (p 4750) (derived40810 p h) (h 22994)

theorem derived50138 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3952) ∨ (¬ p 4237) ∨ (¬ p 4509) :=
  ElevenRUP.step50138 (p 2027) (p 3256) (p 3692) (p 3952) (p 4237) (p 4509) (derived40810 p h) (h 22995)

theorem derived50139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3570) ∨ (¬ p 4320) ∨ (¬ p 4431) ∨ (¬ p 4960) :=
  ElevenRUP.step50139 (p 2027) (p 3527) (p 3570) (p 4320) (p 4431) (p 4960) (derived40810 p h) (h 22997)

theorem derived50140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2797) ∨ (¬ p 2807) ∨ (¬ p 3572) ∨ (¬ p 4975) :=
  ElevenRUP.step50140 (p 2027) (p 2657) (p 2797) (p 2807) (p 3572) (p 4975) (derived40810 p h) (h 22998)

theorem derived50141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 4349) ∨ (¬ p 5063) ∨ (¬ p 5284) :=
  ElevenRUP.step50141 (p 2027) (p 3146) (p 3266) (p 4349) (p 5063) (p 5284) (derived40810 p h) (h 22999)

theorem derived50145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2657) ∨ (¬ p 2946) ∨ (¬ p 3487) ∨ (¬ p 4241) ∨ (¬ p 4715) :=
  ElevenRUP.step50145 (p 2027) (p 2499) (p 2657) (p 2946) (p 3487) (p 4241) (p 4715) (derived40810 p h) (h 23005)

theorem derived50146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 3988) ∨ (¬ p 4244) ∨ (¬ p 4555) ∨ (¬ p 4744) :=
  ElevenRUP.step50146 (p 2027) (p 3609) (p 3692) (p 3988) (p 4244) (p 4555) (p 4744) (derived40810 p h) (h 23006)

theorem derived50147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2396) ∨ (¬ p 4118) ∨ (¬ p 4443) ∨ (¬ p 4550) :=
  ElevenRUP.step50147 (p 2027) (p 2299) (p 2396) (p 4118) (p 4443) (p 4550) (derived40810 p h) (h 23008)

theorem derived50148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2952) ∨ (¬ p 3497) ∨ (¬ p 3986) ∨ (¬ p 4507) :=
  ElevenRUP.step50148 (p 2027) (p 2331) (p 2952) (p 3497) (p 3986) (p 4507) (derived40810 p h) (h 23009)

theorem derived50149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3574) ∨ (¬ p 3662) ∨ (¬ p 4281) ∨ (¬ p 4701) :=
  ElevenRUP.step50149 (p 2027) (p 2493) (p 3574) (p 3662) (p 4281) (p 4701) (derived40810 p h) (h 23010)

theorem derived50150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2579) ∨ (¬ p 3189) ∨ (¬ p 3956) ∨ (¬ p 4009) ∨ (¬ p 4347) ∨ (¬ p 5122) ∨ (¬ p 5193) :=
  ElevenRUP.step50150 (p 2027) (p 2241) (p 2579) (p 3189) (p 3956) (p 4009) (p 4347) (p 5122) (p 5193) (derived40810 p h) (h 23011)

theorem derived50151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 3646) ∨ (¬ p 3684) ∨ (¬ p 4203) ∨ (¬ p 4533) :=
  ElevenRUP.step50151 (p 2027) (p 3422) (p 3646) (p 3684) (p 4203) (p 4533) (derived40810 p h) (h 23012)

theorem derived50152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2901) ∨ (¬ p 3497) ∨ (¬ p 4132) ∨ (¬ p 4556) :=
  ElevenRUP.step50152 (p 2027) (p 2177) (p 2901) (p 3497) (p 4132) (p 4556) (derived40810 p h) (h 23013)

theorem derived50153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2396) ∨ (¬ p 2901) ∨ (¬ p 2992) ∨ (¬ p 3540) ∨ (¬ p 4278) ∨ (¬ p 4556) ∨ (¬ p 5193) :=
  ElevenRUP.step50153 (p 2027) (p 2241) (p 2396) (p 2901) (p 2992) (p 3540) (p 4278) (p 4556) (p 5193) (derived40810 p h) (h 23015)

theorem derived50154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2427) ∨ (¬ p 3880) ∨ (¬ p 4132) ∨ (¬ p 4556) :=
  ElevenRUP.step50154 (p 2027) (p 2177) (p 2427) (p 3880) (p 4132) (p 4556) (derived40810 p h) (h 23016)

theorem derived50155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3051) ∨ (¬ p 3551) ∨ (¬ p 4556) ∨ (¬ p 4984) :=
  ElevenRUP.step50155 (p 2027) (p 2177) (p 3051) (p 3551) (p 4556) (p 4984) (derived40810 p h) (h 23018)

theorem derived50156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2396) ∨ (¬ p 3692) ∨ (¬ p 4443) ∨ (¬ p 4902) :=
  ElevenRUP.step50156 (p 2027) (p 2299) (p 2396) (p 3692) (p 4443) (p 4902) (derived40810 p h) (h 23021)

theorem derived50157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 3570) ∨ (¬ p 3821) ∨ (¬ p 4556) :=
  ElevenRUP.step50157 (p 2027) (p 2341) (p 2396) (p 3570) (p 3821) (p 4556) (derived40810 p h) (h 23022)

theorem derived50160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2934) ∨ (¬ p 3631) ∨ (¬ p 3742) ∨ (¬ p 3821) ∨ (¬ p 4279) ∨ (¬ p 4814) :=
  ElevenRUP.step50160 (p 2027) (p 2934) (p 3631) (p 3742) (p 3821) (p 4279) (p 4814) (derived40810 p h) (h 23025)

theorem derived50161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2192) ∨ (¬ p 2743) ∨ (¬ p 3371) ∨ (¬ p 3646) ∨ (¬ p 5052) :=
  ElevenRUP.step50161 (p 2027) (p 2143) (p 2192) (p 2743) (p 3371) (p 3646) (p 5052) (derived40810 p h) (h 23026)

theorem derived50165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4793) ∨ (¬ p 5206) :=
  ElevenRUP.step50165 (p 2027) (p 2608) (p 3631) (p 3821) (p 4793) (p 5206) (derived40810 p h) (h 23030)

theorem derived50168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2608) ∨ (¬ p 2742) ∨ (¬ p 2839) ∨ (¬ p 5052) :=
  ElevenRUP.step50168 (p 2027) (p 2247) (p 2608) (p 2742) (p 2839) (p 5052) (derived40810 p h) (h 23035)

theorem derived50169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 2717) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 3587) :=
  ElevenRUP.step50169 (p 2027) (p 2140) (p 2717) (p 3556) (p 3570) (p 3587) (derived40810 p h) (h 23036)

theorem derived50170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2891) ∨ (¬ p 3371) ∨ (¬ p 3556) ∨ (¬ p 3585) ∨ (¬ p 4884) :=
  ElevenRUP.step50170 (p 2027) (p 2143) (p 2891) (p 3371) (p 3556) (p 3585) (p 4884) (derived40810 p h) (h 23037)

theorem derived50171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3506) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3830) ∨ (¬ p 3853) ∨ (¬ p 3989) ∨ (¬ p 4959) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step50171 (p 2027) (p 2247) (p 3506) (p 3645) (p 3646) (p 3830) (p 3853) (p 3989) (p 4959) (p 5123) (p 5580) (derived40810 p h) (h 23038)

theorem derived50173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3105) ∨ (¬ p 3694) ∨ (¬ p 4132) ∨ (¬ p 4402) ∨ (¬ p 4556) :=
  ElevenRUP.step50173 (p 2027) (p 2177) (p 3105) (p 3694) (p 4132) (p 4402) (p 4556) (derived40810 p h) (h 23040)

theorem derived50174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3073) ∨ (¬ p 3742) ∨ (¬ p 4186) ∨ (¬ p 4688) ∨ (¬ p 4814) :=
  ElevenRUP.step50174 (p 2027) (p 2534) (p 3073) (p 3742) (p 4186) (p 4688) (p 4814) (derived40810 p h) (h 23041)

theorem derived50175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2440) ∨ (¬ p 3646) ∨ (¬ p 3948) ∨ (¬ p 4031) ∨ (¬ p 4814) :=
  ElevenRUP.step50175 (p 2027) (p 2192) (p 2440) (p 3646) (p 3948) (p 4031) (p 4814) (derived40810 p h) (h 23042)

theorem derived50176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3873) ∨ (¬ p 4877) :=
  ElevenRUP.step50176 (p 2027) (p 2210) (p 2737) (p 3365) (p 3873) (p 4877) (derived40810 p h) (h 23044)

theorem derived50177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3399) ∨ (¬ p 3873) ∨ (¬ p 4796) :=
  ElevenRUP.step50177 (p 2027) (p 2737) (p 3365) (p 3399) (p 3873) (p 4796) (derived40810 p h) (h 23045)

theorem derived50178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 3093) ∨ (¬ p 3555) ∨ (¬ p 4507) ∨ (¬ p 4516) :=
  ElevenRUP.step50178 (p 2027) (p 2191) (p 3093) (p 3555) (p 4507) (p 4516) (derived40810 p h) (h 23046)

theorem derived50182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2749) ∨ (¬ p 3859) ∨ (¬ p 4181) ∨ (¬ p 4416) ∨ (¬ p 4877) ∨ (¬ p 5590) :=
  ElevenRUP.step50182 (p 2027) (p 2210) (p 2749) (p 3859) (p 4181) (p 4416) (p 4877) (p 5590) (derived40810 p h) (h 23051)

theorem derived50183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2311) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4356) ∨ (¬ p 4431) ∨ (¬ p 4507) :=
  ElevenRUP.step50183 (p 2027) (p 2191) (p 2311) (p 3631) (p 3821) (p 4356) (p 4431) (p 4507) (derived40810 p h) (h 23053)

theorem derived50184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 3821) ∨ (¬ p 4877) ∨ (¬ p 5206) :=
  ElevenRUP.step50184 (p 2027) (p 2210) (p 3631) (p 3687) (p 3821) (p 4877) (p 5206) (derived40810 p h) (h 23054)

theorem derived50185 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2387) ∨ (¬ p 2396) ∨ (¬ p 3581) ∨ (¬ p 4278) :=
  ElevenRUP.step50185 (p 2003) (p 2027) (p 2352) (p 2387) (p 2396) (p 2997) (p 3581) (p 4278) (h 2163) (derived40810 p h) (derived40890 p h) (h 23055)

theorem derived50189 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3540) ∨ (¬ p 4009) ∨ (¬ p 4278) ∨ (¬ p 4381) ∨ (¬ p 4729) ∨ (¬ p 5119) :=
  ElevenRUP.step50189 (p 2027) (p 2696) (p 3005) (p 3540) (p 4009) (p 4278) (p 4381) (p 4729) (p 5119) (derived40810 p h) (h 23059)

theorem derived50191 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3954) ∨ (¬ p 3989) ∨ (¬ p 4877) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step50191 (p 2027) (p 3073) (p 3449) (p 3645) (p 3646) (p 3954) (p 3989) (p 4877) (p 5118) (p 5580) (derived40810 p h) (h 23066)

theorem derived50194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3093) ∨ (¬ p 3555) ∨ (¬ p 3922) ∨ (¬ p 4195) :=
  ElevenRUP.step50194 (p 1994) (p 2027) (p 2630) (p 2873) (p 3093) (p 3555) (p 3922) (p 4195) (h 2154) (derived40810 p h) (derived40886 p h) (h 23070)

theorem derived50195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 3947) ∨ (¬ p 3986) ∨ (¬ p 4067) ∨ (¬ p 4120) ∨ (¬ p 4507) ∨ (¬ p 4988) :=
  ElevenRUP.step50195 (p 2027) (p 3516) (p 3947) (p 3986) (p 4067) (p 4120) (p 4507) (p 4988) (derived40810 p h) (h 23073)

theorem derived50196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3680) ∨ (¬ p 4314) ∨ (¬ p 5043) ∨ (¬ p 5284) :=
  ElevenRUP.step50196 (p 2027) (p 2284) (p 3680) (p 4314) (p 5043) (p 5284) (derived40810 p h) (h 23076)

theorem derived50197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2264) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3027) ∨ (¬ p 3556) ∨ (¬ p 3583) ∨ (¬ p 3690) ∨ (¬ p 4666) ∨ (¬ p 4737) :=
  ElevenRUP.step50197 (p 2027) (p 2143) (p 2264) (p 2696) (p 2742) (p 3027) (p 3556) (p 3583) (p 3690) (p 4666) (p 4737) (derived40810 p h) (h 23077)

theorem derived50198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2307) ∨ (¬ p 2962) ∨ (¬ p 3688) ∨ (¬ p 3822) ∨ (¬ p 4737) :=
  ElevenRUP.step50198 (p 2027) (p 2144) (p 2307) (p 2962) (p 3688) (p 3822) (p 4737) (derived40810 p h) (h 23078)

theorem derived50202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3323) ∨ (¬ p 3551) ∨ (¬ p 3588) ∨ (¬ p 3959) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4737) :=
  ElevenRUP.step50202 (p 2027) (p 2641) (p 2696) (p 2742) (p 3323) (p 3551) (p 3588) (p 3959) (p 4330) (p 4348) (p 4737) (derived40810 p h) (h 23082)

theorem derived50204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3588) ∨ (¬ p 3857) ∨ (¬ p 3959) ∨ (¬ p 3961) ∨ (¬ p 4133) ∨ (¬ p 4737) :=
  ElevenRUP.step50204 (p 2027) (p 2459) (p 2641) (p 2668) (p 2696) (p 2742) (p 3588) (p 3857) (p 3959) (p 3961) (p 4133) (p 4737) (derived40810 p h) (h 23086)

theorem derived50205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2427) ∨ (¬ p 2542) ∨ (¬ p 2727) ∨ (¬ p 4204) :=
  ElevenRUP.step50205 (p 1990) (p 2027) (p 2241) (p 2427) (p 2542) (p 2699) (p 2727) (p 4204) (h 2150) (derived40810 p h) (derived40881 p h) (h 23087)

theorem derived50206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2785) ∨ (¬ p 3590) ∨ (¬ p 3688) ∨ (¬ p 4107) ∨ (¬ p 4669) ∨ (¬ p 4737) :=
  ElevenRUP.step50206 (p 2027) (p 2313) (p 2518) (p 2528) (p 2598) (p 2785) (p 3590) (p 3688) (p 4107) (p 4669) (p 4737) (derived40810 p h) (h 23088)

theorem derived50208 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 2785) ∨ (¬ p 2992) ∨ (¬ p 3156) ∨ (¬ p 3688) ∨ (¬ p 4737) ∨ (¬ p 4902) :=
  ElevenRUP.step50208 (p 2027) (p 2299) (p 2313) (p 2696) (p 2742) (p 2785) (p 2992) (p 3156) (p 3688) (p 4737) (p 4902) (derived40810 p h) (h 23090)

theorem derived50209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2311) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 2785) ∨ (¬ p 2901) ∨ (¬ p 2992) ∨ (¬ p 3551) ∨ (¬ p 3688) ∨ (¬ p 4556) ∨ (¬ p 4737) :=
  ElevenRUP.step50209 (p 2027) (p 2177) (p 2311) (p 2696) (p 2742) (p 2785) (p 2901) (p 2992) (p 3551) (p 3688) (p 4556) (p 4737) (derived40810 p h) (h 23091)

theorem derived50211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 2901) ∨ (¬ p 2911) ∨ (¬ p 2992) ∨ (¬ p 3363) ∨ (¬ p 3551) ∨ (¬ p 3585) ∨ (¬ p 4647) ∨ (¬ p 4737) ∨ (¬ p 5197) :=
  ElevenRUP.step50211 (p 2027) (p 2696) (p 2742) (p 2901) (p 2911) (p 2992) (p 3363) (p 3551) (p 3585) (p 4647) (p 4737) (p 5197) (derived40810 p h) (h 23093)

theorem derived50214 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 2819) ∨ (¬ p 3923) ∨ (¬ p 3953) ∨ (¬ p 4476) :=
  ElevenRUP.step50214 (p 2027) (p 2707) (p 2819) (p 3923) (p 3953) (p 4476) (derived40810 p h) (h 23096)

theorem derived50215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3389) ∨ (¬ p 3585) ∨ (¬ p 3876) :=
  ElevenRUP.step50215 (p 1992) (p 2027) (p 2579) (p 3008) (p 3389) (p 3585) (p 3876) (h 2152) (derived40810 p h) (derived40891 p h) (h 23098)

theorem derived50217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2657) ∨ (¬ p 3553) ∨ (¬ p 4067) ∨ (¬ p 4104) ∨ (¬ p 4975) :=
  ElevenRUP.step50217 (p 2027) (p 2341) (p 2657) (p 3553) (p 4067) (p 4104) (p 4975) (derived40810 p h) (h 23100)

theorem derived50218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 2992) ∨ (¬ p 3156) ∨ (¬ p 3363) ∨ (¬ p 3540) ∨ (¬ p 3585) ∨ (¬ p 3644) ∨ (¬ p 4737) ∨ (¬ p 4902) :=
  ElevenRUP.step50218 (p 2027) (p 2696) (p 2742) (p 2992) (p 3156) (p 3363) (p 3540) (p 3585) (p 3644) (p 4737) (p 4902) (derived40810 p h) (h 23102)

theorem derived50220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3707) ∨ (¬ p 3773) ∨ (¬ p 5329) ∨ (¬ p 5486) :=
  ElevenRUP.step50220 (p 2027) (p 2608) (p 3707) (p 3773) (p 5329) (p 5486) (derived40810 p h) (h 23104)

theorem derived50221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2563) ∨ (¬ p 3146) ∨ (¬ p 4507) ∨ (¬ p 4607) :=
  ElevenRUP.step50221 (p 2027) (p 2534) (p 2563) (p 3146) (p 4507) (p 4607) (derived40810 p h) (h 23105)

theorem derived50224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3367) ∨ (¬ p 3422) ∨ (¬ p 3905) ∨ (¬ p 4734) :=
  ElevenRUP.step50224 (p 2027) (p 2579) (p 3367) (p 3422) (p 3905) (p 4734) (derived40810 p h) (h 23109)

theorem derived50225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2663) ∨ (¬ p 2952) ∨ (¬ p 3389) ∨ (¬ p 3742) ∨ (¬ p 4701) :=
  ElevenRUP.step50225 (p 2027) (p 2663) (p 2952) (p 3389) (p 3742) (p 4701) (derived40810 p h) (h 23110)

theorem derived50226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2743) ∨ (¬ p 2829) ∨ (¬ p 3361) ∨ (¬ p 4328) ∨ (¬ p 4975) :=
  ElevenRUP.step50226 (p 2027) (p 2657) (p 2743) (p 2829) (p 3361) (p 4328) (p 4975) (derived40810 p h) (h 23111)

theorem derived50227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 2598) ∨ (¬ p 2785) ∨ (¬ p 3590) ∨ (¬ p 3688) ∨ (¬ p 4737) ∨ (¬ p 4902) :=
  ElevenRUP.step50227 (p 2027) (p 2299) (p 2313) (p 2373) (p 2406) (p 2598) (p 2785) (p 3590) (p 3688) (p 4737) (p 4902) (derived40810 p h) (h 23112)

theorem derived50228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2667) ∨ (¬ p 2727) ∨ (¬ p 2952) ∨ (¬ p 3987) ∨ (¬ p 4154) ∨ (¬ p 4701) :=
  ElevenRUP.step50228 (p 2027) (p 2667) (p 2727) (p 2952) (p 3987) (p 4154) (p 4701) (derived40810 p h) (h 23113)

theorem derived50229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3016) ∨ (¬ p 4203) ∨ (¬ p 4948) ∨ (¬ p 5043) :=
  ElevenRUP.step50229 (p 2027) (p 2440) (p 3016) (p 4203) (p 4948) (p 5043) (derived40810 p h) (h 23114)

theorem derived50230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2995) ∨ (¬ p 3497) ∨ (¬ p 3581) ∨ (¬ p 4203) ∨ (¬ p 4278) ∨ (¬ p 4507) :=
  ElevenRUP.step50230 (p 2027) (p 2449) (p 2995) (p 3497) (p 3581) (p 4203) (p 4278) (p 4507) (derived40810 p h) (h 23116)

theorem derived50231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2630) ∨ (¬ p 3879) ∨ (¬ p 4315) ∨ (¬ p 4814) :=
  ElevenRUP.step50231 (p 2027) (p 2406) (p 2630) (p 3879) (p 4315) (p 4814) (derived40810 p h) (h 23117)

theorem derived50232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3969) ∨ (¬ p 4286) ∨ (¬ p 4507) ∨ (¬ p 4607) :=
  ElevenRUP.step50232 (p 2027) (p 2563) (p 3969) (p 4286) (p 4507) (p 4607) (derived40810 p h) (h 23118)

theorem derived50233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2641) ∨ (¬ p 3156) ∨ (¬ p 3368) ∨ (¬ p 3413) ∨ (¬ p 4975) :=
  ElevenRUP.step50233 (p 2027) (p 2191) (p 2641) (p 3156) (p 3368) (p 3413) (p 4975) (derived40810 p h) (h 23119)

theorem derived50234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2311) ∨ (¬ p 2406) ∨ (¬ p 2427) ∨ (¬ p 2598) ∨ (¬ p 2785) ∨ (¬ p 3551) ∨ (¬ p 3590) ∨ (¬ p 3688) ∨ (¬ p 4556) ∨ (¬ p 4737) :=
  ElevenRUP.step50234 (p 2027) (p 2177) (p 2311) (p 2406) (p 2427) (p 2598) (p 2785) (p 3551) (p 3590) (p 3688) (p 4556) (p 4737) (derived40810 p h) (h 23120)

theorem derived50235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2427) ∨ (¬ p 4382) ∨ (¬ p 4556) ∨ (¬ p 4948) :=
  ElevenRUP.step50235 (p 2027) (p 2396) (p 2427) (p 4382) (p 4556) (p 4948) (derived40810 p h) (h 23121)

theorem derived50237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3032) ∨ (¬ p 3379) ∨ (¬ p 3740) ∨ (¬ p 4366) ∨ (¬ p 4644) :=
  ElevenRUP.step50237 (p 2027) (p 2406) (p 3032) (p 3379) (p 3740) (p 4366) (p 4644) (derived40810 p h) (h 23123)

theorem derived50238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2498) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 4715) :=
  ElevenRUP.step50238 (p 2027) (p 2406) (p 2498) (p 3379) (p 3591) (p 4715) (derived40810 p h) (h 23124)

theorem derived50239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (p 4972) :=
  ElevenRUP.step50239 (p 1991) (p 2287) (p 2657) (p 4972) (h 2151) (derived40869 p h) (h 23125)

theorem derived50240 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 2850) ∨ (¬ p 3475) ∨ (¬ p 4787) :=
  ElevenRUP.step50240 (p 2027) (p 2440) (p 2657) (p 2850) (p 3475) (p 4787) (derived40810 p h) (h 23126)

theorem derived50241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 3055) ∨ (¬ p 3684) ∨ (¬ p 3951) ∨ (¬ p 4736) ∨ (¬ p 4948) :=
  ElevenRUP.step50241 (p 2027) (p 2241) (p 2449) (p 3027) (p 3055) (p 3684) (p 3951) (p 4736) (p 4948) (derived40810 p h) (h 23127)

theorem derived50242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2696) ∨ (¬ p 2870) ∨ (¬ p 3556) ∨ (¬ p 5049) :=
  ElevenRUP.step50242 (p 2027) (p 2136) (p 2696) (p 2870) (p 3556) (p 5049) (derived40810 p h) (h 23128)

theorem derived50243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (¬ p 3556) ∨ (¬ p 4135) ∨ (¬ p 4277) ∨ (¬ p 4278) :=
  ElevenRUP.step50243 (p 2027) (p 3212) (p 3556) (p 4135) (p 4277) (p 4278) (derived40810 p h) (h 23129)

theorem derived50244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2191) ∨ (¬ p 2220) ∨ (¬ p 2737) ∨ (¬ p 4874) ∨ (¬ p 5049) :=
  ElevenRUP.step50244 (p 2027) (p 2137) (p 2191) (p 2220) (p 2737) (p 4874) (p 5049) (derived40810 p h) (h 23130)

theorem derived50246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2696) ∨ (¬ p 2860) ∨ (¬ p 3646) ∨ (¬ p 5049) :=
  ElevenRUP.step50246 (p 2027) (p 2136) (p 2696) (p 2860) (p 3646) (p 5049) (derived40810 p h) (h 23132)

theorem derived50247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 4120) ∨ (¬ p 4787) :=
  ElevenRUP.step50247 (p 2027) (p 2950) (p 3136) (p 3156) (p 4120) (p 4787) (derived40810 p h) (h 23133)

theorem derived50249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2299) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 2963) ∨ (¬ p 3379) ∨ (¬ p 3568) ∨ (¬ p 4668) :=
  ElevenRUP.step50249 (p 2027) (p 2254) (p 2299) (p 2417) (p 2922) (p 2963) (p 3379) (p 3568) (p 4668) (derived40810 p h) (h 23135)

theorem derived50250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2881) ∨ (¬ p 3389) ∨ (¬ p 4277) ∨ (¬ p 4383) :=
  ElevenRUP.step50250 (p 2027) (p 2476) (p 2881) (p 3389) (p 4277) (p 4383) (derived40810 p h) (h 23136)

theorem derived50251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2630) ∨ (¬ p 2950) ∨ (¬ p 3413) ∨ (¬ p 3646) ∨ (¬ p 4787) :=
  ElevenRUP.step50251 (p 2027) (p 2284) (p 2630) (p 2950) (p 3413) (p 3646) (p 4787) (derived40810 p h) (h 23137)

theorem derived50252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3568) ∨ (¬ p 4191) ∨ (¬ p 4421) ∨ (¬ p 4624) :=
  ElevenRUP.step50252 (p 2027) (p 3506) (p 3568) (p 4191) (p 4421) (p 4624) (derived40810 p h) (h 23138)

theorem derived50253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (¬ p 4173) ∨ (¬ p 4322) ∨ (¬ p 4942) ∨ (¬ p 5046) :=
  ElevenRUP.step50253 (p 2027) (p 3707) (p 4173) (p 4322) (p 4942) (p 5046) (derived40810 p h) (h 23139)

theorem derived50255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2860) ∨ (¬ p 4244) ∨ (¬ p 4275) ∨ (¬ p 4405) :=
  ElevenRUP.step50255 (p 2027) (p 2187) (p 2860) (p 4244) (p 4275) (p 4405) (derived40810 p h) (h 23141)

theorem derived50257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2780) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4736) :=
  ElevenRUP.step50257 (p 2027) (p 2417) (p 2780) (p 2922) (p 3379) (p 3950) (p 4347) (p 4358) (p 4736) (derived40810 p h) (h 23143)

theorem derived50258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2668) ∨ (¬ p 2797) ∨ (¬ p 3983) ∨ (¬ p 4787) :=
  ElevenRUP.step50258 (p 2027) (p 2387) (p 2668) (p 2797) (p 3983) (p 4787) (derived40810 p h) (h 23144)

theorem derived50260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3286) ∨ (¬ p 3917) ∨ (¬ p 4367) ∨ (¬ p 4843) :=
  ElevenRUP.step50260 (p 2027) (p 2963) (p 3286) (p 3917) (p 4367) (p 4843) (derived40810 p h) (h 23146)

theorem derived50261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2311) ∨ (¬ p 3204) ∨ (¬ p 3319) ∨ (¬ p 3551) ∨ (¬ p 4624) :=
  ElevenRUP.step50261 (p 2027) (p 2177) (p 2311) (p 3204) (p 3319) (p 3551) (p 4624) (derived40810 p h) (h 23147)

theorem derived50263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3568) ∨ (¬ p 4195) :=
  ElevenRUP.step50263 (p 1991) (p 2027) (p 2952) (p 2997) (p 3136) (p 3568) (p 4195) (h 2151) (derived40810 p h) (derived40890 p h) (h 23149)

theorem derived50264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 2952) ∨ (¬ p 3097) ∨ (¬ p 3379) ∨ (¬ p 3952) ∨ (¬ p 4405) :=
  ElevenRUP.step50264 (p 2027) (p 2254) (p 2352) (p 2493) (p 2952) (p 3097) (p 3379) (p 3952) (p 4405) (derived40810 p h) (h 23150)

theorem derived50265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3097) ∨ (¬ p 3550) ∨ (¬ p 4260) ∨ (¬ p 5559) :=
  ElevenRUP.step50265 (p 2027) (p 2187) (p 3097) (p 3550) (p 4260) (p 5559) (derived40810 p h) (h 23151)

theorem derived50266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2274) ∨ (¬ p 2829) ∨ (¬ p 3583) ∨ (¬ p 4185) :=
  ElevenRUP.step50266 (p 1998) (p 2027) (p 2177) (p 2274) (p 2829) (p 3474) (p 3583) (p 4185) (h 2158) (derived40810 p h) (derived40898 p h) (h 23152)

theorem derived50268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3551) ∨ (¬ p 3572) ∨ (¬ p 4378) ∨ (¬ p 4851) :=
  ElevenRUP.step50268 (p 2027) (p 3005) (p 3551) (p 3572) (p 4378) (p 4851) (derived40810 p h) (h 23155)

theorem derived50269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2493) ∨ (¬ p 3379) ∨ (¬ p 3564) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4621) ∨ (¬ p 4736) :=
  ElevenRUP.step50269 (p 2027) (p 2138) (p 2493) (p 3379) (p 3564) (p 3690) (p 4244) (p 4621) (p 4736) (derived40810 p h) (h 23156)

theorem derived50270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2829) ∨ (¬ p 2963) ∨ (¬ p 4328) ∨ (¬ p 4787) :=
  ElevenRUP.step50270 (p 2027) (p 2743) (p 2829) (p 2963) (p 4328) (p 4787) (derived40810 p h) (h 23157)

theorem derived50271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3201) ∨ (¬ p 3475) ∨ (¬ p 3742) ∨ (¬ p 4787) :=
  ElevenRUP.step50271 (p 2027) (p 2657) (p 3201) (p 3475) (p 3742) (p 4787) (derived40810 p h) (h 23158)

theorem derived50272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2553) ∨ (¬ p 3568) ∨ (¬ p 4194) ∨ (¬ p 4715) :=
  ElevenRUP.step50272 (p 2027) (p 2542) (p 2553) (p 3568) (p 4194) (p 4715) (derived40810 p h) (h 23159)

theorem derived50273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2952) ∨ (¬ p 3434) ∨ (¬ p 3570) ∨ (¬ p 4320) ∨ (¬ p 4668) :=
  ElevenRUP.step50273 (p 2027) (p 2254) (p 2608) (p 2707) (p 2952) (p 3434) (p 3570) (p 4320) (p 4668) (derived40810 p h) (h 23160)

theorem derived50275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2589) ∨ (¬ p 2641) ∨ (¬ p 3323) ∨ (¬ p 3692) ∨ (¬ p 3880) ∨ (¬ p 4330) ∨ (¬ p 5193) :=
  ElevenRUP.step50275 (p 2027) (p 2241) (p 2589) (p 2641) (p 3323) (p 3692) (p 3880) (p 4330) (p 5193) (derived40810 p h) (h 23162)

theorem derived50277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3570) ∨ (¬ p 4173) ∨ (¬ p 4431) ∨ (¬ p 4558) :=
  ElevenRUP.step50277 (p 2027) (p 3527) (p 3570) (p 4173) (p 4431) (p 4558) (derived40810 p h) (h 23164)

theorem derived50278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2295) ∨ (¬ p 2589) ∨ (¬ p 2641) ∨ (¬ p 3744) ∨ (¬ p 4110) ∨ (¬ p 4620) ∨ (¬ p 5193) :=
  ElevenRUP.step50278 (p 2027) (p 2241) (p 2295) (p 2589) (p 2641) (p 3744) (p 4110) (p 4620) (p 5193) (derived40810 p h) (h 23165)

theorem derived50279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2396) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4736) :=
  ElevenRUP.step50279 (p 2027) (p 2138) (p 2396) (p 3093) (p 3309) (p 3692) (p 3694) (p 3950) (p 4736) (derived40810 p h) (h 23166)

theorem derived50280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3690) ∨ (¬ p 4235) ∨ (¬ p 4666) ∨ (¬ p 5193) :=
  ElevenRUP.step50280 (p 2027) (p 2241) (p 2264) (p 2589) (p 3027) (p 3690) (p 4235) (p 4666) (p 5193) (derived40810 p h) (h 23167)

theorem derived50281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2542) ∨ (¬ p 2598) ∨ (¬ p 3698) ∨ (¬ p 4750) :=
  ElevenRUP.step50281 (p 2027) (p 2138) (p 2542) (p 2598) (p 3698) (p 4750) (derived40810 p h) (h 23168)

theorem derived50283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3367) ∨ (¬ p 3583) ∨ (¬ p 3698) ∨ (¬ p 4110) :=
  ElevenRUP.step50283 (p 1986) (p 2027) (p 2997) (p 3097) (p 3367) (p 3583) (p 3698) (p 4110) (h 2146) (derived40810 p h) (derived40890 p h) (h 23170)

theorem derived50284 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3146) ∨ (¬ p 4134) ∨ (¬ p 5193) :=
  ElevenRUP.step50284 (p 2027) (p 2241) (p 2476) (p 2534) (p 2641) (p 2668) (p 3146) (p 4134) (p 5193) (derived40810 p h) (h 23171)

theorem derived50285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3105) ∨ (¬ p 3694) ∨ (¬ p 4118) ∨ (¬ p 5063) :=
  ElevenRUP.step50285 (p 2027) (p 2532) (p 3105) (p 3694) (p 4118) (p 5063) (derived40810 p h) (h 23172)

theorem derived50288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3363) ∨ (¬ p 3585) ∨ (¬ p 4405) ∨ (¬ p 4737) :=
  ElevenRUP.step50288 (p 2027) (p 2579) (p 2588) (p 2641) (p 2668) (p 2696) (p 2742) (p 3363) (p 3585) (p 4405) (p 4737) (derived40810 p h) (h 23175)

theorem derived50289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3027) ∨ (¬ p 3931) ∨ (¬ p 4444) ∨ (¬ p 4826) ∨ (¬ p 5193) :=
  ElevenRUP.step50289 (p 2027) (p 2241) (p 2476) (p 2534) (p 3027) (p 3931) (p 4444) (p 4826) (p 5193) (derived40810 p h) (h 23176)

theorem derived50293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2780) ∨ (¬ p 3097) ∨ (¬ p 3583) ∨ (¬ p 4428) :=
  ElevenRUP.step50293 (p 1992) (p 2027) (p 2132) (p 2780) (p 2997) (p 3097) (p 3583) (p 4428) (h 2152) (derived40810 p h) (derived40890 p h) (h 23180)

theorem derived50294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3950) ∨ (¬ p 4425) ∨ (¬ p 5193) :=
  ElevenRUP.step50294 (p 2027) (p 2241) (p 2449) (p 3027) (p 3266) (p 3346) (p 3950) (p 4425) (p 5193) (derived40810 p h) (h 23181)

theorem derived50295 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2850) ∨ (¬ p 3556) ∨ (¬ p 3904) ∨ (¬ p 4727) :=
  ElevenRUP.step50295 (p 2027) (p 2427) (p 2850) (p 3556) (p 3904) (p 4727) (derived40810 p h) (h 23182)

theorem derived50296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2177) ∨ (¬ p 3570) ∨ (¬ p 3583) ∨ (¬ p 3646) ∨ (¬ p 4204) :=
  ElevenRUP.step50296 (p 1992) (p 2027) (p 2143) (p 2177) (p 2997) (p 3570) (p 3583) (p 3646) (p 4204) (h 2152) (derived40810 p h) (derived40890 p h) (h 23183)

theorem derived50297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 2579) ∨ (¬ p 3027) ∨ (¬ p 3950) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 5193) :=
  ElevenRUP.step50297 (p 2027) (p 2241) (p 2449) (p 2579) (p 3027) (p 3950) (p 3956) (p 4347) (p 5193) (derived40810 p h) (h 23184)

theorem derived50298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3367) ∨ (¬ p 3688) ∨ (¬ p 4342) ∨ (¬ p 4715) :=
  ElevenRUP.step50298 (p 2027) (p 2850) (p 3367) (p 3688) (p 4342) (p 4715) (derived40810 p h) (h 23185)

theorem derived50301 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2295) ∨ (¬ p 4118) ∨ (¬ p 4170) ∨ (¬ p 4196) ∨ (¬ p 4501) :=
  ElevenRUP.step50301 (p 2027) (p 2088) (p 2295) (p 4118) (p 4170) (p 4196) (p 4501) (derived40810 p h) (h 23188)

theorem derived50302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3172) ∨ (¬ p 3641) ∨ (¬ p 4437) ∨ (¬ p 4753) :=
  ElevenRUP.step50302 (p 2027) (p 2651) (p 3172) (p 3641) (p 4437) (p 4753) (derived40810 p h) (h 23189)

theorem derived50303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 3051) ∨ (¬ p 3365) ∨ (¬ p 4244) ∨ (¬ p 5052) :=
  ElevenRUP.step50303 (p 2027) (p 2144) (p 3051) (p 3365) (p 4244) (p 5052) (derived40810 p h) (h 23190)

theorem derived50304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2743) ∨ (¬ p 3371) ∨ (¬ p 3694) ∨ (¬ p 5052) :=
  ElevenRUP.step50304 (p 2027) (p 2166) (p 2743) (p 3371) (p 3694) (p 5052) (derived40810 p h) (h 23191)

theorem derived50305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 4107) ∨ (¬ p 4110) :=
  ElevenRUP.step50305 (p 1975) (p 2027) (p 2427) (p 2765) (p 3246) (p 4107) (p 4110) (h 2135) (derived40810 p h) (derived40883 p h) (h 23192)

theorem derived50306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3952) ∨ (¬ p 4237) ∨ (¬ p 4509) :=
  ElevenRUP.step50306 (p 2027) (p 3256) (p 3692) (p 3952) (p 4237) (p 4509) (derived40810 p h) (h 23193)

theorem derived50308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3745) ∨ (¬ p 4195) ∨ (¬ p 4509) :=
  ElevenRUP.step50308 (p 2027) (p 3136) (p 3156) (p 3745) (p 4195) (p 4509) (derived40810 p h) (h 23195)

theorem derived50310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3365) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4736) :=
  ElevenRUP.step50310 (p 2027) (p 2396) (p 3093) (p 3309) (p 3365) (p 3877) (p 3950) (p 4118) (p 4736) (derived40810 p h) (h 23197)

theorem derived50312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 4195) ∨ (¬ p 4389) ∨ (¬ p 4715) :=
  ElevenRUP.step50312 (p 2027) (p 2230) (p 2630) (p 2656) (p 4195) (p 4389) (p 4715) (derived40810 p h) (h 23199)

theorem derived50313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 3365) ∨ (¬ p 3379) ∨ (¬ p 3568) ∨ (¬ p 4195) ∨ (¬ p 4405) ∨ (¬ p 4736) :=
  ElevenRUP.step50313 (p 2027) (p 2352) (p 2493) (p 3365) (p 3379) (p 3568) (p 4195) (p 4405) (p 4736) (derived40810 p h) (h 23200)

theorem derived50317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2499) ∨ (¬ p 2518) ∨ (¬ p 2573) ∨ (¬ p 3570) ∨ (¬ p 4079) ∨ (¬ p 4133) ∨ (¬ p 4157) ∨ (¬ p 4244) ∨ (¬ p 4736) :=
  ElevenRUP.step50317 (p 2027) (p 2138) (p 2499) (p 2518) (p 2573) (p 3570) (p 4079) (p 4133) (p 4157) (p 4244) (p 4736) (derived40810 p h) (h 23204)

theorem derived50319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3365) ∨ (¬ p 4208) ∨ (¬ p 4315) ∨ (¬ p 4736) ∨ (¬ p 5059) :=
  ElevenRUP.step50319 (p 2027) (p 2363) (p 3063) (p 3093) (p 3365) (p 4208) (p 4315) (p 4736) (p 5059) (derived40810 p h) (h 23206)

theorem derived50320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2573) ∨ (¬ p 4079) :=
  ElevenRUP.step50320 (p 1982) (p 2027) (p 2499) (p 2518) (p 2528) (p 2573) (p 2699) (p 4079) (h 2142) (derived40810 p h) (derived40881 p h) (h 23207)

theorem derived50321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3212) ∨ (¬ p 4399) ∨ (¬ p 4715) ∨ (¬ p 4948) :=
  ElevenRUP.step50321 (p 2027) (p 2579) (p 3212) (p 4399) (p 4715) (p 4948) (derived40810 p h) (h 23208)

theorem derived50322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3570) ∨ (¬ p 4244) ∨ (¬ p 4668) ∨ (¬ p 4736) :=
  ElevenRUP.step50322 (p 2027) (p 2138) (p 2417) (p 2922) (p 3379) (p 3570) (p 4244) (p 4668) (p 4736) (derived40810 p h) (h 23209)

theorem derived50323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 2573) ∨ (¬ p 3570) ∨ (¬ p 4079) ∨ (¬ p 4133) ∨ (¬ p 4244) ∨ (¬ p 4347) ∨ (¬ p 4736) :=
  ElevenRUP.step50323 (p 2027) (p 2138) (p 2510) (p 2528) (p 2573) (p 3570) (p 4079) (p 4133) (p 4244) (p 4347) (p 4736) (derived40810 p h) (h 23210)

theorem derived50325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2630) ∨ (¬ p 2951) ∨ (¬ p 2962) ∨ (¬ p 4358) ∨ (¬ p 4701) ∨ (¬ p 4841) :=
  ElevenRUP.step50325 (p 2027) (p 2383) (p 2630) (p 2951) (p 2962) (p 4358) (p 4701) (p 4841) (derived40810 p h) (h 23212)

theorem derived50326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3365) ∨ (¬ p 3449) ∨ (¬ p 3497) ∨ (¬ p 4315) ∨ (¬ p 4348) ∨ (¬ p 4736) ∨ (¬ p 4905) :=
  ElevenRUP.step50326 (p 2027) (p 3073) (p 3365) (p 3449) (p 3497) (p 4315) (p 4348) (p 4736) (p 4905) (derived40810 p h) (h 23213)

theorem derived50327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2307) ∨ (¬ p 3063) ∨ (¬ p 3146) ∨ (¬ p 3172) ∨ (¬ p 3549) ∨ (¬ p 4118) ∨ (¬ p 4134) ∨ (¬ p 5020) :=
  ElevenRUP.step50327 (p 2027) (p 2254) (p 2307) (p 3063) (p 3146) (p 3172) (p 3549) (p 4118) (p 4134) (p 5020) (derived40810 p h) (h 23214)

theorem derived50328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2437) ∨ (¬ p 3096) ∨ (¬ p 3574) ∨ (¬ p 3575) ∨ (¬ p 4509) ∨ (¬ p 4984) :=
  ElevenRUP.step50328 (p 2027) (p 2220) (p 2437) (p 3096) (p 3574) (p 3575) (p 4509) (p 4984) (derived40810 p h) (h 23215)

theorem derived50329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 2449) ∨ (¬ p 3574) ∨ (¬ p 3580) ∨ (¬ p 4278) ∨ (¬ p 4715) :=
  ElevenRUP.step50329 (p 2027) (p 2441) (p 2449) (p 3574) (p 3580) (p 4278) (p 4715) (derived40810 p h) (h 23216)

theorem derived50331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3105) ∨ (¬ p 4110) ∨ (¬ p 4244) :=
  ElevenRUP.step50331 (p 2011) (p 2027) (p 2427) (p 2765) (p 3105) (p 4110) (p 4244) (h 2171) (derived40810 p h) (derived40883 p h) (h 23218)

theorem derived50332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2295) ∨ (¬ p 2312) ∨ (¬ p 4261) ∨ (¬ p 4371) ∨ (¬ p 4590) ∨ (¬ p 4757) :=
  ElevenRUP.step50332 (p 2027) (p 2088) (p 2295) (p 2312) (p 4261) (p 4371) (p 4590) (p 4757) (derived40810 p h) (h 23220)

theorem derived50334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2901) ∨ (¬ p 3540) ∨ (¬ p 3952) ∨ (¬ p 4001) :=
  ElevenRUP.step50334 (p 1997) (p 2027) (p 2230) (p 2765) (p 2901) (p 3540) (p 3952) (p 4001) (h 2157) (derived40810 p h) (derived40883 p h) (h 23222)

theorem derived50337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 4348) ∨ (¬ p 4423) ∨ (¬ p 4805) ∨ (¬ p 5559) :=
  ElevenRUP.step50337 (p 2027) (p 3609) (p 4348) (p 4423) (p 4805) (p 5559) (derived40810 p h) (h 23225)

theorem derived50340 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2972) ∨ (¬ p 3948) ∨ (¬ p 4031) ∨ (¬ p 4032) ∨ (¬ p 4715) :=
  ElevenRUP.step50340 (p 2027) (p 2499) (p 2972) (p 3948) (p 4031) (p 4032) (p 4715) (derived40810 p h) (h 23228)

theorem derived50341 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2245) ∨ (¬ p 2774) ∨ (¬ p 2952) ∨ (¬ p 3146) ∨ (¬ p 3661) ∨ (¬ p 4118) ∨ (¬ p 4733) ∨ (¬ p 4905) :=
  ElevenRUP.step50341 (p 2027) (p 2122) (p 2177) (p 2245) (p 2774) (p 2952) (p 3146) (p 3661) (p 4118) (p 4733) (p 4905) (derived40810 p h) (h 23229)

theorem derived50342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2498) ∨ (¬ p 2850) ∨ (¬ p 3822) ∨ (¬ p 4715) ∨ (¬ p 5016) ∨ (¬ p 5220) :=
  ElevenRUP.step50342 (p 2027) (p 2307) (p 2498) (p 2850) (p 3822) (p 4715) (p 5016) (p 5220) (derived40810 p h) (h 23230)

theorem derived50343 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2927) ∨ (¬ p 3516) ∨ (¬ p 3543) ∨ (¬ p 3686) ∨ (¬ p 4324) ∨ (¬ p 4644) :=
  ElevenRUP.step50343 (p 2027) (p 2850) (p 2927) (p 3516) (p 3543) (p 3686) (p 4324) (p 4644) (derived40810 p h) (h 23231)

theorem derived50344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 3791) ∨ (¬ p 4425) ∨ (¬ p 4733) ∨ (¬ p 4826) :=
  ElevenRUP.step50344 (p 2027) (p 2122) (p 2774) (p 3193) (p 3452) (p 3791) (p 4425) (p 4733) (p 4826) (derived40810 p h) (h 23232)

theorem derived50345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 2860) ∨ (¬ p 2901) ∨ (¬ p 3556) ∨ (¬ p 3952) :=
  ElevenRUP.step50345 (p 2027) (p 2140) (p 2860) (p 2901) (p 3556) (p 3952) (derived40810 p h) (h 23235)

theorem derived50347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 4032) ∨ (¬ p 4787) :=
  ElevenRUP.step50347 (p 2027) (p 2950) (p 3115) (p 3136) (p 4032) (p 4787) (derived40810 p h) (h 23237)

theorem derived50349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2177) ∨ (¬ p 3093) ∨ (¬ p 3146) ∨ (¬ p 3309) ∨ (¬ p 4340) ∨ (¬ p 4359) ∨ (¬ p 4736) ∨ (¬ p 4905) :=
  ElevenRUP.step50349 (p 2027) (p 2138) (p 2177) (p 3093) (p 3146) (p 3309) (p 4340) (p 4359) (p 4736) (p 4905) (derived40810 p h) (h 23239)

theorem derived50350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3694) ∨ (¬ p 4736) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step50350 (p 2027) (p 2138) (p 2363) (p 3063) (p 3093) (p 3694) (p 4736) (p 5118) (p 5568) (derived40810 p h) (h 23240)

theorem derived50352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3136) ∨ (¬ p 3519) ∨ (¬ p 4241) ∨ (¬ p 4715) :=
  ElevenRUP.step50352 (p 2027) (p 2499) (p 2662) (p 2810) (p 3136) (p 3519) (p 4241) (p 4715) (derived40810 p h) (h 23242)

theorem derived50354 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3452) ∨ (¬ p 3584) ∨ (¬ p 3590) ∨ (¬ p 4241) ∨ (¬ p 4282) ∨ (¬ p 4715) :=
  ElevenRUP.step50354 (p 2027) (p 2210) (p 3452) (p 3584) (p 3590) (p 4241) (p 4282) (p 4715) (derived40810 p h) (h 23244)

theorem derived50355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2579) ∨ (¬ p 3389) ∨ (¬ p 3742) ∨ (¬ p 4715) :=
  ElevenRUP.step50355 (p 2027) (p 2542) (p 2579) (p 3389) (p 3742) (p 4715) (derived40810 p h) (h 23245)

theorem derived50356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2850) ∨ (¬ p 3389) ∨ (¬ p 3876) ∨ (¬ p 4715) :=
  ElevenRUP.step50356 (p 2027) (p 2579) (p 2850) (p 3389) (p 3876) (p 4715) (derived40810 p h) (h 23246)

theorem derived50357 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2737) ∨ (¬ p 3506) ∨ (¬ p 4381) ∨ (¬ p 4661) :=
  ElevenRUP.step50357 (p 1983) (p 2027) (p 2114) (p 2685) (p 2737) (p 3506) (p 4381) (p 4661) (h 2143) (derived40810 p h) (derived40864 p h) (h 23248)

theorem derived50359 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2946) ∨ (¬ p 3359) ∨ (¬ p 4241) ∨ (¬ p 4949) :=
  ElevenRUP.step50359 (p 2027) (p 2657) (p 2946) (p 3359) (p 4241) (p 4949) (derived40810 p h) (h 23250)

theorem derived50360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2727) ∨ (¬ p 2807) ∨ (¬ p 2996) :=
  ElevenRUP.step50360 (p 1997) (p 2027) (p 2323) (p 2542) (p 2727) (p 2807) (p 2996) (h 2157) (derived40810 p h) (derived40870 p h) (h 23251)

theorem derived50361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3747) ∨ (¬ p 3969) ∨ (¬ p 4196) ∨ (¬ p 4275) ∨ (¬ p 4624) ∨ (¬ p 5600) :=
  ElevenRUP.step50361 (p 2027) (p 3323) (p 3747) (p 3969) (p 4196) (p 4275) (p 4624) (p 5600) (derived40810 p h) (h 23252)

theorem derived50363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2927) ∨ (¬ p 3379) ∨ (¬ p 3487) ∨ (¬ p 4366) ∨ (¬ p 4644) :=
  ElevenRUP.step50363 (p 2027) (p 2542) (p 2927) (p 3379) (p 3487) (p 4366) (p 4644) (derived40810 p h) (h 23254)

theorem derived50364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 3888) ∨ (¬ p 4194) ∨ (¬ p 4715) ∨ (¬ p 5717) :=
  ElevenRUP.step50364 (p 2027) (p 2542) (p 3888) (p 4194) (p 4715) (p 5717) (derived40810 p h) (h 23256)

theorem derived50365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2588) ∨ (¬ p 3222) ∨ (¬ p 4331) ∨ (¬ p 4624) :=
  ElevenRUP.step50365 (p 2027) (p 2499) (p 2588) (p 3222) (p 4331) (p 4624) (derived40810 p h) (h 23258)

theorem derived50366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3452) ∨ (¬ p 3979) ∨ (¬ p 4733) ∨ (¬ p 5122) :=
  ElevenRUP.step50366 (p 2027) (p 2509) (p 2534) (p 2774) (p 2819) (p 3452) (p 3979) (p 4733) (p 5122) (derived40810 p h) (h 23260)

theorem derived50367 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 3005) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4417) :=
  ElevenRUP.step50367 (p 1982) (p 2027) (p 2331) (p 2363) (p 2611) (p 3005) (p 4117) (p 4195) (p 4417) (h 2142) (derived40810 p h) (derived40877 p h) (h 23261)

theorem derived50368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2579) ∨ (¬ p 3553) ∨ (¬ p 4241) ∨ (¬ p 4386) ∨ (¬ p 4715) ∨ (¬ p 5201) :=
  ElevenRUP.step50368 (p 2027) (p 2341) (p 2579) (p 3553) (p 4241) (p 4386) (p 4715) (p 5201) (derived40810 p h) (h 23262)

theorem derived50369 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 4330) ∨ (¬ p 4733) :=
  ElevenRUP.step50369 (p 2027) (p 2191) (p 2696) (p 2797) (p 3323) (p 3555) (p 3692) (p 4330) (p 4733) (derived40810 p h) (h 23263)

theorem derived50373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2881) ∨ (¬ p 3323) ∨ (¬ p 3551) ∨ (¬ p 3690) ∨ (¬ p 4621) ∨ (¬ p 5210) :=
  ElevenRUP.step50373 (p 2027) (p 2241) (p 2641) (p 2881) (p 3323) (p 3551) (p 3690) (p 4621) (p 5210) (derived40810 p h) (h 23270)

theorem derived50375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 3791) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step50375 (p 2027) (p 2248) (p 2295) (p 2331) (p 3791) (p 3860) (p 4261) (p 4444) (p 4826) (derived40810 p h) (h 23272)

theorem derived50378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2651) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3580) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4117) ∨ (¬ p 4877) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step50378 (p 2027) (p 2449) (p 2651) (p 2753) (p 2761) (p 3580) (p 3645) (p 3646) (p 3989) (p 4117) (p 4877) (p 5123) (p 5580) (derived40810 p h) (h 23275)

theorem derived50379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3516) ∨ (¬ p 3551) ∨ (¬ p 4276) ∨ (¬ p 4278) :=
  ElevenRUP.step50379 (p 2027) (p 2177) (p 3516) (p 3551) (p 4276) (p 4278) (derived40810 p h) (h 23276)

theorem derived50380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2246) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 3860) ∨ (¬ p 4959) ∨ (¬ p 5118) ∨ (¬ p 5693) :=
  ElevenRUP.step50380 (p 2027) (p 2210) (p 2246) (p 2528) (p 2651) (p 3083) (p 3860) (p 4959) (p 5118) (p 5693) (derived40810 p h) (h 23277)

theorem derived50381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 4244) ∨ (¬ p 4392) ∨ (¬ p 4790) :=
  ElevenRUP.step50381 (p 2027) (p 2901) (p 2946) (p 4244) (p 4392) (p 4790) (derived40810 p h) (h 23278)

theorem derived50382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3583) ∨ (¬ p 3694) ∨ (¬ p 3954) ∨ (¬ p 4134) ∨ (¬ p 4347) :=
  ElevenRUP.step50382 (p 2027) (p 2248) (p 3166) (p 3256) (p 3583) (p 3694) (p 3954) (p 4134) (p 4347) (derived40810 p h) (h 23280)

theorem derived50383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2417) ∨ (¬ p 2922) ∨ (¬ p 3947) :=
  ElevenRUP.step50383 (p 1998) (p 2027) (p 2264) (p 2409) (p 2417) (p 2922) (p 3947) (h 2158) (derived40810 p h) (derived40874 p h) (h 23281)

theorem derived50384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2608) ∨ (¬ p 3452) :=
  ElevenRUP.step50384 (p 1992) (p 2027) (p 2509) (p 2534) (p 2608) (p 2766) (p 3452) (h 2152) (derived40810 p h) (derived40884 p h) (h 23282)

theorem derived50386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2928) ∨ (¬ p 3286) ∨ (¬ p 3452) ∨ (¬ p 3506) ∨ (¬ p 4191) ∨ (¬ p 4278) ∨ (¬ p 4621) :=
  ElevenRUP.step50386 (p 2027) (p 2248) (p 2928) (p 3286) (p 3452) (p 3506) (p 4191) (p 4278) (p 4621) (derived40810 p h) (h 23284)

theorem derived50387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3222) ∨ (¬ p 4107) ∨ (¬ p 4451) ∨ (¬ p 4712) :=
  ElevenRUP.step50387 (p 2027) (p 2928) (p 3222) (p 4107) (p 4451) (p 4712) (derived40810 p h) (h 23285)

theorem derived50388 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2542) ∨ (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 3096) ∨ (¬ p 4558) :=
  ElevenRUP.step50388 (p 2027) (p 2427) (p 2542) (p 2579) (p 2662) (p 3096) (p 4558) (derived40810 p h) (h 23286)

theorem derived50392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3055) ∨ (¬ p 3541) ∨ (¬ p 3584) ∨ (¬ p 4734) :=
  ElevenRUP.step50392 (p 2027) (p 2493) (p 3055) (p 3541) (p 3584) (p 4734) (derived40810 p h) (h 23292)

theorem derived50394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2972) ∨ (¬ p 3486) ∨ (¬ p 4135) ∨ (¬ p 4277) ∨ (¬ p 4278) :=
  ElevenRUP.step50394 (p 2027) (p 2972) (p 3486) (p 4135) (p 4277) (p 4278) (derived40810 p h) (h 23294)

theorem derived50396 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3347) ∨ (¬ p 3399) ∨ (¬ p 3954) ∨ (¬ p 4075) ∨ (¬ p 4444) ∨ (¬ p 4826) ∨ (¬ p 5216) :=
  ElevenRUP.step50396 (p 2027) (p 2476) (p 2534) (p 3347) (p 3399) (p 3954) (p 4075) (p 4444) (p 4826) (p 5216) (derived40810 p h) (h 23296)

theorem derived50399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (¬ p 3631) ∨ (¬ p 3687) ∨ (¬ p 3821) ∨ (¬ p 5206) ∨ (¬ p 5216) :=
  ElevenRUP.step50399 (p 2027) (p 3379) (p 3631) (p 3687) (p 3821) (p 5206) (p 5216) (derived40810 p h) (h 23300)

theorem derived50403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2995) ∨ (¬ p 3136) ∨ (¬ p 3551) ∨ (¬ p 4787) ∨ (¬ p 4849) :=
  ElevenRUP.step50403 (p 2027) (p 2264) (p 2995) (p 3136) (p 3551) (p 4787) (p 4849) (derived40810 p h) (h 23304)

theorem derived50404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2630) ∨ (¬ p 2655) ∨ (¬ p 3083) ∨ (¬ p 4787) :=
  ElevenRUP.step50404 (p 2027) (p 2476) (p 2630) (p 2655) (p 3083) (p 4787) (derived40810 p h) (h 23305)

theorem derived50406 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 3093) ∨ (¬ p 3365) ∨ (¬ p 3527) ∨ (¬ p 4315) ∨ (¬ p 4320) ∨ (¬ p 4452) ∨ (¬ p 4559) ∨ (¬ p 4736) :=
  ElevenRUP.step50406 (p 2027) (p 2299) (p 3093) (p 3365) (p 3527) (p 4315) (p 4320) (p 4452) (p 4559) (p 4736) (derived40810 p h) (h 23307)

theorem derived50407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2928) ∨ (¬ p 3019) ∨ (¬ p 3644) ∨ (¬ p 4156) ∨ (¬ p 4811) :=
  ElevenRUP.step50407 (p 2027) (p 2264) (p 2928) (p 3019) (p 3644) (p 4156) (p 4811) (derived40810 p h) (h 23308)

theorem derived50408 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2387) ∨ (¬ p 2911) ∨ (¬ p 4138) ∨ (¬ p 4712) :=
  ElevenRUP.step50408 (p 2027) (p 2307) (p 2387) (p 2911) (p 4138) (p 4712) (derived40810 p h) (h 23309)

theorem derived50409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 3346) ∨ (¬ p 3347) ∨ (¬ p 3543) ∨ (¬ p 3680) ∨ (¬ p 3951) ∨ (¬ p 4257) ∨ (¬ p 4425) ∨ (¬ p 4793) :=
  ElevenRUP.step50409 (p 2027) (p 2299) (p 2341) (p 2396) (p 3346) (p 3347) (p 3543) (p 3680) (p 3951) (p 4257) (p 4425) (p 4793) (derived40810 p h) (h 23310)

theorem derived50410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2982) ∨ (¬ p 3096) ∨ (¬ p 3584) ∨ (¬ p 5046) :=
  ElevenRUP.step50410 (p 2027) (p 2850) (p 2982) (p 3096) (p 3584) (p 5046) (derived40810 p h) (h 23311)

theorem derived50411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2727) ∨ (¬ p 2950) ∨ (¬ p 3115) ∨ (¬ p 4032) ∨ (¬ p 4701) :=
  ElevenRUP.step50411 (p 2027) (p 2252) (p 2727) (p 2950) (p 3115) (p 4032) (p 4701) (derived40810 p h) (h 23312)

theorem derived50412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2579) ∨ (¬ p 2928) ∨ (¬ p 3389) ∨ (¬ p 4715) :=
  ElevenRUP.step50412 (p 2027) (p 2406) (p 2579) (p 2928) (p 3389) (p 4715) (derived40810 p h) (h 23313)

theorem derived50416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2982) ∨ (¬ p 3365) ∨ (¬ p 3379) ∨ (¬ p 3877) ∨ (¬ p 4118) ∨ (¬ p 4450) ∨ (¬ p 4736) :=
  ElevenRUP.step50416 (p 2027) (p 2406) (p 2982) (p 3365) (p 3379) (p 3877) (p 4118) (p 4450) (p 4736) (derived40810 p h) (h 23318)

theorem derived50418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (¬ p 2963) ∨ (¬ p 3552) ∨ (¬ p 3822) ∨ (¬ p 4843) :=
  ElevenRUP.step50418 (p 2027) (p 2807) (p 2963) (p 3552) (p 3822) (p 4843) (derived40810 p h) (h 23320)

theorem derived50419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2810) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3365) ∨ (¬ p 4256) ∨ (¬ p 4438) ∨ (¬ p 4736) :=
  ElevenRUP.step50419 (p 2027) (p 2177) (p 2810) (p 3093) (p 3309) (p 3365) (p 4256) (p 4438) (p 4736) (derived40810 p h) (h 23321)

theorem derived50420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3365) ∨ (¬ p 3379) ∨ (¬ p 3564) ∨ (¬ p 3568) ∨ (¬ p 4195) ∨ (¬ p 4624) ∨ (¬ p 4736) :=
  ElevenRUP.step50420 (p 2027) (p 2493) (p 3365) (p 3379) (p 3564) (p 3568) (p 4195) (p 4624) (p 4736) (derived40810 p h) (h 23322)

theorem derived50421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3692) ∨ (¬ p 3880) ∨ (¬ p 4444) ∨ (¬ p 5193) :=
  ElevenRUP.step50421 (p 1998) (p 2027) (p 2241) (p 2264) (p 2589) (p 2764) (p 3027) (p 3692) (p 3880) (p 4444) (p 5193) (h 2158) (derived40810 p h) (derived40882 p h) (h 23323)

theorem derived50422 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 3365) ∨ (¬ p 3758) ∨ (¬ p 5052) :=
  ElevenRUP.step50422 (p 2027) (p 2144) (p 2156) (p 3365) (p 3758) (p 5052) (derived40810 p h) (h 23324)

theorem derived50424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2531) ∨ (¬ p 3083) ∨ (¬ p 3694) ∨ (¬ p 4882) :=
  ElevenRUP.step50424 (p 2027) (p 2440) (p 2531) (p 3083) (p 3694) (p 4882) (derived40810 p h) (h 23327)

theorem derived50428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2928) ∨ (¬ p 3156) ∨ (¬ p 3452) ∨ (¬ p 3644) ∨ (¬ p 3952) ∨ (¬ p 4521) ∨ (¬ p 4902) :=
  ElevenRUP.step50428 (p 2027) (p 2156) (p 2928) (p 3156) (p 3452) (p 3644) (p 3952) (p 4521) (p 4902) (derived40810 p h) (h 23331)

theorem derived50429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3367) ∨ (¬ p 3583) ∨ (¬ p 3698) ∨ (¬ p 4646) :=
  ElevenRUP.step50429 (p 2027) (p 3201) (p 3367) (p 3583) (p 3698) (p 4646) (derived40810 p h) (h 23332)

theorem derived50430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2598) ∨ (¬ p 4286) ∨ (¬ p 5369) ∨ (¬ p 5616) ∨ (¬ p 5682) :=
  ElevenRUP.step50430 (p 2027) (p 2104) (p 2598) (p 4286) (p 5369) (p 5616) (p 5682) (derived40810 p h) (h 23333)

theorem derived50431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3941) ∨ (¬ p 4119) ∨ (¬ p 4898) ∨ (¬ p 5568) :=
  ElevenRUP.step50431 (p 2027) (p 2717) (p 3941) (p 4119) (p 4898) (p 5568) (derived40810 p h) (h 23334)

theorem derived50433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 2459) ∨ (¬ p 2509) ∨ (¬ p 2668) ∨ (¬ p 3452) ∨ (¬ p 3550) ∨ (¬ p 4286) ∨ (¬ p 5118) :=
  ElevenRUP.step50433 (p 2027) (p 2248) (p 2331) (p 2459) (p 2509) (p 2668) (p 3452) (p 3550) (p 4286) (p 5118) (derived40810 p h) (h 23336)

theorem derived50434 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2449) ∨ (¬ p 2995) ∨ (¬ p 3690) ∨ (¬ p 3952) :=
  ElevenRUP.step50434 (p 1985) (p 2027) (p 2148) (p 2156) (p 2449) (p 2995) (p 3690) (p 3952) (h 2145) (derived40810 p h) (derived40865 p h) (h 23337)

theorem derived50436 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3758) ∨ (¬ p 4019) ∨ (¬ p 4509) ∨ (¬ p 4744) ∨ (¬ p 5568) :=
  ElevenRUP.step50436 (p 2027) (p 3758) (p 4019) (p 4509) (p 4744) (p 5568) (derived40810 p h) (h 23339)

theorem derived50439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2504) ∨ (¬ p 3093) ∨ (¬ p 3452) ∨ (¬ p 3574) ∨ (¬ p 4814) :=
  ElevenRUP.step50439 (p 2027) (p 2504) (p 3093) (p 3452) (p 3574) (p 4814) (derived40810 p h) (h 23343)

theorem derived50440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2588) ∨ (¬ p 3550) ∨ (¬ p 3570) ∨ (¬ p 4556) :=
  ElevenRUP.step50440 (p 2027) (p 2352) (p 2588) (p 3550) (p 3570) (p 4556) (derived40810 p h) (h 23344)

theorem derived50441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2901) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 3952) ∨ (¬ p 4521) ∨ (¬ p 4898) :=
  ElevenRUP.step50441 (p 2027) (p 2156) (p 2901) (p 3055) (p 3367) (p 3588) (p 3873) (p 3952) (p 4521) (p 4898) (derived40810 p h) (h 23345)

theorem derived50442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 2707) ∨ (¬ p 3556) ∨ (¬ p 3583) ∨ (¬ p 4344) :=
  ElevenRUP.step50442 (p 2027) (p 2140) (p 2707) (p 3556) (p 3583) (p 4344) (derived40810 p h) (h 23346)

theorem derived50443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 3873) ∨ (¬ p 4173) ∨ (¬ p 4874) :=
  ElevenRUP.step50443 (p 1984) (p 2027) (p 2202) (p 2563) (p 3055) (p 3367) (p 3873) (p 4173) (p 4874) (h 2144) (derived40810 p h) (derived40867 p h) (h 23347)

theorem derived50446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2911) ∨ (¬ p 3097) ∨ (¬ p 3920) ∨ (¬ p 4718) :=
  ElevenRUP.step50446 (p 2027) (p 2299) (p 2911) (p 3097) (p 3920) (p 4718) (derived40810 p h) (h 23351)

theorem derived50448 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2960) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3947) ∨ (¬ p 4386) :=
  ElevenRUP.step50448 (p 2027) (p 2960) (p 3051) (p 3246) (p 3947) (p 4386) (derived40810 p h) (h 23353)

theorem derived50450 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2651) ∨ (¬ p 2963) ∨ (¬ p 4389) ∨ (¬ p 4814) :=
  ElevenRUP.step50450 (p 2027) (p 2493) (p 2651) (p 2963) (p 4389) (p 4814) (derived40810 p h) (h 23356)

theorem derived50451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2579) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3422) ∨ (¬ p 3874) ∨ (¬ p 4438) ∨ (¬ p 5193) :=
  ElevenRUP.step50451 (p 2027) (p 2210) (p 2579) (p 2881) (p 2891) (p 3422) (p 3874) (p 4438) (p 5193) (derived40810 p h) (h 23357)

theorem derived50452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 2951) ∨ (¬ p 3051) ∨ (¬ p 3368) ∨ (¬ p 3486) ∨ (¬ p 4701) :=
  ElevenRUP.step50452 (p 2027) (p 2727) (p 2951) (p 3051) (p 3368) (p 3486) (p 4701) (derived40810 p h) (h 23358)

theorem derived50453 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2839) ∨ (¬ p 2881) ∨ (¬ p 2928) ∨ (¬ p 3051) ∨ (¬ p 3055) ∨ (¬ p 4030) ∨ (¬ p 4278) ∨ (¬ p 4666) ∨ (¬ p 4734) :=
  ElevenRUP.step50453 (p 2027) (p 2137) (p 2839) (p 2881) (p 2928) (p 3051) (p 3055) (p 4030) (p 4278) (p 4666) (p 4734) (derived40810 p h) (h 23360)

theorem derived50454 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2396) ∨ (¬ p 2748) ∨ (¬ p 2779) ∨ (¬ p 2829) ∨ (¬ p 3365) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 4734) :=
  ElevenRUP.step50454 (p 2027) (p 2307) (p 2396) (p 2748) (p 2779) (p 2829) (p 3365) (p 3950) (p 4118) (p 4360) (p 4734) (derived40810 p h) (h 23361)

theorem derived50456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2630) ∨ (¬ p 2951) ∨ (¬ p 3694) ∨ (¬ p 4392) ∨ (¬ p 4701) :=
  ElevenRUP.step50456 (p 2027) (p 2220) (p 2630) (p 2951) (p 3694) (p 4392) (p 4701) (derived40810 p h) (h 23364)

theorem derived50458 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2663) ∨ (¬ p 2952) ∨ (¬ p 4256) ∨ (¬ p 4701) :=
  ElevenRUP.step50458 (p 2027) (p 2470) (p 2663) (p 2952) (p 4256) (p 4701) (derived40810 p h) (h 23367)

theorem derived50459 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3166) ∨ (¬ p 3989) ∨ (¬ p 4417) ∨ (¬ p 4560) :=
  ElevenRUP.step50459 (p 2027) (p 2963) (p 3166) (p 3989) (p 4417) (p 4560) (derived40810 p h) (h 23369)

theorem derived50461 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 4733) :=
  ElevenRUP.step50461 (p 2027) (p 2132) (p 2247) (p 2870) (p 3246) (p 3950) (p 4118) (p 4360) (p 4733) (derived40810 p h) (h 23371)

theorem derived50462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3051) ∨ (¬ p 3370) ∨ (¬ p 3412) ∨ (¬ p 4244) ∨ (¬ p 4392) ∨ (¬ p 4701) :=
  ElevenRUP.step50462 (p 2027) (p 2630) (p 3051) (p 3370) (p 3412) (p 4244) (p 4392) (p 4701) (derived40810 p h) (h 23372)

theorem derived50465 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2727) ∨ (¬ p 3591) ∨ (¬ p 4319) ∨ (¬ p 4972) :=
  ElevenRUP.step50465 (p 2027) (p 2241) (p 2727) (p 3591) (p 4319) (p 4972) (derived40810 p h) (h 23375)

theorem derived50466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2417) ∨ (¬ p 3570) ∨ (¬ p 3821) ∨ (¬ p 4647) :=
  ElevenRUP.step50466 (p 2027) (p 2341) (p 2417) (p 3570) (p 3821) (p 4647) (derived40810 p h) (h 23377)

theorem derived50467 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2341) ∨ (¬ p 2839) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 4988) :=
  ElevenRUP.step50467 (p 1983) (p 2027) (p 2114) (p 2137) (p 2341) (p 2839) (p 3246) (p 3570) (p 4988) (h 2143) (derived40810 p h) (derived40864 p h) (h 23378)

theorem derived50468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 4988) :=
  ElevenRUP.step50468 (p 1983) (p 2027) (p 2341) (p 2622) (p 2951) (p 3136) (p 3246) (p 3570) (p 4988) (h 2143) (derived40810 p h) (derived40878 p h) (h 23379)

theorem derived50471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2588) ∨ (¬ p 3055) ∨ (¬ p 3527) ∨ (¬ p 3570) ∨ (¬ p 3584) ∨ (¬ p 4431) ∨ (¬ p 4556) ∨ (¬ p 4736) :=
  ElevenRUP.step50471 (p 2027) (p 2210) (p 2588) (p 3055) (p 3527) (p 3570) (p 3584) (p 4431) (p 4556) (p 4736) (derived40810 p h) (h 23383)

theorem derived50472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3989) ∨ (¬ p 4261) ∨ (¬ p 4318) ∨ (¬ p 4341) ∨ (¬ p 4560) :=
  ElevenRUP.step50472 (p 2027) (p 3256) (p 3989) (p 4261) (p 4318) (p 4341) (p 4560) (derived40810 p h) (h 23384)

theorem derived50473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 3414) ∨ (¬ p 3644) ∨ (¬ p 3740) :=
  ElevenRUP.step50473 (p 1987) (p 2027) (p 2633) (p 2651) (p 2810) (p 3414) (p 3644) (p 3740) (h 2147) (derived40810 p h) (derived40879 p h) (h 23385)

theorem derived50474 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2518) ∨ (¬ p 3193) ∨ (¬ p 4440) ∨ (¬ p 4596) :=
  ElevenRUP.step50474 (p 2027) (p 2363) (p 2518) (p 3193) (p 4440) (p 4596) (derived40810 p h) (h 23386)

theorem derived50477 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2307) ∨ (¬ p 3570) ∨ (¬ p 4204) ∨ (¬ p 4489) :=
  ElevenRUP.step50477 (p 2027) (p 2177) (p 2307) (p 3570) (p 4204) (p 4489) (derived40810 p h) (h 23389)

theorem derived50480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3367) ∨ (¬ p 3583) ∨ (¬ p 3698) ∨ (¬ p 3759) ∨ (¬ p 4610) :=
  ElevenRUP.step50480 (p 2027) (p 2470) (p 3367) (p 3583) (p 3698) (p 3759) (p 4610) (derived40810 p h) (h 23392)

theorem derived50482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2383) ∨ (¬ p 3497) ∨ (¬ p 4489) ∨ (¬ p 4506) :=
  ElevenRUP.step50482 (p 2027) (p 2284) (p 2383) (p 3497) (p 4489) (p 4506) (derived40810 p h) (h 23398)

theorem derived50483 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2383) ∨ (¬ p 2748) ∨ (¬ p 2786) ∨ (¬ p 3923) ∨ (¬ p 4245) ∨ (¬ p 5049) :=
  ElevenRUP.step50483 (p 2027) (p 2138) (p 2383) (p 2748) (p 2786) (p 3923) (p 4245) (p 5049) (derived40810 p h) (h 23400)

theorem derived50484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2137) ∨ (¬ p 2737) ∨ (¬ p 2774) ∨ (¬ p 3688) ∨ (¬ p 5049) :=
  ElevenRUP.step50484 (p 2027) (p 2136) (p 2137) (p 2737) (p 2774) (p 3688) (p 5049) (derived40810 p h) (h 23401)

theorem derived50485 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 2748) ∨ (¬ p 2786) ∨ (¬ p 3549) ∨ (¬ p 4245) ∨ (¬ p 5049) :=
  ElevenRUP.step50485 (p 2027) (p 2138) (p 2307) (p 2748) (p 2786) (p 3549) (p 4245) (p 5049) (derived40810 p h) (h 23402)

theorem derived50486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2737) ∨ (¬ p 3051) ∨ (¬ p 3486) ∨ (¬ p 4874) ∨ (¬ p 5049) :=
  ElevenRUP.step50486 (p 2027) (p 2137) (p 2737) (p 3051) (p 3486) (p 4874) (p 5049) (derived40810 p h) (h 23404)

theorem derived50487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 2786) ∨ (¬ p 3822) ∨ (¬ p 4841) ∨ (¬ p 5049) :=
  ElevenRUP.step50487 (p 2027) (p 2138) (p 2307) (p 2786) (p 3822) (p 4841) (p 5049) (derived40810 p h) (h 23405)

theorem derived50488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2657) ∨ (¬ p 3644) ∨ (¬ p 3742) ∨ (¬ p 4133) :=
  ElevenRUP.step50488 (p 2027) (p 2187) (p 2192) (p 2210) (p 2254) (p 2657) (p 3644) (p 3742) (p 4133) (derived40810 p h) (h 23406)

theorem derived50489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 3366) ∨ (¬ p 3414) ∨ (¬ p 3537) ∨ (¬ p 3553) ∨ (¬ p 3609) ∨ (¬ p 5049) ∨ (¬ p 5118) ∨ (¬ p 5558) :=
  ElevenRUP.step50489 (p 2027) (p 2138) (p 2252) (p 2748) (p 3366) (p 3414) (p 3537) (p 3553) (p 3609) (p 5049) (p 5118) (p 5558) (derived40810 p h) (h 23407)

theorem derived50491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2657) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3644) ∨ (¬ p 3742) ∨ (¬ p 4668) :=
  ElevenRUP.step50491 (p 2027) (p 2210) (p 2254) (p 2657) (p 2891) (p 3246) (p 3644) (p 3742) (p 4668) (derived40810 p h) (h 23409)

theorem derived50493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2972) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 3680) ∨ (¬ p 5123) ∨ (¬ p 5193) ∨ (¬ p 5558) :=
  ElevenRUP.step50493 (p 2027) (p 2210) (p 2972) (p 3540) (p 3644) (p 3680) (p 5123) (p 5193) (p 5558) (derived40810 p h) (h 23411)

theorem derived50495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2963) ∨ (¬ p 2972) ∨ (¬ p 3568) ∨ (¬ p 3680) ∨ (¬ p 4260) ∨ (¬ p 4831) :=
  ElevenRUP.step50495 (p 2027) (p 2210) (p 2254) (p 2963) (p 2972) (p 3568) (p 3680) (p 4260) (p 4831) (derived40810 p h) (h 23413)

theorem derived50496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2829) ∨ (¬ p 3583) ∨ (¬ p 4120) ∨ (¬ p 4185) ∨ (¬ p 4507) :=
  ElevenRUP.step50496 (p 2027) (p 2143) (p 2829) (p 3583) (p 4120) (p 4185) (p 4507) (derived40810 p h) (h 23414)

theorem derived50497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2299) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3537) ∨ (¬ p 3583) ∨ (¬ p 3589) ∨ (¬ p 4802) ∨ (¬ p 5193) :=
  ElevenRUP.step50497 (p 2027) (p 2132) (p 2299) (p 2579) (p 2588) (p 3537) (p 3583) (p 3589) (p 4802) (p 5193) (derived40810 p h) (h 23415)

theorem derived50498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2774) ∨ (¬ p 3694) ∨ (¬ p 4185) ∨ (¬ p 4507) :=
  ElevenRUP.step50498 (p 2027) (p 2138) (p 2774) (p 3694) (p 4185) (p 4507) (derived40810 p h) (h 23416)

theorem derived50500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3644) ∨ (¬ p 3692) ∨ (¬ p 4443) ∨ (¬ p 4902) :=
  ElevenRUP.step50500 (p 2027) (p 2417) (p 3644) (p 3692) (p 4443) (p 4902) (derived40810 p h) (h 23418)

theorem derived50501 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2992) ∨ (¬ p 3156) ∨ (¬ p 3367) ∨ (¬ p 4242) ∨ (¬ p 4340) ∨ (¬ p 4902) :=
  ElevenRUP.step50501 (p 1986) (p 2027) (p 2241) (p 2459) (p 2699) (p 2992) (p 3156) (p 3367) (p 4242) (p 4340) (p 4902) (h 2146) (derived40810 p h) (derived40881 p h) (h 23419)

theorem derived50502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2284) ∨ (¬ p 2972) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4208) ∨ (¬ p 4348) ∨ (¬ p 5193) :=
  ElevenRUP.step50502 (p 1990) (p 2027) (p 2210) (p 2284) (p 2766) (p 2972) (p 3540) (p 3644) (p 4208) (p 4348) (p 5193) (h 2150) (derived40810 p h) (derived40884 p h) (h 23420)

theorem derived50503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2992) ∨ (¬ p 3115) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4348) ∨ (¬ p 4450) ∨ (¬ p 5193) :=
  ElevenRUP.step50503 (p 2027) (p 2241) (p 2992) (p 3115) (p 3540) (p 3644) (p 4348) (p 4450) (p 5193) (derived40810 p h) (h 23421)

theorem derived50504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2860) ∨ (¬ p 3591) ∨ (¬ p 3957) ∨ (¬ p 4875) :=
  ElevenRUP.step50504 (p 2027) (p 2210) (p 2860) (p 3591) (p 3957) (p 4875) (derived40810 p h) (h 23422)

theorem derived50505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3692) ∨ (¬ p 4902) ∨ (¬ p 5193) :=
  ElevenRUP.step50505 (p 2027) (p 2299) (p 2579) (p 2588) (p 3073) (p 3449) (p 3692) (p 4902) (p 5193) (derived40810 p h) (h 23423)

theorem derived50506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3588) ∨ (¬ p 3599) ∨ (¬ p 3690) ∨ (¬ p 4898) ∨ (¬ p 5233) :=
  ElevenRUP.step50506 (p 2027) (p 3588) (p 3599) (p 3690) (p 4898) (p 5233) (derived40810 p h) (h 23424)

theorem derived50507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 4107) :=
  ElevenRUP.step50507 (p 1975) (p 2027) (p 2210) (p 2699) (p 2891) (p 3246) (p 4107) (h 2135) (derived40810 p h) (derived40881 p h) (h 23425)

theorem derived50508 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2254) ∨ (¬ p 2761) ∨ (¬ p 3125) ∨ (¬ p 3414) ∨ (¬ p 4429) ∨ (¬ p 4621) ∨ (¬ p 5284) :=
  ElevenRUP.step50508 (p 2027) (p 2192) (p 2210) (p 2254) (p 2761) (p 3125) (p 3414) (p 4429) (p 4621) (p 5284) (derived40810 p h) (h 23427)

theorem derived50512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2252) ∨ (¬ p 2299) ∨ (¬ p 2748) ∨ (¬ p 2963) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 3568) ∨ (¬ p 4668) ∨ (¬ p 5049) :=
  ElevenRUP.step50512 (p 2027) (p 2138) (p 2252) (p 2299) (p 2748) (p 2963) (p 3434) (p 3471) (p 3568) (p 4668) (p 5049) (derived40810 p h) (h 23432)

theorem derived50513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2860) ∨ (¬ p 4173) ∨ (¬ p 4874) ∨ (¬ p 5049) :=
  ElevenRUP.step50513 (p 2027) (p 2737) (p 2860) (p 4173) (p 4874) (p 5049) (derived40810 p h) (h 23433)

theorem derived50515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 3292) ∨ (¬ p 3434) ∨ (¬ p 3461) ∨ (¬ p 3471) ∨ (¬ p 4625) ∨ (¬ p 5049) ∨ (¬ p 5284) :=
  ElevenRUP.step50515 (p 2027) (p 2138) (p 2252) (p 2748) (p 3292) (p 3434) (p 3461) (p 3471) (p 4625) (p 5049) (p 5284) (derived40810 p h) (h 23436)

theorem derived50518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3877) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4736) :=
  ElevenRUP.step50518 (p 2027) (p 2210) (p 2891) (p 3246) (p 3365) (p 3877) (p 3950) (p 4118) (p 4736) (derived40810 p h) (h 23439)

theorem derived50520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 4173) ∨ (¬ p 4446) ∨ (¬ p 4509) :=
  ElevenRUP.step50520 (p 2027) (p 3449) (p 3555) (p 4173) (p 4446) (p 4509) (derived40810 p h) (h 23441)

theorem derived50523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3055) ∨ (¬ p 3707) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4322) ∨ (¬ p 4395) ∨ (¬ p 4736) ∨ (¬ p 4942) :=
  ElevenRUP.step50523 (p 2027) (p 2210) (p 3055) (p 3707) (p 3876) (p 4278) (p 4322) (p 4395) (p 4736) (p 4942) (derived40810 p h) (h 23445)

theorem derived50525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2518) ∨ (¬ p 2655) ∨ (¬ p 3361) ∨ (¬ p 3541) ∨ (¬ p 3583) ∨ (¬ p 5049) :=
  ElevenRUP.step50525 (p 2027) (p 2476) (p 2518) (p 2655) (p 3361) (p 3541) (p 3583) (p 5049) (derived40810 p h) (h 23448)

theorem derived50529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2748) ∨ (¬ p 2928) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3402) ∨ (¬ p 5049) :=
  ElevenRUP.step50529 (p 2027) (p 2138) (p 2748) (p 2928) (p 3362) (p 3389) (p 3402) (p 5049) (derived40810 p h) (h 23455)

theorem derived50530 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3659) ∨ (¬ p 3670) ∨ (¬ p 4381) ∨ (¬ p 4668) ∨ (¬ p 5234) :=
  ElevenRUP.step50530 (p 2027) (p 3659) (p 3670) (p 4381) (p 4668) (p 5234) (derived40810 p h) (h 23456)

theorem derived50534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3016) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3570) ∨ (¬ p 3742) ∨ (¬ p 4647) ∨ (¬ p 5193) :=
  ElevenRUP.step50534 (p 2027) (p 2579) (p 3016) (p 3399) (p 3527) (p 3570) (p 3742) (p 4647) (p 5193) (derived40810 p h) (h 23461)

theorem derived50537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2737) ∨ (¬ p 2797) ∨ (¬ p 3055) ∨ (¬ p 3584) ∨ (¬ p 3956) ∨ (¬ p 4501) ∨ (¬ p 4734) :=
  ElevenRUP.step50537 (p 2027) (p 2295) (p 2737) (p 2797) (p 3055) (p 3584) (p 3956) (p 4501) (p 4734) (derived40810 p h) (h 23464)

theorem derived50538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4733) :=
  ElevenRUP.step50538 (p 2027) (p 2668) (p 2696) (p 2797) (p 3486) (p 3555) (p 3570) (p 4133) (p 4733) (derived40810 p h) (h 23465)

theorem derived50540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 3367) ∨ (¬ p 3583) ∨ (¬ p 3698) ∨ (¬ p 4750) :=
  ElevenRUP.step50540 (p 2027) (p 2542) (p 3367) (p 3583) (p 3698) (p 4750) (derived40810 p h) (h 23470)

theorem derived50541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2528) ∨ (¬ p 3949) ∨ (¬ p 4032) ∨ (¬ p 4434) :=
  ElevenRUP.step50541 (p 2027) (p 2220) (p 2528) (p 3949) (p 4032) (p 4434) (derived40810 p h) (h 23471)

theorem derived50543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 3156) ∨ (¬ p 3568) ∨ (¬ p 4153) ∨ (¬ p 4509) :=
  ElevenRUP.step50543 (p 2027) (p 2274) (p 3156) (p 3568) (p 4153) (p 4509) (derived40810 p h) (h 23473)

theorem derived50544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2598) ∨ (¬ p 3083) ∨ (¬ p 4750) ∨ (¬ p 5369) :=
  ElevenRUP.step50544 (p 2027) (p 2104) (p 2598) (p 3083) (p 4750) (p 5369) (derived40810 p h) (h 23474)

theorem derived50546 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 3645) ∨ (¬ p 3954) ∨ (¬ p 4276) ∨ (¬ p 4877) :=
  ElevenRUP.step50546 (p 2027) (p 2177) (p 2922) (p 3379) (p 3556) (p 3570) (p 3645) (p 3954) (p 4276) (p 4877) (derived40810 p h) (h 23476)

theorem derived50550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3146) ∨ (¬ p 3297) ∨ (¬ p 4035) ∨ (¬ p 4456) ∨ (¬ p 5063) :=
  ElevenRUP.step50550 (p 2027) (p 3005) (p 3146) (p 3297) (p 4035) (p 4456) (p 5063) (derived40810 p h) (h 23482)

theorem derived50551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2957) ∨ (¬ p 3646) ∨ (¬ p 4315) ∨ (¬ p 4333) ∨ (¬ p 4558) :=
  ElevenRUP.step50551 (p 2027) (p 2685) (p 2957) (p 3646) (p 4315) (p 4333) (p 4558) (derived40810 p h) (h 23483)

theorem derived50552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3591) ∨ (¬ p 3957) ∨ (¬ p 4558) :=
  ElevenRUP.step50552 (p 2027) (p 2210) (p 2891) (p 3591) (p 3957) (p 4558) (derived40810 p h) (h 23484)

theorem derived50553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 2850) ∨ (¬ p 4796) ∨ (¬ p 4909) :=
  ElevenRUP.step50553 (p 2027) (p 2427) (p 2598) (p 2753) (p 2850) (p 4796) (p 4909) (derived40810 p h) (h 23485)

theorem derived50555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3755) ∨ (¬ p 4195) ∨ (¬ p 4367) ∨ (¬ p 5249) ∨ (¬ p 5717) :=
  ElevenRUP.step50555 (p 2027) (p 3755) (p 4195) (p 4367) (p 5249) (p 5717) (derived40810 p h) (h 23487)

theorem derived50556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2753) ∨ (¬ p 3016) ∨ (¬ p 3486) ∨ (¬ p 3564) ∨ (¬ p 3570) ∨ (¬ p 4117) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4877) :=
  ElevenRUP.step50556 (p 2027) (p 2651) (p 2753) (p 3016) (p 3486) (p 3564) (p 3570) (p 4117) (p 4330) (p 4348) (p 4877) (derived40810 p h) (h 23488)

theorem derived50557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2749) ∨ (¬ p 3016) ∨ (¬ p 3266) ∨ (¬ p 3564) ∨ (¬ p 3645) ∨ (¬ p 4120) ∨ (¬ p 4322) ∨ (¬ p 4330) ∨ (¬ p 4335) ∨ (¬ p 4877) :=
  ElevenRUP.step50557 (p 2027) (p 2246) (p 2651) (p 2749) (p 3016) (p 3266) (p 3564) (p 3645) (p 4120) (p 4322) (p 4330) (p 4335) (p 4877) (derived40810 p h) (h 23489)

theorem derived50558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (¬ p 3547) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4501) :=
  ElevenRUP.step50558 (p 2027) (p 3399) (p 3547) (p 3591) (p 3923) (p 4501) (derived40810 p h) (h 23490)

theorem derived50560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3550) ∨ (¬ p 3568) ∨ (¬ p 3570) ∨ (¬ p 4556) :=
  ElevenRUP.step50560 (p 2027) (p 2668) (p 3550) (p 3568) (p 3570) (p 4556) (derived40810 p h) (h 23492)

theorem derived50562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3136) ∨ (¬ p 3540) ∨ (¬ p 4241) ∨ (¬ p 4644) :=
  ElevenRUP.step50562 (p 2027) (p 2662) (p 2810) (p 3136) (p 3540) (p 4241) (p 4644) (derived40810 p h) (h 23495)

theorem derived50563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2427) ∨ (¬ p 3425) ∨ (¬ p 4169) ∨ (¬ p 4882) :=
  ElevenRUP.step50563 (p 2027) (p 2132) (p 2427) (p 3425) (p 4169) (p 4882) (derived40810 p h) (h 23496)

theorem derived50565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3540) ∨ (¬ p 3914) ∨ (¬ p 4278) ∨ (¬ p 4381) ∨ (¬ p 5193) ∨ (¬ p 5250) :=
  ElevenRUP.step50565 (p 2027) (p 2608) (p 2753) (p 2774) (p 3540) (p 3914) (p 4278) (p 4381) (p 5193) (p 5250) (derived40810 p h) (h 23498)

theorem derived50566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2475) ∨ (¬ p 3998) ∨ (¬ p 4196) ∨ (¬ p 4432) ∨ (¬ p 4501) ∨ (¬ p 5600) :=
  ElevenRUP.step50566 (p 2027) (p 2295) (p 2475) (p 3998) (p 4196) (p 4432) (p 4501) (p 5600) (derived40810 p h) (h 23499)

theorem derived50567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2662) ∨ (¬ p 2810) ∨ (¬ p 3556) ∨ (¬ p 3904) ∨ (¬ p 4110) :=
  ElevenRUP.step50567 (p 1987) (p 2027) (p 2427) (p 2662) (p 2765) (p 2810) (p 3556) (p 3904) (p 4110) (h 2147) (derived40810 p h) (derived40883 p h) (h 23500)

theorem derived50572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3166) ∨ (¬ p 4358) ∨ (¬ p 4417) ∨ (¬ p 4843) :=
  ElevenRUP.step50572 (p 2027) (p 2963) (p 3166) (p 4358) (p 4417) (p 4843) (derived40810 p h) (h 23505)

theorem derived50573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2663) ∨ (¬ p 2952) ∨ (¬ p 3355) ∨ (¬ p 3359) ∨ (¬ p 4701) :=
  ElevenRUP.step50573 (p 2027) (p 2663) (p 2952) (p 3355) (p 3359) (p 4701) (derived40810 p h) (h 23506)

theorem derived50574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3027) ∨ (¬ p 3414) ∨ (¬ p 3662) ∨ (¬ p 4701) :=
  ElevenRUP.step50574 (p 2027) (p 2651) (p 3027) (p 3414) (p 3662) (p 4701) (derived40810 p h) (h 23507)

theorem derived50576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3952) ∨ (¬ p 4425) ∨ (¬ p 4952) ∨ (¬ p 5038) ∨ (¬ p 5046) :=
  ElevenRUP.step50576 (p 2027) (p 3506) (p 3952) (p 4425) (p 4952) (p 5038) (p 5046) (derived40810 p h) (h 23510)

theorem derived50577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3212) ∨ (¬ p 3745) ∨ (¬ p 4154) ∨ (¬ p 5046) :=
  ElevenRUP.step50577 (p 2027) (p 2951) (p 2992) (p 3212) (p 3745) (p 4154) (p 5046) (derived40810 p h) (h 23511)

theorem derived50578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2299) ∨ (¬ p 3097) ∨ (¬ p 4156) ∨ (¬ p 4560) :=
  ElevenRUP.step50578 (p 2027) (p 2264) (p 2299) (p 3097) (p 4156) (p 4560) (derived40810 p h) (h 23512)

theorem derived50581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 3222) ∨ (¬ p 3346) ∨ (¬ p 3662) ∨ (¬ p 4281) ∨ (¬ p 4701) :=
  ElevenRUP.step50581 (p 2027) (p 2662) (p 3222) (p 3346) (p 3662) (p 4281) (p 4701) (derived40810 p h) (h 23515)

theorem derived50583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2663) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3363) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3585) ∨ (¬ p 4418) ∨ (¬ p 4668) ∨ (¬ p 4737) :=
  ElevenRUP.step50583 (p 2027) (p 2132) (p 2663) (p 2891) (p 3246) (p 3363) (p 3414) (p 3553) (p 3585) (p 4418) (p 4668) (p 4737) (derived40810 p h) (h 23518)

theorem derived50585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 2427) ∨ (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 4558) ∨ (¬ p 4607) :=
  ElevenRUP.step50585 (p 2027) (p 2190) (p 2427) (p 2534) (p 3146) (p 4558) (p 4607) (derived40810 p h) (h 23520)

theorem derived50587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2761) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3346) ∨ (¬ p 4425) ∨ (¬ p 4621) ∨ (¬ p 4729) :=
  ElevenRUP.step50587 (p 2027) (p 2696) (p 2761) (p 2797) (p 3323) (p 3346) (p 4425) (p 4621) (p 4729) (derived40810 p h) (h 23522)

theorem derived50588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 4133) ∨ (¬ p 4729) :=
  ElevenRUP.step50588 (p 2027) (p 2459) (p 2476) (p 2534) (p 2668) (p 2696) (p 2797) (p 4133) (p 4729) (derived40810 p h) (h 23523)

theorem derived50589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3347) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 3880) ∨ (¬ p 3954) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5568) :=
  ElevenRUP.step50589 (p 2027) (p 2589) (p 3347) (p 3707) (p 3830) (p 3880) (p 3954) (p 5123) (p 5216) (p 5568) (derived40810 p h) (h 23524)

theorem derived50590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 3545) ∨ (¬ p 3817) ∨ (¬ p 3954) ∨ (¬ p 4796) :=
  ElevenRUP.step50590 (p 2027) (p 3516) (p 3545) (p 3817) (p 3954) (p 4796) (derived40810 p h) (h 23525)

theorem derived50591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3347) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 3954) ∨ (¬ p 3956) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5580) :=
  ElevenRUP.step50591 (p 2027) (p 2579) (p 3347) (p 3707) (p 3830) (p 3954) (p 3956) (p 5123) (p 5216) (p 5580) (derived40810 p h) (h 23526)

theorem derived50598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 3506) ∨ (¬ p 3846) ∨ (¬ p 4321) ∨ (¬ p 5008) ∨ (¬ p 5111) :=
  ElevenRUP.step50598 (p 2027) (p 2727) (p 3506) (p 3846) (p 4321) (p 5008) (p 5111) (derived40810 p h) (h 23533)

theorem derived50600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3362) ∨ (¬ p 3365) ∨ (¬ p 3758) ∨ (¬ p 4399) ∨ (¬ p 5052) :=
  ElevenRUP.step50600 (p 2027) (p 2156) (p 3362) (p 3365) (p 3758) (p 4399) (p 5052) (derived40810 p h) (h 23535)

theorem derived50608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3309) ∨ (¬ p 3957) ∨ (¬ p 4120) ∨ (¬ p 4501) ∨ (¬ p 4506) :=
  ElevenRUP.step50608 (p 2027) (p 2156) (p 3309) (p 3957) (p 4120) (p 4501) (p 4506) (derived40810 p h) (h 23544)

theorem derived50609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2780) ∨ (¬ p 2870) ∨ (¬ p 3096) ∨ (¬ p 4342) ∨ (¬ p 4558) :=
  ElevenRUP.step50609 (p 2027) (p 2132) (p 2780) (p 2870) (p 3096) (p 4342) (p 4558) (derived40810 p h) (h 23545)

theorem derived50614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3246) ∨ (¬ p 3872) ∨ (¬ p 4136) ∨ (¬ p 4324) ∨ (¬ p 4509) :=
  ElevenRUP.step50614 (p 2027) (p 2619) (p 3246) (p 3872) (p 4136) (p 4324) (p 4509) (derived40810 p h) (h 23551)

theorem derived50615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3238) ∨ (¬ p 3695) ∨ (¬ p 3954) ∨ (¬ p 4243) ∨ (¬ p 5216) :=
  ElevenRUP.step50615 (p 2027) (p 2210) (p 3238) (p 3695) (p 3954) (p 4243) (p 5216) (derived40810 p h) (h 23552)

theorem derived50616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 4228) ∨ (¬ p 4278) ∨ (¬ p 4381) ∨ (¬ p 5216) ∨ (¬ p 5250) :=
  ElevenRUP.step50616 (p 2027) (p 2696) (p 2753) (p 2797) (p 3347) (p 3540) (p 4228) (p 4278) (p 4381) (p 5216) (p 5250) (derived40810 p h) (h 23553)

theorem derived50617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 4877) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step50617 (p 2027) (p 2427) (p 2696) (p 2753) (p 3005) (p 3256) (p 3556) (p 3645) (p 4877) (p 4948) (p 5059) (derived40810 p h) (h 23554)

theorem derived50619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2870) ∨ (¬ p 4385) ∨ (¬ p 4387) ∨ (¬ p 4647) ∨ (¬ p 5358) :=
  ElevenRUP.step50619 (p 2027) (p 2417) (p 2870) (p 4385) (p 4387) (p 4647) (p 5358) (derived40810 p h) (h 23556)

theorem derived50620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 2911) ∨ (¬ p 3323) ∨ (¬ p 3546) ∨ (¬ p 3551) ∨ (¬ p 4278) ∨ (¬ p 4621) ∨ (¬ p 4796) :=
  ElevenRUP.step50620 (p 2027) (p 2696) (p 2753) (p 2797) (p 2911) (p 3323) (p 3546) (p 3551) (p 4278) (p 4621) (p 4796) (derived40810 p h) (h 23557)

theorem derived50621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 5216) :=
  ElevenRUP.step50621 (p 2027) (p 2696) (p 2753) (p 2797) (p 3323) (p 3347) (p 3540) (p 3644) (p 4330) (p 4348) (p 5216) (derived40810 p h) (h 23558)

theorem derived50622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 3645) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4877) :=
  ElevenRUP.step50622 (p 2027) (p 2696) (p 2753) (p 2797) (p 3323) (p 3556) (p 3570) (p 3645) (p 4330) (p 4348) (p 4877) (derived40810 p h) (h 23559)

theorem derived50623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 2881) ∨ (¬ p 3323) ∨ (¬ p 3551) ∨ (¬ p 3690) ∨ (¬ p 4621) ∨ (¬ p 5260) :=
  ElevenRUP.step50623 (p 2027) (p 2696) (p 2797) (p 2881) (p 3323) (p 3551) (p 3690) (p 4621) (p 5260) (derived40810 p h) (h 23560)

theorem derived50624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3506) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 3755) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5558) :=
  ElevenRUP.step50624 (p 2027) (p 2696) (p 2753) (p 3347) (p 3506) (p 3540) (p 3644) (p 3755) (p 5123) (p 5216) (p 5558) (derived40810 p h) (h 23562)

theorem derived50625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3319) ∨ (¬ p 3946) ∨ (¬ p 4869) ∨ (¬ p 4877) ∨ (¬ p 5015) :=
  ElevenRUP.step50625 (p 2027) (p 2210) (p 3319) (p 3946) (p 4869) (p 4877) (p 5015) (derived40810 p h) (h 23563)

theorem derived50626 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3266) ∨ (¬ p 3917) ∨ (¬ p 3955) ∨ (¬ p 4191) :=
  ElevenRUP.step50626 (p 1975) (p 2027) (p 2766) (p 2819) (p 3266) (p 3917) (p 3955) (p 4191) (h 2135) (derived40810 p h) (derived40884 p h) (h 23564)

theorem derived50627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3093) ∨ (¬ p 3922) ∨ (¬ p 4111) ∨ (¬ p 4975) :=
  ElevenRUP.step50627 (p 2027) (p 2247) (p 3093) (p 3922) (p 4111) (p 4975) (derived40810 p h) (h 23565)

theorem derived50628 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2891) ∨ (¬ p 3371) ∨ (¬ p 4244) ∨ (¬ p 4734) :=
  ElevenRUP.step50628 (p 2027) (p 2138) (p 2891) (p 3371) (p 4244) (p 4734) (derived40810 p h) (h 23566)

theorem derived50632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 4118) ∨ (¬ p 4330) ∨ (¬ p 4360) ∨ (¬ p 4733) :=
  ElevenRUP.step50632 (p 2027) (p 2247) (p 2598) (p 3422) (p 3564) (p 4118) (p 4330) (p 4360) (p 4733) (derived40810 p h) (h 23570)

theorem derived50633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2247) ∨ (¬ p 2396) ∨ (¬ p 2774) ∨ (¬ p 3662) ∨ (¬ p 3951) ∨ (¬ p 4208) ∨ (¬ p 4733) :=
  ElevenRUP.step50633 (p 2027) (p 2122) (p 2247) (p 2396) (p 2774) (p 3662) (p 3951) (p 4208) (p 4733) (derived40810 p h) (h 23571)

theorem derived50635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 2996) ∨ (¬ p 3947) ∨ (¬ p 4666) ∨ (¬ p 4733) :=
  ElevenRUP.step50635 (p 2027) (p 2132) (p 2247) (p 2870) (p 2881) (p 2996) (p 3947) (p 4666) (p 4733) (derived40810 p h) (h 23573)

theorem derived50636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 3027) ∨ (¬ p 3097) ∨ (¬ p 4066) ∨ (¬ p 4154) ∨ (¬ p 4560) :=
  ElevenRUP.step50636 (p 2027) (p 2318) (p 3027) (p 3097) (p 4066) (p 4154) (p 4560) (derived40810 p h) (h 23574)

theorem derived50637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2307) ∨ (¬ p 2363) ∨ (¬ p 3325) ∨ (¬ p 3497) ∨ (¬ p 3662) ∨ (¬ p 4348) ∨ (¬ p 4905) ∨ (¬ p 5017) :=
  ElevenRUP.step50637 (p 2027) (p 2247) (p 2307) (p 2363) (p 3325) (p 3497) (p 3662) (p 4348) (p 4905) (p 5017) (derived40810 p h) (h 23575)

theorem derived50638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2264) ∨ (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 3031) ∨ (¬ p 3548) ∨ (¬ p 4361) ∨ (¬ p 4733) :=
  ElevenRUP.step50638 (p 2027) (p 2132) (p 2247) (p 2264) (p 2274) (p 2860) (p 3031) (p 3548) (p 4361) (p 4733) (derived40810 p h) (h 23576)

theorem derived50639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3548) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4366) ∨ (¬ p 4733) :=
  ElevenRUP.step50639 (p 2027) (p 2132) (p 2860) (p 3125) (p 3548) (p 4330) (p 4348) (p 4366) (p 4733) (derived40810 p h) (h 23578)

theorem derived50641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3548) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4366) ∨ (¬ p 4733) :=
  ElevenRUP.step50641 (p 2027) (p 2598) (p 3422) (p 3548) (p 3564) (p 4330) (p 4348) (p 4366) (p 4733) (derived40810 p h) (h 23580)

theorem derived50643 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 2982) ∨ (¬ p 3548) ∨ (¬ p 4348) ∨ (¬ p 4366) ∨ (¬ p 4450) ∨ (¬ p 4733) :=
  ElevenRUP.step50643 (p 2027) (p 2598) (p 2850) (p 2982) (p 3548) (p 4348) (p 4366) (p 4450) (p 4733) (derived40810 p h) (h 23584)

theorem derived50644 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2230) ∨ (¬ p 3201) ∨ (¬ p 3362) ∨ (¬ p 3548) ∨ (¬ p 3684) ∨ (¬ p 4276) ∨ (¬ p 4366) ∨ (¬ p 4733) :=
  ElevenRUP.step50644 (p 2027) (p 2177) (p 2230) (p 3201) (p 3362) (p 3548) (p 3684) (p 4276) (p 4366) (p 4733) (derived40810 p h) (h 23585)

theorem derived50647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3551) ∨ (¬ p 4984) :=
  ElevenRUP.step50647 (p 2027) (p 2140) (p 2870) (p 2881) (p 3551) (p 4984) (derived40810 p h) (h 23589)

theorem derived50649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2383) ∨ (¬ p 3324) ∨ (¬ p 3987) ∨ (¬ p 4111) ∨ (¬ p 4975) :=
  ElevenRUP.step50649 (p 2027) (p 2246) (p 2383) (p 3324) (p 3987) (p 4111) (p 4975) (derived40810 p h) (h 23591)

theorem derived50650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2387) ∨ (¬ p 2427) ∨ (¬ p 4031) ∨ (¬ p 4198) ∨ (¬ p 4558) :=
  ElevenRUP.step50650 (p 2027) (p 2187) (p 2387) (p 2427) (p 4031) (p 4198) (p 4558) (derived40810 p h) (h 23592)

theorem derived50652 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2659) ∨ (¬ p 3027) ∨ (¬ p 3540) ∨ (¬ p 3579) ∨ (¬ p 4111) :=
  ElevenRUP.step50652 (p 2027) (p 2659) (p 3027) (p 3540) (p 3579) (p 4111) (derived40810 p h) (h 23594)

theorem derived50653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3365) ∨ (¬ p 3367) ∨ (¬ p 3568) ∨ (¬ p 3644) ∨ (¬ p 3759) ∨ (¬ p 4195) ∨ (¬ p 4276) ∨ (¬ p 4734) ∨ (¬ p 5201) :=
  ElevenRUP.step50653 (p 2027) (p 2341) (p 3365) (p 3367) (p 3568) (p 3644) (p 3759) (p 4195) (p 4276) (p 4734) (p 5201) (derived40810 p h) (h 23595)

theorem derived50654 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 4111) ∨ (¬ p 4320) ∨ (¬ p 4365) ∨ (¬ p 4704) :=
  ElevenRUP.step50654 (p 2027) (p 2891) (p 4111) (p 4320) (p 4365) (p 4704) (derived40810 p h) (h 23596)

theorem derived50655 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2667) ∨ (¬ p 2810) ∨ (¬ p 2819) ∨ (¬ p 4426) ∨ (¬ p 4975) :=
  ElevenRUP.step50655 (p 2027) (p 2387) (p 2667) (p 2810) (p 2819) (p 4426) (p 4975) (derived40810 p h) (h 23597)

theorem derived50656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2192) ∨ (¬ p 3541) ∨ (¬ p 3758) ∨ (¬ p 3948) ∨ (¬ p 4734) :=
  ElevenRUP.step50656 (p 2027) (p 2138) (p 2192) (p 3541) (p 3758) (p 3948) (p 4734) (derived40810 p h) (h 23598)

theorem derived50658 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2331) ∨ (¬ p 2950) ∨ (¬ p 3948) ∨ (¬ p 4116) ∨ (¬ p 4120) ∨ (¬ p 4975) :=
  ElevenRUP.step50658 (p 2027) (p 2166) (p 2331) (p 2950) (p 3948) (p 4116) (p 4120) (p 4975) (derived40810 p h) (h 23600)

theorem derived50659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2667) ∨ (¬ p 2810) ∨ (¬ p 4426) ∨ (¬ p 4975) :=
  ElevenRUP.step50659 (p 2027) (p 2122) (p 2313) (p 2667) (p 2810) (p 4426) (p 4975) (derived40810 p h) (h 23601)

theorem derived50665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2230) ∨ (¬ p 3367) ∨ (¬ p 3698) ∨ (¬ p 3759) ∨ (¬ p 4734) :=
  ElevenRUP.step50665 (p 2027) (p 2138) (p 2230) (p 3367) (p 3698) (p 3759) (p 4734) (derived40810 p h) (h 23610)

theorem derived50666 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2911) ∨ (¬ p 3367) ∨ (¬ p 3389) ∨ (¬ p 3690) ∨ (¬ p 3759) ∨ (¬ p 4244) ∨ (¬ p 4666) ∨ (¬ p 4734) :=
  ElevenRUP.step50666 (p 2027) (p 2138) (p 2911) (p 3367) (p 3389) (p 3690) (p 3759) (p 4244) (p 4666) (p 4734) (derived40810 p h) (h 23611)

theorem derived50667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2191) ∨ (¬ p 2417) ∨ (¬ p 3367) ∨ (¬ p 3389) ∨ (¬ p 3692) ∨ (¬ p 3759) ∨ (¬ p 3950) ∨ (¬ p 4243) ∨ (¬ p 4734) :=
  ElevenRUP.step50667 (p 2027) (p 2138) (p 2191) (p 2417) (p 3367) (p 3389) (p 3692) (p 3759) (p 3950) (p 4243) (p 4734) (derived40810 p h) (h 23612)

theorem derived50668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2668) ∨ (¬ p 2737) ∨ (¬ p 2797) ∨ (¬ p 3425) ∨ (¬ p 3544) ∨ (¬ p 3576) ∨ (¬ p 4133) ∨ (¬ p 4261) ∨ (¬ p 4734) :=
  ElevenRUP.step50668 (p 2027) (p 2459) (p 2668) (p 2737) (p 2797) (p 3425) (p 3544) (p 3576) (p 4133) (p 4261) (p 4734) (derived40810 p h) (h 23613)

theorem derived50670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2911) ∨ (¬ p 3097) ∨ (¬ p 3367) ∨ (¬ p 3516) ∨ (¬ p 3759) ∨ (¬ p 4173) ∨ (¬ p 4243) ∨ (¬ p 4278) ∨ (¬ p 4734) ∨ (¬ p 5201) :=
  ElevenRUP.step50670 (p 1998) (p 2027) (p 2138) (p 2911) (p 2997) (p 3097) (p 3367) (p 3516) (p 3759) (p 4173) (p 4243) (p 4278) (p 4734) (p 5201) (h 2158) (derived40810 p h) (derived40890 p h) (h 23615)

theorem derived50672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3097) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 4560) :=
  ElevenRUP.step50672 (p 2027) (p 2668) (p 3097) (p 3309) (p 3923) (p 4560) (derived40810 p h) (h 23618)

theorem derived50673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3055) ∨ (¬ p 3541) ∨ (¬ p 3876) ∨ (¬ p 4734) :=
  ElevenRUP.step50673 (p 2027) (p 2922) (p 3055) (p 3541) (p 3876) (p 4734) (derived40810 p h) (h 23619)

theorem derived50676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2449) ∨ (¬ p 2839) ∨ (¬ p 3425) ∨ (¬ p 4324) ∨ (¬ p 4361) ∨ (¬ p 4734) :=
  ElevenRUP.step50676 (p 2027) (p 2137) (p 2156) (p 2274) (p 2449) (p 2839) (p 3425) (p 4324) (p 4361) (p 4734) (derived40810 p h) (h 23624)

theorem derived50680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 3172) ∨ (¬ p 3189) ∨ (¬ p 3568) ∨ (¬ p 4154) :=
  ElevenRUP.step50680 (p 1984) (p 2027) (p 2245) (p 2997) (p 3172) (p 3189) (p 3568) (p 4154) (h 2144) (derived40810 p h) (derived40890 p h) (h 23630)

theorem derived50681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 3324) ∨ (¬ p 4111) ∨ (¬ p 4759) ∨ (¬ p 4975) :=
  ElevenRUP.step50681 (p 2027) (p 3063) (p 3324) (p 4111) (p 4759) (p 4975) (derived40810 p h) (h 23631)

theorem derived50684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2476) ∨ (¬ p 3189) ∨ (¬ p 4111) ∨ (¬ p 4346) :=
  ElevenRUP.step50684 (p 1997) (p 2027) (p 2230) (p 2476) (p 2545) (p 3189) (p 4111) (p 4346) (h 2157) (derived40810 p h) (derived40876 p h) (h 23635)

theorem derived50689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2191) ∨ (¬ p 2396) ∨ (¬ p 2774) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 4733) :=
  ElevenRUP.step50689 (p 2027) (p 2122) (p 2191) (p 2396) (p 2774) (p 3555) (p 3692) (p 3950) (p 4733) (derived40810 p h) (h 23640)

theorem derived50690 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3367) ∨ (¬ p 3540) ∨ (¬ p 3905) ∨ (¬ p 4734) :=
  ElevenRUP.step50690 (p 2027) (p 3201) (p 3367) (p 3540) (p 3905) (p 4734) (derived40810 p h) (h 23641)

theorem derived50691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2284) ∨ (¬ p 2780) ∨ (¬ p 4428) ∨ (¬ p 4906) :=
  ElevenRUP.step50691 (p 2027) (p 2132) (p 2284) (p 2780) (p 4428) (p 4906) (derived40810 p h) (h 23642)

theorem derived50693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2748) ∨ (¬ p 2839) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 4734) :=
  ElevenRUP.step50693 (p 2027) (p 2137) (p 2748) (p 2839) (p 3051) (p 3246) (p 3365) (p 3950) (p 4118) (p 4360) (p 4734) (derived40810 p h) (h 23646)

theorem derived50696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2573) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 4360) ∨ (¬ p 5123) ∨ (¬ p 5190) ∨ (¬ p 5600) :=
  ElevenRUP.step50696 (p 2027) (p 2247) (p 2573) (p 3461) (p 3564) (p 4360) (p 5123) (p 5190) (p 5600) (derived40810 p h) (h 23651)

theorem derived50697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3434) ∨ (¬ p 4382) ∨ (¬ p 4898) ∨ (¬ p 4948) :=
  ElevenRUP.step50697 (p 2027) (p 2427) (p 3434) (p 4382) (p 4898) (p 4948) (derived40810 p h) (h 23652)

theorem derived50699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3583) ∨ (¬ p 3951) ∨ (¬ p 3954) ∨ (¬ p 4385) ∨ (¬ p 5190) :=
  ElevenRUP.step50699 (p 2027) (p 2396) (p 2553) (p 2573) (p 3583) (p 3951) (p 3954) (p 4385) (p 5190) (derived40810 p h) (h 23655)

theorem derived50701 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2247) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2996) ∨ (¬ p 3947) ∨ (¬ p 4666) ∨ (¬ p 5190) :=
  ElevenRUP.step50701 (p 2027) (p 2177) (p 2247) (p 2553) (p 2573) (p 2996) (p 3947) (p 4666) (p 5190) (derived40810 p h) (h 23657)

theorem derived50702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2630) ∨ (¬ p 2656) :=
  ElevenRUP.step50702 (p 1998) (p 2027) (p 2177) (p 2553) (p 2573) (p 2622) (p 2630) (p 2656) (h 2158) (derived40810 p h) (derived40878 p h) (h 23658)

theorem derived50704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3172) ∨ (¬ p 3189) ∨ (¬ p 4111) ∨ (¬ p 4787) :=
  ElevenRUP.step50704 (p 2027) (p 2630) (p 3172) (p 3189) (p 4111) (p 4787) (derived40810 p h) (h 23660)

theorem derived50706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 4187) ∨ (p 4620) ∨ (¬ p 5190) :=
  ElevenRUP.step50706 (p 2000) (p 2247) (p 2688) (p 4187) (p 4620) (p 5190) (h 2160) (derived40880 p h) (h 23662)

theorem derived50707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2659) ∨ (¬ p 2911) ∨ (¬ p 3551) ∨ (¬ p 5197) :=
  ElevenRUP.step50707 (p 2027) (p 2437) (p 2659) (p 2911) (p 3551) (p 5197) (derived40810 p h) (h 23663)

theorem derived50710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2641) ∨ (¬ p 2963) ∨ (¬ p 3402) ∨ (¬ p 4116) ∨ (¬ p 4787) :=
  ElevenRUP.step50710 (p 2027) (p 2630) (p 2641) (p 2963) (p 3402) (p 4116) (p 4787) (derived40810 p h) (h 23666)

theorem derived50711 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2579) ∨ (¬ p 2630) ∨ (¬ p 2655) ∨ (¬ p 4116) ∨ (¬ p 4787) :=
  ElevenRUP.step50711 (p 2027) (p 2493) (p 2579) (p 2630) (p 2655) (p 4116) (p 4787) (derived40810 p h) (h 23667)

theorem derived50713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3483) ∨ (¬ p 3922) ∨ (¬ p 4026) ∨ (¬ p 4426) ∨ (¬ p 4787) :=
  ElevenRUP.step50713 (p 2027) (p 2963) (p 3483) (p 3922) (p 4026) (p 4426) (p 4787) (derived40810 p h) (h 23669)

theorem derived50719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3989) ∨ (¬ p 4154) ∨ (¬ p 4417) ∨ (¬ p 4560) :=
  ElevenRUP.step50719 (p 2027) (p 3189) (p 3989) (p 4154) (p 4417) (p 4560) (derived40810 p h) (h 23676)

theorem derived50720 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2641) ∨ (¬ p 3567) ∨ (¬ p 3584) ∨ (¬ p 4111) ∨ (¬ p 4750) :=
  ElevenRUP.step50720 (p 2027) (p 2386) (p 2641) (p 3567) (p 3584) (p 4111) (p 4750) (derived40810 p h) (h 23677)

theorem derived50721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step50721 (p 2027) (p 2132) (p 2870) (p 3246) (p 3591) (p 3923) (p 3950) (p 4347) (p 4733) (derived40810 p h) (h 23678)

theorem derived50723 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2331) ∨ (¬ p 3551) ∨ (¬ p 3580) ∨ (¬ p 4849) ∨ (¬ p 4975) :=
  ElevenRUP.step50723 (p 2027) (p 2264) (p 2331) (p 3551) (p 3580) (p 4849) (p 4975) (derived40810 p h) (h 23680)

theorem derived50724 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step50724 (p 2027) (p 2417) (p 2598) (p 3201) (p 3591) (p 3923) (p 3950) (p 4347) (p 4733) (derived40810 p h) (h 23681)

theorem derived50726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3690) ∨ (¬ p 4666) ∨ (¬ p 4733) :=
  ElevenRUP.step50726 (p 2027) (p 2598) (p 2911) (p 3201) (p 3486) (p 3555) (p 3690) (p 4666) (p 4733) (derived40810 p h) (h 23683)

theorem derived50727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 2881) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step50727 (p 1998) (p 2027) (p 2427) (p 2598) (p 2766) (p 2850) (p 2881) (p 3591) (p 3923) (p 4347) (p 4733) (h 2158) (derived40810 p h) (derived40884 p h) (h 23684)

theorem derived50728 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 4256) ∨ (¬ p 4687) ∨ (¬ p 4814) :=
  ElevenRUP.step50728 (p 2027) (p 3449) (p 3452) (p 4256) (p 4687) (p 4814) (derived40810 p h) (h 23686)

theorem derived50729 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2850) ∨ (¬ p 3876) ∨ (¬ p 4001) ∨ (¬ p 4555) :=
  ElevenRUP.step50729 (p 2027) (p 2563) (p 2850) (p 3876) (p 4001) (p 4555) (derived40810 p h) (h 23687)

theorem derived50731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2573) ∨ (¬ p 2589) ∨ (¬ p 3584) ∨ (¬ p 4750) :=
  ElevenRUP.step50731 (p 2027) (p 2542) (p 2573) (p 2589) (p 3584) (p 4750) (derived40810 p h) (h 23689)

theorem derived50732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2505) ∨ (¬ p 3063) ∨ (¬ p 3584) ∨ (¬ p 3956) ∨ (¬ p 5217) :=
  ElevenRUP.step50732 (p 2027) (p 2505) (p 3063) (p 3584) (p 3956) (p 5217) (derived40810 p h) (h 23690)

theorem derived50734 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 3580) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4750) :=
  ElevenRUP.step50734 (p 2027) (p 2449) (p 3580) (p 3876) (p 4278) (p 4750) (derived40810 p h) (h 23692)

theorem derived50737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3370) ∨ (¬ p 3413) ∨ (¬ p 3684) ∨ (¬ p 4031) ∨ (¬ p 4173) ∨ (¬ p 4750) :=
  ElevenRUP.step50737 (p 2027) (p 2284) (p 3370) (p 3413) (p 3684) (p 4031) (p 4173) (p 4750) (derived40810 p h) (h 23695)

theorem derived50738 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3569) ∨ (¬ p 3646) ∨ (¬ p 3684) ∨ (¬ p 4031) ∨ (¬ p 4558) :=
  ElevenRUP.step50738 (p 2027) (p 3201) (p 3569) (p 3646) (p 3684) (p 4031) (p 4558) (derived40810 p h) (h 23696)

theorem derived50739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2437) ∨ (¬ p 3540) ∨ (¬ p 3684) ∨ (¬ p 4750) :=
  ElevenRUP.step50739 (p 2027) (p 2230) (p 2437) (p 3540) (p 3684) (p 4750) (derived40810 p h) (h 23697)

theorem derived50740 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3413) ∨ (¬ p 3574) ∨ (¬ p 4272) ∨ (¬ p 4715) ∨ (¬ p 5433) :=
  ElevenRUP.step50740 (p 2027) (p 3413) (p 3574) (p 4272) (p 4715) (p 5433) (derived40810 p h) (h 23699)

theorem derived50741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2427) ∨ (¬ p 3486) ∨ (¬ p 4120) ∨ (¬ p 4533) :=
  ElevenRUP.step50741 (p 2027) (p 2166) (p 2427) (p 3486) (p 4120) (p 4533) (derived40810 p h) (h 23700)

theorem derived50742 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 3690) ∨ (¬ p 4204) ∨ (¬ p 4560) :=
  ElevenRUP.step50742 (p 2027) (p 2295) (p 2396) (p 3690) (p 4204) (p 4560) (derived40810 p h) (h 23701)

theorem derived50745 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3581) ∨ (¬ p 3644) ∨ (¬ p 4203) ∨ (¬ p 4363) ∨ (¬ p 4431) ∨ (¬ p 5043) :=
  ElevenRUP.step50745 (p 2027) (p 3527) (p 3581) (p 3644) (p 4203) (p 4363) (p 4431) (p 5043) (derived40810 p h) (h 23704)

theorem derived50746 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2982) ∨ (¬ p 3051) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4235) ∨ (¬ p 4397) ∨ (¬ p 4399) ∨ (¬ p 5190) :=
  ElevenRUP.step50746 (p 2027) (p 2247) (p 2982) (p 3051) (p 4037) (p 4154) (p 4235) (p 4397) (p 4399) (p 5190) (derived40810 p h) (h 23705)

theorem derived50748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 4244) ∨ (¬ p 4283) ∨ (¬ p 4431) ∨ (¬ p 4878) :=
  ElevenRUP.step50748 (p 2027) (p 3527) (p 3551) (p 4244) (p 4283) (p 4431) (p 4878) (derived40810 p h) (h 23707)

theorem derived50750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 3136) ∨ (¬ p 4117) :=
  ElevenRUP.step50750 (p 1990) (p 2027) (p 2284) (p 2611) (p 2651) (p 2810) (p 3136) (p 4117) (h 2150) (derived40810 p h) (derived40877 p h) (h 23712)

theorem derived50751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2891) ∨ (¬ p 3695) ∨ (¬ p 3948) ∨ (¬ p 4244) ∨ (¬ p 4814) :=
  ElevenRUP.step50751 (p 2027) (p 2440) (p 2891) (p 3695) (p 3948) (p 4244) (p 4814) (derived40810 p h) (h 23713)

theorem derived50754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2505) ∨ (¬ p 2785) ∨ (¬ p 3309) ∨ (¬ p 3574) ∨ (¬ p 4390) ∨ (¬ p 4814) :=
  ElevenRUP.step50754 (p 2027) (p 2313) (p 2505) (p 2785) (p 3309) (p 3574) (p 4390) (p 4814) (derived40810 p h) (h 23716)

theorem derived50755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3690) ∨ (¬ p 4666) ∨ (¬ p 4733) :=
  ElevenRUP.step50755 (p 2027) (p 2264) (p 2685) (p 2696) (p 3486) (p 3555) (p 3690) (p 4666) (p 4733) (derived40810 p h) (h 23717)

theorem derived50757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 4733) :=
  ElevenRUP.step50757 (p 2027) (p 2191) (p 2449) (p 2685) (p 2696) (p 3555) (p 3692) (p 3950) (p 4733) (derived40810 p h) (h 23719)

theorem derived50758 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4347) ∨ (¬ p 4450) ∨ (¬ p 4733) :=
  ElevenRUP.step50758 (p 2027) (p 2696) (p 3115) (p 3136) (p 3591) (p 3923) (p 4347) (p 4450) (p 4733) (derived40810 p h) (h 23720)

theorem derived50759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3370) ∨ (¬ p 3684) ∨ (¬ p 3742) ∨ (¬ p 3948) ∨ (¬ p 4031) ∨ (¬ p 4814) :=
  ElevenRUP.step50759 (p 2027) (p 3201) (p 3370) (p 3684) (p 3742) (p 3948) (p 4031) (p 4814) (derived40810 p h) (h 23721)

theorem derived50760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3347) ∨ (¬ p 4228) ∨ (¬ p 4444) ∨ (¬ p 5216) ∨ (¬ p 5250) :=
  ElevenRUP.step50760 (p 2027) (p 2476) (p 2534) (p 2696) (p 2753) (p 2797) (p 3347) (p 4228) (p 4444) (p 5216) (p 5250) (derived40810 p h) (h 23722)

theorem derived50761 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3758) ∨ (¬ p 4053) ∨ (¬ p 4338) ∨ (¬ p 4393) ∨ (¬ p 4878) :=
  ElevenRUP.step50761 (p 2027) (p 3758) (p 4053) (p 4338) (p 4393) (p 4878) (derived40810 p h) (h 23723)

theorem derived50763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3555) ∨ (¬ p 3931) ∨ (¬ p 4322) ∨ (¬ p 4363) ∨ (¬ p 4733) ∨ (¬ p 4826) :=
  ElevenRUP.step50763 (p 2027) (p 2685) (p 2696) (p 3555) (p 3931) (p 4322) (p 4363) (p 4733) (p 4826) (derived40810 p h) (h 23725)

theorem derived50764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2505) ∨ (¬ p 3309) ∨ (¬ p 3684) ∨ (¬ p 4031) ∨ (¬ p 4198) ∨ (¬ p 5217) :=
  ElevenRUP.step50764 (p 2027) (p 2313) (p 2505) (p 3309) (p 3684) (p 4031) (p 4198) (p 5217) (derived40810 p h) (h 23726)

theorem derived50765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3180) ∨ (¬ p 3266) ∨ (¬ p 4349) ∨ (¬ p 5284) :=
  ElevenRUP.step50765 (p 2027) (p 2088) (p 3180) (p 3266) (p 4349) (p 5284) (derived40810 p h) (h 23727)

theorem derived50766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3548) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4366) ∨ (¬ p 4733) :=
  ElevenRUP.step50766 (p 2027) (p 2696) (p 2797) (p 3323) (p 3548) (p 4330) (p 4348) (p 4366) (p 4733) (derived40810 p h) (h 23728)

theorem derived50768 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 3690) ∨ (¬ p 4228) ∨ (¬ p 4381) ∨ (¬ p 4877) ∨ (¬ p 5250) :=
  ElevenRUP.step50768 (p 2027) (p 2696) (p 2753) (p 2797) (p 3556) (p 3645) (p 3690) (p 4228) (p 4381) (p 4877) (p 5250) (derived40810 p h) (h 23733)

theorem derived50769 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3222) ∨ (¬ p 3346) ∨ (¬ p 3541) ∨ (¬ p 4108) ∨ (¬ p 4877) :=
  ElevenRUP.step50769 (p 2027) (p 2210) (p 3222) (p 3346) (p 3541) (p 4108) (p 4877) (derived40810 p h) (h 23734)

theorem derived50770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2589) ∨ (¬ p 3005) ∨ (¬ p 3570) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4235) ∨ (¬ p 4550) ∨ (¬ p 4729) :=
  ElevenRUP.step50770 (p 2027) (p 2331) (p 2589) (p 3005) (p 3570) (p 4117) (p 4195) (p 4235) (p 4550) (p 4729) (derived40810 p h) (h 23735)

theorem derived50771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3551) ∨ (¬ p 3737) ∨ (¬ p 4348) ∨ (¬ p 4444) ∨ (¬ p 4729) ∨ (¬ p 5197) ∨ (¬ p 5250) :=
  ElevenRUP.step50771 (p 2027) (p 2132) (p 2860) (p 3551) (p 3737) (p 4348) (p 4444) (p 4729) (p 5197) (p 5250) (derived40810 p h) (h 23736)

theorem derived50772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 2911) ∨ (¬ p 3125) ∨ (¬ p 3551) ∨ (¬ p 4278) ∨ (¬ p 4621) ∨ (¬ p 4729) ∨ (¬ p 5197) :=
  ElevenRUP.step50772 (p 2027) (p 2132) (p 2860) (p 2911) (p 3125) (p 3551) (p 4278) (p 4621) (p 4729) (p 5197) (derived40810 p h) (h 23737)

theorem derived50773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4729) :=
  ElevenRUP.step50773 (p 2027) (p 2132) (p 2860) (p 3125) (p 3540) (p 3644) (p 4330) (p 4348) (p 4729) (derived40810 p h) (h 23738)

theorem derived50774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 3256) ∨ (¬ p 3449) ∨ (¬ p 3692) ∨ (¬ p 4288) :=
  ElevenRUP.step50774 (p 2001) (p 2027) (p 2247) (p 2688) (p 3256) (p 3449) (p 3692) (p 4288) (h 2161) (derived40810 p h) (derived40880 p h) (h 23739)

theorem derived50776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2427) ∨ (¬ p 3005) ∨ (¬ p 3556) ∨ (¬ p 3880) ∨ (¬ p 3904) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4729) ∨ (¬ p 5063) :=
  ElevenRUP.step50776 (p 2027) (p 2331) (p 2427) (p 3005) (p 3556) (p 3880) (p 3904) (p 4117) (p 4195) (p 4729) (p 5063) (derived40810 p h) (h 23741)

theorem derived50777 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2533) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3556) ∨ (¬ p 3904) ∨ (¬ p 4117) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4729) ∨ (¬ p 4948) :=
  ElevenRUP.step50777 (p 2027) (p 2427) (p 2533) (p 3166) (p 3256) (p 3556) (p 3904) (p 4117) (p 4134) (p 4347) (p 4729) (p 4948) (derived40810 p h) (h 23742)

theorem derived50780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2589) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3690) ∨ (¬ p 3755) ∨ (¬ p 4117) ∨ (¬ p 4195) ∨ (¬ p 4235) ∨ (¬ p 4658) ∨ (¬ p 5216) :=
  ElevenRUP.step50780 (p 2027) (p 2331) (p 2589) (p 2753) (p 3347) (p 3690) (p 3755) (p 4117) (p 4195) (p 4235) (p 4658) (p 5216) (derived40810 p h) (h 23745)

theorem derived50781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3552) ∨ (¬ p 4501) :=
  ElevenRUP.step50781 (p 2027) (p 2807) (p 2963) (p 3324) (p 3552) (p 4501) (derived40810 p h) (h 23746)

theorem derived50782 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2630) ∨ (¬ p 2963) ∨ (¬ p 3361) ∨ (¬ p 3568) :=
  ElevenRUP.step50782 (p 1994) (p 2027) (p 2299) (p 2630) (p 2633) (p 2963) (p 3361) (p 3568) (h 2154) (derived40810 p h) (derived40879 p h) (h 23747)

theorem derived50783 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3954) ∨ (¬ p 4172) ∨ (¬ p 4173) ∨ (¬ p 4877) :=
  ElevenRUP.step50783 (p 2027) (p 2156) (p 3954) (p 4172) (p 4173) (p 4877) (derived40810 p h) (h 23748)

theorem derived50784 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 3860) ∨ (¬ p 3906) ∨ (¬ p 4507) :=
  ElevenRUP.step50784 (p 2027) (p 2192) (p 2210) (p 3860) (p 3906) (p 4507) (derived40810 p h) (h 23749)

theorem derived50785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3347) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3954) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 5216) :=
  ElevenRUP.step50785 (p 2027) (p 2579) (p 2588) (p 3347) (p 3399) (p 3527) (p 3954) (p 4107) (p 4666) (p 5216) (derived40810 p h) (h 23750)

theorem derived50786 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2373) ∨ (¬ p 3969) ∨ (¬ p 4197) ∨ (¬ p 4198) ∨ (¬ p 4882) ∨ (¬ p 5590) :=
  ElevenRUP.step50786 (p 2027) (p 2143) (p 2373) (p 3969) (p 4197) (p 4198) (p 4882) (p 5590) (derived40810 p h) (h 23751)

theorem derived50790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 3166) ∨ (¬ p 3755) ∨ (¬ p 3877) ∨ (¬ p 4107) ∨ (¬ p 4117) ∨ (¬ p 4658) ∨ (¬ p 4729) :=
  ElevenRUP.step50790 (p 2027) (p 2579) (p 2588) (p 3166) (p 3755) (p 3877) (p 4107) (p 4117) (p 4658) (p 4729) (derived40810 p h) (h 23755)

theorem derived50791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 4695) ∨ (¬ p 5118) :=
  ElevenRUP.step50791 (p 2027) (p 3343) (p 4256) (p 4286) (p 4695) (p 5118) (derived40810 p h) (h 23756)

theorem derived50792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3005) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 3690) ∨ (¬ p 4009) ∨ (¬ p 4381) ∨ (¬ p 4877) ∨ (¬ p 5119) :=
  ElevenRUP.step50792 (p 2027) (p 2696) (p 2753) (p 3005) (p 3556) (p 3645) (p 3690) (p 4009) (p 4381) (p 4877) (p 5119) (derived40810 p h) (h 23757)

theorem derived50793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3083) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 3692) ∨ (¬ p 4119) ∨ (¬ p 4420) ∨ (¬ p 4877) :=
  ElevenRUP.step50793 (p 2027) (p 2459) (p 2630) (p 2696) (p 2753) (p 3083) (p 3556) (p 3645) (p 3692) (p 4119) (p 4420) (p 4877) (derived40810 p h) (h 23758)

theorem derived50794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3097) ∨ (¬ p 3343) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 4107) ∨ (¬ p 4638) ∨ (¬ p 4877) :=
  ElevenRUP.step50794 (p 2027) (p 2630) (p 2696) (p 2753) (p 3097) (p 3343) (p 3645) (p 3646) (p 4107) (p 4638) (p 4877) (derived40810 p h) (h 23759)

theorem derived50795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (¬ p 3097) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3644) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3954) ∨ (¬ p 4107) ∨ (¬ p 4877) :=
  ElevenRUP.step50795 (p 1997) (p 2027) (p 2441) (p 2462) (p 3097) (p 3399) (p 3527) (p 3644) (p 3645) (p 3646) (p 3954) (p 4107) (p 4877) (h 2157) (derived40810 p h) (derived40875 p h) (h 23760)

theorem derived50797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 3083) ∨ (¬ p 3204) ∨ (¬ p 3683) ∨ (¬ p 4024) ∨ (¬ p 4420) ∨ (¬ p 5220) :=
  ElevenRUP.step50797 (p 2027) (p 2299) (p 2313) (p 3083) (p 3204) (p 3683) (p 4024) (p 4420) (p 5220) (derived40810 p h) (h 23762)

theorem derived50798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3570) ∨ (¬ p 3609) ∨ (¬ p 4118) ∨ (¬ p 4235) ∨ (¬ p 4373) ∨ (¬ p 4550) ∨ (¬ p 5216) :=
  ElevenRUP.step50798 (p 2027) (p 2589) (p 2696) (p 2753) (p 3347) (p 3570) (p 3609) (p 4118) (p 4235) (p 4373) (p 4550) (p 5216) (derived40810 p h) (h 23764)

theorem derived50800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3292) ∨ (¬ p 4733) ∨ (¬ p 5111) :=
  ElevenRUP.step50800 (p 2027) (p 2245) (p 2696) (p 3005) (p 3292) (p 4733) (p 5111) (derived40810 p h) (h 23766)

theorem derived50801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3956) ∨ (¬ p 4729) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step50801 (p 2027) (p 2579) (p 2696) (p 3005) (p 3256) (p 3956) (p 4729) (p 5118) (p 5580) (derived40810 p h) (h 23768)

theorem derived50802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2299) ∨ (¬ p 2534) ∨ (¬ p 2753) ∨ (¬ p 3097) ∨ (¬ p 3609) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 4420) ∨ (¬ p 4877) :=
  ElevenRUP.step50802 (p 2027) (p 2098) (p 2299) (p 2534) (p 2753) (p 3097) (p 3609) (p 3645) (p 3646) (p 4420) (p 4877) (derived40810 p h) (h 23769)

theorem derived50803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2749) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3989) ∨ (¬ p 4343) ∨ (¬ p 4877) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step50803 (p 2027) (p 2246) (p 2651) (p 2749) (p 3276) (p 3333) (p 3645) (p 3646) (p 3989) (p 4343) (p 4877) (p 5123) (p 5580) (derived40810 p h) (h 23770)

theorem derived50804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2753) ∨ (¬ p 2810) ∨ (¬ p 3204) ∨ (¬ p 3266) ∨ (¬ p 3755) ∨ (¬ p 3946) ∨ (¬ p 4117) ∨ (¬ p 4191) ∨ (¬ p 4512) ∨ (¬ p 4877) ∨ (¬ p 5109) :=
  ElevenRUP.step50804 (p 2027) (p 2651) (p 2753) (p 2810) (p 3204) (p 3266) (p 3755) (p 3946) (p 4117) (p 4191) (p 4512) (p 4877) (p 5109) (derived40810 p h) (h 23771)

theorem derived50805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3319) ∨ (¬ p 4366) ∨ (¬ p 4427) ∨ (¬ p 4624) :=
  ElevenRUP.step50805 (p 2027) (p 3093) (p 3319) (p 4366) (p 4427) (p 4624) (derived40810 p h) (h 23772)

theorem derived50808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2437) ∨ (¬ p 2928) ∨ (¬ p 3684) ∨ (¬ p 4750) :=
  ElevenRUP.step50808 (p 2027) (p 2406) (p 2437) (p 2928) (p 3684) (p 4750) (derived40810 p h) (h 23776)

theorem derived50809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 3742) ∨ (¬ p 4031) ∨ (¬ p 4644) :=
  ElevenRUP.step50809 (p 2027) (p 2810) (p 2951) (p 3136) (p 3742) (p 4031) (p 4644) (derived40810 p h) (h 23777)

theorem derived50810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3367) ∨ (¬ p 3588) ∨ (¬ p 4106) ∨ (¬ p 4644) :=
  ElevenRUP.step50810 (p 2027) (p 2850) (p 3367) (p 3588) (p 4106) (p 4644) (derived40810 p h) (h 23778)

theorem derived50811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3325) ∨ (¬ p 3654) ∨ (¬ p 3979) ∨ (¬ p 4197) ∨ (¬ p 4624) ∨ (¬ p 5590) :=
  ElevenRUP.step50811 (p 2027) (p 3325) (p 3654) (p 3979) (p 4197) (p 4624) (p 5590) (derived40810 p h) (h 23779)

theorem derived50812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 2761) ∨ (¬ p 2952) ∨ (¬ p 3516) ∨ (¬ p 3694) ∨ (¬ p 4066) ∨ (¬ p 4787) ∨ (¬ p 5051) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step50812 (p 2027) (p 2685) (p 2761) (p 2952) (p 3516) (p 3694) (p 4066) (p 4787) (p 5051) (p 5123) (p 5568) (derived40810 p h) (h 23780)

theorem derived50813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2311) ∨ (¬ p 3551) ∨ (¬ p 3654) ∨ (¬ p 4624) :=
  ElevenRUP.step50813 (p 2027) (p 2177) (p 2311) (p 3551) (p 3654) (p 4624) (derived40810 p h) (h 23781)

theorem derived50814 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2922) ∨ (¬ p 2950) ∨ (¬ p 3379) ∨ (¬ p 3868) ∨ (¬ p 4118) ∨ (¬ p 4120) ∨ (¬ p 4311) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step50814 (p 2027) (p 2254) (p 2922) (p 2950) (p 3379) (p 3868) (p 4118) (p 4120) (p 4311) (p 4444) (p 4826) (derived40810 p h) (h 23782)

theorem derived50815 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2963) ∨ (¬ p 3222) ∨ (¬ p 3276) ∨ (¬ p 3379) ∨ (¬ p 3568) ∨ (¬ p 4260) ∨ (¬ p 4831) :=
  ElevenRUP.step50815 (p 2027) (p 2254) (p 2963) (p 3222) (p 3276) (p 3379) (p 3568) (p 4260) (p 4831) (derived40810 p h) (h 23783)

theorem derived50817 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2963) ∨ (¬ p 3233) ∨ (¬ p 3324) ∨ (¬ p 3379) ∨ (¬ p 3707) ∨ (¬ p 4332) ∨ (¬ p 4347) ∨ (¬ p 4425) :=
  ElevenRUP.step50817 (p 2027) (p 2254) (p 2963) (p 3233) (p 3324) (p 3379) (p 3707) (p 4332) (p 4347) (p 4425) (derived40810 p h) (h 23785)

theorem derived50819 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3172) ∨ (¬ p 3201) ∨ (¬ p 3868) ∨ (¬ p 4118) ∨ (¬ p 4444) ∨ (¬ p 4789) ∨ (¬ p 4826) :=
  ElevenRUP.step50819 (p 2027) (p 2598) (p 3172) (p 3201) (p 3868) (p 4118) (p 4444) (p 4789) (p 4826) (derived40810 p h) (h 23787)

theorem derived50820 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2534) ∨ (¬ p 3146) ∨ (¬ p 4539) ∨ (¬ p 4607) :=
  ElevenRUP.step50820 (p 2027) (p 2220) (p 2534) (p 3146) (p 4539) (p 4607) (derived40810 p h) (h 23788)

theorem derived50821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2850) ∨ (¬ p 3693) ∨ (¬ p 3874) ∨ (¬ p 4539) :=
  ElevenRUP.step50821 (p 2027) (p 2220) (p 2850) (p 3693) (p 3874) (p 4539) (derived40810 p h) (h 23789)

theorem derived50822 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2406) ∨ (¬ p 2499) ∨ (¬ p 3096) ∨ (¬ p 4539) :=
  ElevenRUP.step50822 (p 2027) (p 2156) (p 2406) (p 2499) (p 3096) (p 4539) (derived40810 p h) (h 23790)

theorem derived50826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2619) ∨ (¬ p 3582) ∨ (¬ p 3876) ∨ (¬ p 3880) ∨ (¬ p 3905) :=
  ElevenRUP.step50826 (p 1976) (p 2027) (p 2589) (p 2619) (p 2914) (p 3582) (p 3876) (p 3880) (p 3905) (h 2136) (derived40810 p h) (derived40887 p h) (h 23795)

theorem derived50827 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2850) ∨ (¬ p 3644) ∨ (¬ p 3876) ∨ (¬ p 3905) :=
  ElevenRUP.step50827 (p 1976) (p 2027) (p 2589) (p 2633) (p 2850) (p 3644) (p 3876) (p 3905) (h 2136) (derived40810 p h) (derived40879 p h) (h 23796)

theorem derived50828 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2441) ∨ (¬ p 3580) ∨ (¬ p 3644) ∨ (¬ p 3684) ∨ (¬ p 4750) :=
  ElevenRUP.step50828 (p 2027) (p 2264) (p 2441) (p 3580) (p 3644) (p 3684) (p 4750) (derived40810 p h) (h 23797)

theorem derived50830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2373) ∨ (¬ p 4042) ∨ (¬ p 4235) ∨ (¬ p 4559) :=
  ElevenRUP.step50830 (p 2027) (p 2299) (p 2373) (p 4042) (p 4235) (p 4559) (derived40810 p h) (h 23802)

theorem derived50831 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2493) ∨ (¬ p 2553) ∨ (¬ p 3379) ∨ (¬ p 3758) ∨ (¬ p 3989) ∨ (¬ p 4501) ∨ (¬ p 4736) :=
  ElevenRUP.step50831 (p 2027) (p 2138) (p 2493) (p 2553) (p 3379) (p 3758) (p 3989) (p 4501) (p 4736) (derived40810 p h) (h 23803)

theorem derived50832 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 4117) ∨ (p 4786) :=
  ElevenRUP.step50832 (p 1987) (p 2611) (p 2696) (p 4117) (p 4786) (h 2147) (derived40877 p h) (h 23804)

theorem derived50835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3379) ∨ (¬ p 3425) ∨ (¬ p 3564) ∨ (¬ p 3659) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4736) :=
  ElevenRUP.step50835 (p 2027) (p 2493) (p 3379) (p 3425) (p 3564) (p 3659) (p 4330) (p 4348) (p 4736) (derived40810 p h) (h 23807)

theorem derived50836 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2665) ∨ (¬ p 3051) ∨ (¬ p 4235) ∨ (¬ p 4399) :=
  ElevenRUP.step50836 (p 2027) (p 2440) (p 2665) (p 3051) (p 4235) (p 4399) (derived40810 p h) (h 23808)

theorem derived50838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2563) ∨ (¬ p 3359) ∨ (¬ p 4947) ∨ (¬ p 5043) :=
  ElevenRUP.step50838 (p 2027) (p 2542) (p 2563) (p 3359) (p 4947) (p 5043) (derived40810 p h) (h 23810)

theorem derived50839 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 3690) ∨ (¬ p 4235) ∨ (¬ p 4539) ∨ (¬ p 4988) :=
  ElevenRUP.step50839 (p 2027) (p 3516) (p 3690) (p 4235) (p 4539) (p 4988) (derived40810 p h) (h 23811)

theorem derived50842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 2509) ∨ (¬ p 2860) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4108) ∨ (¬ p 4384) ∨ (¬ p 4733) :=
  ElevenRUP.step50842 (p 2027) (p 2132) (p 2187) (p 2509) (p 2860) (p 2922) (p 3540) (p 4108) (p 4384) (p 4733) (derived40810 p h) (h 23814)

theorem derived50844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3548) ∨ (¬ p 4366) ∨ (¬ p 4733) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step50844 (p 2027) (p 2598) (p 3276) (p 3333) (p 3548) (p 4366) (p 4733) (p 5123) (p 5558) (derived40810 p h) (h 23816)

theorem derived50845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3860) ∨ (¬ p 4129) ∨ (¬ p 4261) ∨ (¬ p 4444) ∨ (¬ p 4733) ∨ (¬ p 4826) :=
  ElevenRUP.step50845 (p 2027) (p 2132) (p 2870) (p 3860) (p 4129) (p 4261) (p 4444) (p 4733) (p 4826) (derived40810 p h) (h 23817)

theorem derived50846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (¬ p 4039) ∨ (¬ p 4110) ∨ (¬ p 4205) ∨ (¬ p 4632) ∨ (¬ p 4942) ∨ (¬ p 5284) :=
  ElevenRUP.step50846 (p 2027) (p 3707) (p 4039) (p 4110) (p 4205) (p 4632) (p 4942) (p 5284) (derived40810 p h) (h 23818)

theorem derived50847 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 4733) :=
  ElevenRUP.step50847 (p 2027) (p 2598) (p 2911) (p 3201) (p 3549) (p 3591) (p 4107) (p 4666) (p 4733) (derived40810 p h) (h 23819)

theorem derived50848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2299) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4668) :=
  ElevenRUP.step50848 (p 2027) (p 2248) (p 2299) (p 2901) (p 2946) (p 3246) (p 3549) (p 3591) (p 4668) (derived40810 p h) (h 23820)

theorem derived50850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 2780) ∨ (¬ p 3822) ∨ (¬ p 4668) ∨ (¬ p 4786) :=
  ElevenRUP.step50850 (p 2027) (p 2299) (p 2417) (p 2437) (p 2651) (p 2780) (p 3822) (p 4668) (p 4786) (derived40810 p h) (h 23822)

theorem derived50852 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2962) ∨ (¬ p 3872) ∨ (¬ p 3989) ∨ (¬ p 4235) ∨ (¬ p 4539) :=
  ElevenRUP.step50852 (p 2027) (p 2383) (p 2962) (p 3872) (p 3989) (p 4235) (p 4539) (derived40810 p h) (h 23824)

theorem derived50853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3051) ∨ (¬ p 4235) ∨ (¬ p 4399) ∨ (¬ p 4715) :=
  ElevenRUP.step50853 (p 2027) (p 2579) (p 3051) (p 4235) (p 4399) (p 4715) (derived40810 p h) (h 23825)

theorem derived50854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2542) ∨ (¬ p 3693) ∨ (¬ p 4256) ∨ (¬ p 4539) :=
  ElevenRUP.step50854 (p 2027) (p 2220) (p 2542) (p 3693) (p 4256) (p 4539) (derived40810 p h) (h 23826)

theorem derived50855 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2299) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4110) ∨ (¬ p 4733) :=
  ElevenRUP.step50855 (p 1997) (p 2027) (p 2284) (p 2299) (p 2633) (p 2696) (p 3136) (p 3549) (p 3591) (p 4110) (p 4733) (h 2157) (derived40810 p h) (derived40879 p h) (h 23827)

theorem derived50856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3767) ∨ (¬ p 4207) ∨ (¬ p 4235) ∨ (¬ p 4322) ∨ (¬ p 4402) ∨ (¬ p 4539) :=
  ElevenRUP.step50856 (p 2027) (p 3767) (p 4207) (p 4235) (p 4322) (p 4402) (p 4539) (derived40810 p h) (h 23828)

theorem derived50857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2274) ∨ (¬ p 2313) ∨ (¬ p 3189) ∨ (¬ p 3645) ∨ (¬ p 3954) ∨ (¬ p 3989) ∨ (¬ p 4198) ∨ (¬ p 4771) ∨ (¬ p 4877) :=
  ElevenRUP.step50857 (p 2027) (p 2241) (p 2274) (p 2313) (p 3189) (p 3645) (p 3954) (p 3989) (p 4198) (p 4771) (p 4877) (derived40810 p h) (h 23829)

theorem derived50858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2140) ∨ (¬ p 3097) ∨ (¬ p 3646) ∨ (¬ p 3985) :=
  ElevenRUP.step50858 (p 2027) (p 2122) (p 2140) (p 3097) (p 3646) (p 3985) (derived40810 p h) (h 23830)

theorem derived50861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2493) ∨ (¬ p 2598) ∨ (¬ p 3564) ∨ (¬ p 3583) ∨ (¬ p 3590) ∨ (¬ p 3692) ∨ (¬ p 4120) ∨ (¬ p 4330) ∨ (¬ p 4737) :=
  ElevenRUP.step50861 (p 2027) (p 2143) (p 2493) (p 2598) (p 3564) (p 3583) (p 3590) (p 3692) (p 4120) (p 4330) (p 4737) (derived40810 p h) (h 23834)

theorem derived50863 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2140) ∨ (¬ p 2187) ∨ (¬ p 2387) ∨ (¬ p 2860) ∨ (¬ p 4198) :=
  ElevenRUP.step50863 (p 2027) (p 2140) (p 2187) (p 2387) (p 2860) (p 4198) (derived40810 p h) (h 23836)

theorem derived50864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3227) ∨ (¬ p 3379) ∨ (¬ p 3834) ∨ (¬ p 4949) :=
  ElevenRUP.step50864 (p 2027) (p 2406) (p 3227) (p 3379) (p 3834) (p 4949) (derived40810 p h) (h 23838)

theorem derived50867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 4736) :=
  ElevenRUP.step50867 (p 2027) (p 2780) (p 2911) (p 2922) (p 3379) (p 3822) (p 4107) (p 4666) (p 4736) (derived40810 p h) (h 23844)

theorem derived50868 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3177) ∨ (¬ p 3661) ∨ (¬ p 3969) ∨ (¬ p 4507) ∨ (¬ p 5590) :=
  ElevenRUP.step50868 (p 2027) (p 2284) (p 3177) (p 3661) (p 3969) (p 4507) (p 5590) (derived40810 p h) (h 23845)

theorem derived50869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2313) ∨ (¬ p 2553) ∨ (¬ p 2577) ∨ (¬ p 3347) ∨ (¬ p 3954) ∨ (¬ p 3956) ∨ (¬ p 4433) ∨ (¬ p 5216) :=
  ElevenRUP.step50869 (p 2027) (p 2166) (p 2210) (p 2313) (p 2553) (p 2577) (p 3347) (p 3954) (p 3956) (p 4433) (p 5216) (derived40810 p h) (h 23846)

theorem derived50870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3555) ∨ (¬ p 4363) ∨ (¬ p 4516) ∨ (¬ p 5043) :=
  ElevenRUP.step50870 (p 2027) (p 3093) (p 3555) (p 4363) (p 4516) (p 5043) (derived40810 p h) (h 23847)

theorem derived50871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2933) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3868) ∨ (¬ p 4322) ∨ (¬ p 4376) ∨ (¬ p 4385) ∨ (¬ p 4826) :=
  ElevenRUP.step50871 (p 2027) (p 2138) (p 2933) (p 3366) (p 3399) (p 3452) (p 3868) (p 4322) (p 4376) (p 4385) (p 4826) (derived40810 p h) (h 23848)

theorem derived50872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2743) ∨ (¬ p 3954) ∨ (¬ p 4243) ∨ (¬ p 5052) :=
  ElevenRUP.step50872 (p 2027) (p 2210) (p 2743) (p 3954) (p 4243) (p 5052) (derived40810 p h) (h 23849)

theorem derived50873 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2299) ∨ (¬ p 2946) ∨ (¬ p 3256) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3692) ∨ (¬ p 4237) ∨ (¬ p 4902) :=
  ElevenRUP.step50873 (p 2027) (p 2248) (p 2299) (p 2946) (p 3256) (p 3549) (p 3591) (p 3692) (p 4237) (p 4902) (derived40810 p h) (h 23850)

theorem derived50874 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 3343) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4107) ∨ (¬ p 4638) ∨ (¬ p 4733) :=
  ElevenRUP.step50874 (p 2027) (p 2630) (p 2696) (p 3343) (p 3549) (p 3591) (p 4107) (p 4638) (p 4733) (derived40810 p h) (h 23851)

theorem derived50875 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 3540) ∨ (¬ p 3921) :=
  ElevenRUP.step50875 (p 1995) (p 2027) (p 2299) (p 2499) (p 2573) (p 2633) (p 3540) (p 3921) (h 2155) (derived40810 p h) (derived40879 p h) (h 23852)

theorem derived50876 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2331) ∨ (¬ p 2881) ∨ (¬ p 3027) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4154) ∨ (¬ p 4280) ∨ (¬ p 4736) :=
  ElevenRUP.step50876 (p 2027) (p 2253) (p 2331) (p 2881) (p 3027) (p 3425) (p 3659) (p 4154) (p 4280) (p 4736) (derived40810 p h) (h 23853)

theorem derived50877 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4244) ∨ (¬ p 4736) :=
  ElevenRUP.step50877 (p 2027) (p 2138) (p 2241) (p 2641) (p 2668) (p 3570) (p 4133) (p 4244) (p 4736) (derived40810 p h) (h 23855)

theorem derived50878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2870) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3556) ∨ (¬ p 3694) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4786) :=
  ElevenRUP.step50878 (p 2027) (p 2136) (p 2870) (p 3166) (p 3256) (p 3556) (p 3694) (p 4134) (p 4347) (p 4786) (derived40810 p h) (h 23856)

theorem derived50879 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 3027) ∨ (¬ p 3570) ∨ (¬ p 4244) ∨ (¬ p 4668) ∨ (¬ p 4736) :=
  ElevenRUP.step50879 (p 2027) (p 2138) (p 2241) (p 2449) (p 3027) (p 3570) (p 4244) (p 4668) (p 4736) (derived40810 p h) (h 23857)

theorem derived50881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2499) ∨ (¬ p 3452) ∨ (¬ p 4210) ∨ (¬ p 4715) :=
  ElevenRUP.step50881 (p 2027) (p 2210) (p 2499) (p 3452) (p 4210) (p 4715) (derived40810 p h) (h 23859)

theorem derived50883 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2952) ∨ (¬ p 3952) ∨ (¬ p 4313) ∨ (¬ p 4787) :=
  ElevenRUP.step50883 (p 2027) (p 2860) (p 2952) (p 3952) (p 4313) (p 4787) (derived40810 p h) (h 23861)

theorem derived50884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 4210) ∨ (¬ p 4644) :=
  ElevenRUP.step50884 (p 2027) (p 2210) (p 2928) (p 3452) (p 4210) (p 4644) (derived40810 p h) (h 23862)

theorem derived50885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3684) ∨ (¬ p 4235) ∨ (¬ p 4399) ∨ (¬ p 4730) :=
  ElevenRUP.step50885 (p 2027) (p 3051) (p 3684) (p 4235) (p 4399) (p 4730) (derived40810 p h) (h 23863)

theorem derived50886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3452) ∨ (¬ p 3486) ∨ (¬ p 4172) ∨ (¬ p 4376) ∨ (¬ p 4874) :=
  ElevenRUP.step50886 (p 2027) (p 3051) (p 3452) (p 3486) (p 4172) (p 4376) (p 4874) (derived40810 p h) (h 23864)

end ElevenLogic
