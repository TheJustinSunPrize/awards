import SunPrize.Certificate.Derived053
import SunPrize.Certificate.Logic054
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived102110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (¬ p 3567) ∨ (¬ p 2528) ∨ (¬ p 5059) ∨ (¬ p 2797) ∨ (¬ p 2577) ∨ (p 3286) ∨ (¬ p 2470) ∨ (¬ p 3680) :=
  ElevenRUP.step102110 (p 2470) (p 2528) (p 2577) (p 2797) (p 3286) (p 3292) (p 3567) (p 3680) (p 5059) (p 5284) (derived73378 p h) (derived72305 p h)

theorem derived102114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 4399) ∨ (p 2563) ∨ (¬ p 2156) ∨ (¬ p 3680) :=
  ElevenRUP.step102114 (p 2156) (p 2563) (p 2982) (p 3680) (p 4110) (p 4399) (derived73516 p h) (derived46721 p h)

theorem derived102115 (p : Nat → Prop) (h : Inputs p) :
    (p 2475) ∨ (p 2470) :=
  ElevenRUP.step102115 (p 2470) (p 2475) (p 2479) (derived73251 p h) (h 3085)

theorem derived102120 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (¬ p 4149) ∨ (p 2608) ∨ (p 3670) ∨ (¬ p 2651) ∨ (¬ p 5119) ∨ (¬ p 2248) ∨ (¬ p 3083) :=
  ElevenRUP.step102120 (p 2248) (p 2608) (p 2651) (p 3083) (p 3599) (p 3670) (p 3954) (p 4149) (p 4379) (p 5119) (p 5387) (derived73572 p h) (derived73498 p h) (derived74026 p h) (derived61691 p h)

theorem derived102122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 5119) ∨ (¬ p 3425) ∨ (¬ p 2744) ∨ (p 3434) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 2651) ∨ (p 2761) ∨ (¬ p 3083) :=
  ElevenRUP.step102122 (p 2246) (p 2651) (p 2744) (p 2761) (p 3083) (p 3366) (p 3425) (p 3434) (p 4149) (p 4324) (p 4381) (p 5119) (derived73556 p h) (derived73574 p h) (derived59451 p h)

theorem derived102128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 2951) ∨ (p 2717) ∨ (¬ p 3136) ∨ (¬ p 2252) ∨ (¬ p 2745) ∨ (p 2807) ∨ (p 2459) ∨ (¬ p 2470) ∨ (¬ p 3904) ∨ (¬ p 4325) ∨ (¬ p 5122) :=
  ElevenRUP.step102128 (p 2252) (p 2459) (p 2470) (p 2717) (p 2745) (p 2807) (p 2951) (p 3136) (p 3414) (p 3659) (p 3904) (p 4149) (p 4325) (p 4348) (p 5122) (derived73438 p h) (derived73392 p h) (derived73562 p h) (derived64910 p h)

theorem derived102129 (p : Nat → Prop) (h : Inputs p) :
    (p 5357) ∨ (p 3631) :=
  ElevenRUP.step102129 (p 3631) (p 5357) (p 6094) (derived74437 p h) (h 13669)

theorem derived102130 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 3266) :=
  ElevenRUP.step102130 (p 3266) (p 5123) (p 6017) (derived74355 p h) (h 13101)

theorem derived102134 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 4009) ∨ (¬ p 5122) ∨ (¬ p 3005) ∨ (¬ p 5107) :=
  ElevenRUP.step102134 (p 3005) (p 3755) (p 4009) (p 4035) (p 5107) (p 5122) (derived73506 p h) (derived63519 p h)

theorem derived102135 (p : Nat → Prop) (h : Inputs p) :
    (p 4610) ∨ (¬ p 2373) :=
  ElevenRUP.step102135 (p 2373) (p 4610) (p 5840) (derived74131 p h) (h 12038)

theorem derived102136 (p : Nat → Prop) (h : Inputs p) :
    (p 4121) ∨ (¬ p 3083) :=
  ElevenRUP.step102136 (p 3083) (p 4121) (p 5978) (derived74307 p h) (h 12859)

theorem derived102143 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3914) ∨ (p 2761) ∨ (¬ p 5250) ∨ (p 2449) ∨ (p 2807) ∨ (¬ p 2608) ∨ (¬ p 2254) ∨ (¬ p 2829) :=
  ElevenRUP.step102143 (p 2254) (p 2449) (p 2608) (p 2761) (p 2807) (p 2829) (p 3414) (p 3914) (p 3947) (p 4381) (p 5250) (derived73574 p h) (derived73494 p h) (derived73392 p h) (derived49074 p h)

theorem derived102146 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (p 3670) ∨ (p 2774) ∨ (¬ p 2829) :=
  ElevenRUP.step102146 (p 2774) (p 2780) (p 2829) (p 3599) (p 3670) (p 4379) (p 5387) (derived73572 p h) (derived74026 p h) (derived73308 p h) (derived47446 p h)

theorem derived102151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (p 3399) ∨ (¬ p 5362) ∨ (p 3434) ∨ (¬ p 4797) :=
  ElevenRUP.step102151 (p 3399) (p 3434) (p 3830) (p 4324) (p 4366) (p 4797) (p 5362) (derived73570 p h) (derived73556 p h) (derived64843 p h)

theorem derived102152 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 2717) ∨ (¬ p 3945) :=
  ElevenRUP.step102152 (p 2717) (p 3434) (p 3945) (p 4324) (derived73556 p h) (h 21746)

theorem derived102155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2246) ∨ (p 2341) ∨ (¬ p 2744) ∨ (¬ p 4621) ∨ (¬ p 3820) ∨ (p 3434) ∨ (¬ p 3366) ∨ (¬ p 2651) ∨ (¬ p 3564) ∨ (¬ p 3016) :=
  ElevenRUP.step102155 (p 2246) (p 2341) (p 2651) (p 2717) (p 2744) (p 3016) (p 3366) (p 3434) (p 3551) (p 3564) (p 3820) (p 4324) (p 4621) (derived73408 p h) (derived73556 p h) (derived64381 p h)

theorem derived102157 (p : Nat → Prop) (h : Inputs p) :
    (p 4781) ∨ (¬ p 3516) ∨ (¬ p 2751) ∨ (¬ p 4066) ∨ (p 3434) ∨ (p 2996) :=
  ElevenRUP.step102157 (p 2751) (p 2996) (p 3027) (p 3434) (p 3516) (p 4066) (p 4324) (p 4781) (derived73556 p h) (derived73340 p h) (derived41444 p h)

theorem derived102159 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5119) ∨ (¬ p 4419) ∨ (p 3434) ∨ (¬ p 3425) ∨ (p 2761) ∨ (¬ p 2230) ∨ (¬ p 2373) :=
  ElevenRUP.step102159 (p 2230) (p 2373) (p 2761) (p 3425) (p 3434) (p 3969) (p 4324) (p 4381) (p 4419) (p 5119) (derived73556 p h) (derived73574 p h) (derived42382 p h)

theorem derived102162 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (p 2761) ∨ (¬ p 5119) ∨ (¬ p 3969) ∨ (¬ p 3425) ∨ (¬ p 3156) ∨ (¬ p 2946) ∨ (¬ p 4786) :=
  ElevenRUP.step102162 (p 2761) (p 2946) (p 3156) (p 3425) (p 3434) (p 3969) (p 4324) (p 4381) (p 4786) (p 5119) (derived73556 p h) (derived73574 p h) (derived41202 p h)

theorem derived102166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5250) ∨ (¬ p 2192) ∨ (¬ p 4736) ∨ (p 3434) ∨ (¬ p 3425) ∨ (¬ p 2210) ∨ (p 2761) :=
  ElevenRUP.step102166 (p 2192) (p 2210) (p 2761) (p 3425) (p 3434) (p 3737) (p 4324) (p 4381) (p 4736) (p 5250) (derived73556 p h) (derived73574 p h) (derived57893 p h)

theorem derived102167 (p : Nat → Prop) (h : Inputs p) :
    (p 2761) ∨ (¬ p 3412) ∨ (¬ p 4736) ∨ (¬ p 2946) ∨ (¬ p 5250) ∨ (p 3434) ∨ (¬ p 2253) ∨ (¬ p 2192) ∨ (¬ p 3425) ∨ (¬ p 3737) :=
  ElevenRUP.step102167 (p 2192) (p 2253) (p 2761) (p 2946) (p 3412) (p 3425) (p 3434) (p 3737) (p 4324) (p 4381) (p 4736) (p 5250) (derived73574 p h) (derived73556 p h) (derived49660 p h)

theorem derived102175 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 3449) ∨ (p 3319) ∨ (¬ p 5307) ∨ (¬ p 3990) ∨ (¬ p 4503) :=
  ElevenRUP.step102175 (p 3093) (p 3319) (p 3449) (p 3591) (p 3990) (p 4026) (p 4503) (p 5307) (derived73432 p h) (derived73504 p h) (derived57197 p h)

theorem derived102176 (p : Nat → Prop) (h : Inputs p) :
    (p 3319) ∨ (p 3923) ∨ (¬ p 3990) :=
  ElevenRUP.step102176 (p 3319) (p 3923) (p 3990) (p 4026) (derived73504 p h) (h 33830)

theorem derived102183 (p : Nat → Prop) (h : Inputs p) :
    (p 4356) ∨ (¬ p 2156) :=
  ElevenRUP.step102183 (p 2156) (p 4356) (p 5792) (derived74067 p h) (h 11759)

theorem derived102189 (p : Nat → Prop) (h : Inputs p) :
    (p 4471) ∨ (p 2122) :=
  ElevenRUP.step102189 (p 2122) (p 4471) (p 5788) (derived74061 p h) (h 11731)

theorem derived102190 (p : Nat → Prop) (h : Inputs p) :
    (p 3698) ∨ (p 2850) :=
  ElevenRUP.step102190 (p 2850) (p 3698) (p 5932) (derived74249 p h) (h 12576)

theorem derived102194 (p : Nat → Prop) (h : Inputs p) :
    (p 4841) ∨ (p 2797) :=
  ElevenRUP.step102194 (p 2797) (p 4841) (p 5917) (derived74229 p h) (h 12487)

theorem derived102203 (p : Nat → Prop) (h : Inputs p) :
    (p 3985) ∨ (¬ p 2860) :=
  ElevenRUP.step102203 (p 2860) (p 3985) (p 5936) (derived74255 p h) (h 12600)

theorem derived102207 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (¬ p 4337) :=
  ElevenRUP.step102207 (p 4337) (p 4401) (p 4560) (derived72955 p h) (h 26956)

theorem derived102210 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (¬ p 2860) :=
  ElevenRUP.step102210 (p 2860) (p 4401) (p 5936) (derived74255 p h) (h 12603)

theorem derived102220 (p : Nat → Prop) (h : Inputs p) :
    (p 2786) ∨ (¬ p 2774) :=
  ElevenRUP.step102220 (p 2774) (p 2786) (p 2789) (derived73313 p h) (h 3701)

theorem derived102221 (p : Nat → Prop) (h : Inputs p) :
    (p 4396) ∨ (p 2396) :=
  ElevenRUP.step102221 (p 2396) (p 4396) (p 5845) (derived74137 p h) (h 12064)

theorem derived102222 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2396) :=
  ElevenRUP.step102222 (p 2396) (p 4620) (p 5845) (derived74137 p h) (h 12067)

theorem derived102227 (p : Nat → Prop) (h : Inputs p) :
    (p 2785) ∨ (¬ p 2774) :=
  ElevenRUP.step102227 (p 2774) (p 2785) (p 2789) (derived73313 p h) (h 3703)

theorem derived102241 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (p 4905) :=
  ElevenRUP.step102241 (p 2341) (p 3551) (p 4905) (derived73408 p h) (derived54672 p h)

theorem derived102242 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3212) ∨ (¬ p 3872) ∨ (¬ p 5046) ∨ (¬ p 2881) ∨ (¬ p 4984) :=
  ElevenRUP.step102242 (p 2341) (p 2881) (p 3212) (p 3551) (p 3872) (p 4984) (p 5046) (derived73408 p h) (derived52382 p h)

theorem derived102247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3546) ∨ (¬ p 3564) ∨ (¬ p 2749) ∨ (¬ p 2246) ∨ (¬ p 4796) ∨ (p 2341) ∨ (p 3246) ∨ (¬ p 2651) ∨ (¬ p 2881) ∨ (¬ p 4445) ∨ (¬ p 3016) ∨ (¬ p 4330) :=
  ElevenRUP.step102247 (p 2246) (p 2341) (p 2651) (p 2749) (p 2881) (p 3016) (p 3246) (p 3546) (p 3551) (p 3564) (p 3690) (p 4330) (p 4445) (p 4796) (derived73408 p h) (derived73446 p h) (derived53278 p h)

theorem derived102248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 2860) ∨ (p 2341) ∨ (p 3266) ∨ (¬ p 2132) ∨ (¬ p 5250) ∨ (¬ p 5197) ∨ (p 2459) ∨ (¬ p 4729) :=
  ElevenRUP.step102248 (p 2132) (p 2341) (p 2459) (p 2860) (p 3266) (p 3551) (p 3737) (p 4348) (p 4444) (p 4729) (p 5197) (p 5250) (derived73408 p h) (derived73580 p h) (derived73562 p h) (derived50771 p h)

theorem derived102249 (p : Nat → Prop) (h : Inputs p) :
    (p 3581) ∨ (p 2553) :=
  ElevenRUP.step102249 (p 2553) (p 3581) (p 5875) (derived74173 p h) (h 12242)

theorem derived102250 (p : Nat → Prop) (h : Inputs p) :
    (p 4596) ∨ (p 2352) :=
  ElevenRUP.step102250 (p 2352) (p 4596) (p 5833) (derived74121 p h) (h 11995)

theorem derived102251 (p : Nat → Prop) (h : Inputs p) :
    (p 4603) ∨ (¬ p 2363) :=
  ElevenRUP.step102251 (p 2363) (p 4603) (p 5837) (derived74127 p h) (h 12019)

theorem derived102252 (p : Nat → Prop) (h : Inputs p) :
    (p 3227) ∨ (¬ p 3193) :=
  ElevenRUP.step102252 (p 3193) (p 3227) (p 3230) (derived73367 p h) (h 4578)

theorem derived102253 (p : Nat → Prop) (h : Inputs p) :
    (p 3266) ∨ (¬ p 3853) ∨ (p 2241) ∨ (¬ p 3506) ∨ (¬ p 3830) :=
  ElevenRUP.step102253 (p 2241) (p 2247) (p 3266) (p 3506) (p 3830) (p 3853) (p 4444) (derived73580 p h) (derived73226 p h) (derived45070 p h)

theorem derived102254 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3853) ∨ (¬ p 2751) ∨ (¬ p 3830) ∨ (p 3755) :=
  ElevenRUP.step102254 (p 2241) (p 2247) (p 2751) (p 3755) (p 3830) (p 3853) (p 4035) (derived73226 p h) (derived73506 p h) (derived61237 p h)

theorem derived102256 (p : Nat → Prop) (h : Inputs p) :
    (p 4202) ∨ (p 2406) :=
  ElevenRUP.step102256 (p 2406) (p 4202) (p 5848) (derived74141 p h) (h 12082)

theorem derived102259 (p : Nat → Prop) (h : Inputs p) :
    (p 4756) ∨ (p 2641) :=
  ElevenRUP.step102259 (p 2641) (p 4756) (p 5893) (derived74197 p h) (h 12345)

theorem derived102260 (p : Nat → Prop) (h : Inputs p) :
    (p 4338) ∨ (¬ p 2192) :=
  ElevenRUP.step102260 (p 2192) (p 4338) (p 5804) (derived74083 p h) (h 11824)

theorem derived102268 (p : Nat → Prop) (h : Inputs p) :
    (p 4496) ∨ (¬ p 2166) :=
  ElevenRUP.step102268 (p 2166) (p 4496) (p 5795) (derived74071 p h) (h 11773)

theorem derived102269 (p : Nat → Prop) (h : Inputs p) :
    (p 3544) ∨ (p 3527) :=
  ElevenRUP.step102269 (p 3527) (p 3544) (p 6076) (derived74417 p h) (h 13486)

theorem derived102271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (p 4953) :=
  ElevenRUP.step102271 (p 2982) (p 4951) (p 4953) (derived73848 p h) (h 8230)

theorem derived102279 (p : Nat → Prop) (h : Inputs p) :
    (p 2440) ∨ (p 3016) ∨ (¬ p 4109) ∨ (¬ p 4509) ∨ (¬ p 3096) ∨ (¬ p 2220) :=
  ElevenRUP.step102279 (p 2220) (p 2440) (p 2542) (p 3016) (p 3096) (p 3574) (p 4109) (p 4509) (derived73270 p h) (derived73422 p h) (derived61866 p h)

theorem derived102285 (p : Nat → Prop) (h : Inputs p) :
    (p 4024) ∨ (¬ p 2829) :=
  ElevenRUP.step102285 (p 2829) (p 4024) (p 5927) (derived74243 p h) (h 12550)

theorem derived102286 (p : Nat → Prop) (h : Inputs p) :
    (p 4757) ∨ (p 2641) :=
  ElevenRUP.step102286 (p 2641) (p 4757) (p 5893) (derived74197 p h) (h 12344)

theorem derived102287 (p : Nat → Prop) (h : Inputs p) :
    (p 2252) ∨ (¬ p 2241) :=
  ElevenRUP.step102287 (p 2241) (p 2252) (p 2256) (derived73231 p h) (h 2647)

theorem derived102297 (p : Nat → Prop) (h : Inputs p) :
    (p 4869) ∨ (¬ p 2829) :=
  ElevenRUP.step102297 (p 2829) (p 4869) (p 5927) (derived74243 p h) (h 12551)

theorem derived102298 (p : Nat → Prop) (h : Inputs p) :
    (p 4842) ∨ (p 2797) :=
  ElevenRUP.step102298 (p 2797) (p 4842) (p 5917) (derived74229 p h) (h 12488)

theorem derived102299 (p : Nat → Prop) (h : Inputs p) :
    (p 3988) ∨ (p 2187) :=
  ElevenRUP.step102299 (p 2187) (p 3988) (p 5800) (derived74077 p h) (h 11802)

theorem derived102304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (p 2241) ∨ (¬ p 4288) ∨ (¬ p 2751) ∨ (p 3005) :=
  ElevenRUP.step102304 (p 2241) (p 2247) (p 2751) (p 3005) (p 3449) (p 3877) (p 4288) (derived73226 p h) (derived73488 p h) (derived41582 p h)

theorem derived102305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 2363) ∨ (p 2156) ∨ (¬ p 3645) ∨ (¬ p 3449) ∨ (¬ p 5122) ∨ (¬ p 4959) ∨ (p 2241) ∨ (p 2187) :=
  ElevenRUP.step102305 (p 2156) (p 2187) (p 2241) (p 2247) (p 2363) (p 3449) (p 3645) (p 3646) (p 3989) (p 4181) (p 4347) (p 4959) (p 5122) (derived73560 p h) (derived73436 p h) (derived73226 p h) (derived73502 p h) (derived52547 p h)

theorem derived102307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3449) ∨ (p 3323) ∨ (¬ p 4377) ∨ (p 2797) ∨ (¬ p 4604) ∨ (¬ p 3366) ∨ (p 2210) ∨ (p 2696) :=
  ElevenRUP.step102307 (p 2210) (p 2696) (p 2797) (p 3073) (p 3323) (p 3365) (p 3366) (p 3449) (p 3555) (p 4037) (p 4195) (p 4377) (p 4604) (derived73508 p h) (derived73532 p h) (derived73412 p h) (derived73390 p h) (derived42385 p h)

theorem derived102311 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 3379) ∨ (¬ p 5122) ∨ (¬ p 3425) ∨ (¬ p 3449) ∨ (p 3146) ∨ (¬ p 4042) ∨ (¬ p 3366) ∨ (¬ p 4376) ∨ (p 2717) :=
  ElevenRUP.step102311 (p 2717) (p 3146) (p 3366) (p 3379) (p 3425) (p 3449) (p 3452) (p 3659) (p 3692) (p 4042) (p 4181) (p 4376) (p 5122) (derived73394 p h) (derived73448 p h) (derived73438 p h) (derived64899 p h)

theorem derived102312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 2608) ∨ (¬ p 3449) ∨ (¬ p 5558) :=
  ElevenRUP.step102312 (p 2608) (p 3449) (p 3954) (p 4181) (p 5558) (derived73498 p h) (derived45163 p h)

theorem derived102320 (p : Nat → Prop) (h : Inputs p) :
    (p 3054) ∨ (p 2850) :=
  ElevenRUP.step102320 (p 2850) (p 3054) (p 5932) (derived74249 p h) (h 12578)

theorem derived102325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 2220) ∨ (¬ p 2563) ∨ (p 2156) :=
  ElevenRUP.step102325 (p 2156) (p 2220) (p 2563) (p 3646) (p 3969) (derived73436 p h) (derived45725 p h)

theorem derived102327 (p : Nat → Prop) (h : Inputs p) :
    (p 4115) ∨ (¬ p 2220) :=
  ElevenRUP.step102327 (p 2220) (p 4115) (p 4530) (derived73620 p h) (h 7128)

theorem derived102333 (p : Nat → Prop) (h : Inputs p) :
    (p 3571) ∨ (¬ p 2891) :=
  ElevenRUP.step102333 (p 2891) (p 3571) (p 5945) (derived74267 p h) (h 12653)

theorem derived102334 (p : Nat → Prop) (h : Inputs p) :
    (p 3587) ∨ (¬ p 2870) :=
  ElevenRUP.step102334 (p 2870) (p 3587) (p 5939) (derived74259 p h) (h 12618)

theorem derived102335 (p : Nat → Prop) (h : Inputs p) :
    (p 3580) ∨ (¬ p 2437) :=
  ElevenRUP.step102335 (p 2437) (p 3580) (p 5858) (derived74155 p h) (h 12141)

theorem derived102345 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2651) :=
  ElevenRUP.step102345 (p 2651) (p 2659) (p 2660) (derived73289 p h) (h 3439)

theorem derived102346 (p : Nat → Prop) (h : Inputs p) :
    (p 4922) ∨ (p 2911) :=
  ElevenRUP.step102346 (p 2911) (p 4922) (p 5950) (derived74273 p h) (h 12684)

theorem derived102352 (p : Nat → Prop) (h : Inputs p) :
    (p 4342) ∨ (p 3422) :=
  ElevenRUP.step102352 (p 3422) (p 4342) (p 6049) (derived74389 p h) (h 13290)

theorem derived102353 (p : Nat → Prop) (h : Inputs p) :
    (p 4871) ∨ (¬ p 2829) :=
  ElevenRUP.step102353 (p 2829) (p 4871) (p 5927) (derived74243 p h) (h 12548)

theorem derived102356 (p : Nat → Prop) (h : Inputs p) :
    (p 4395) ∨ (p 3246) :=
  ElevenRUP.step102356 (p 3246) (p 4395) (p 6010) (derived74345 p h) (h 13057)

theorem derived102357 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 3461) ∨ (p 2774) ∨ (¬ p 2166) ∨ (¬ p 5119) ∨ (¬ p 3917) ∨ (¬ p 4736) ∨ (¬ p 2210) :=
  ElevenRUP.step102357 (p 2166) (p 2210) (p 2774) (p 2780) (p 3461) (p 3917) (p 3969) (p 4191) (p 4736) (p 5119) (derived73530 p h) (derived73308 p h) (derived60366 p h)

theorem derived102361 (p : Nat → Prop) (h : Inputs p) :
    (p 5252) ∨ (¬ p 3461) :=
  ElevenRUP.step102361 (p 3461) (p 5252) (p 6059) (derived74403 p h) (h 13359)

theorem derived102362 (p : Nat → Prop) (h : Inputs p) :
    (p 4394) ∨ (¬ p 3461) :=
  ElevenRUP.step102362 (p 3461) (p 4394) (p 6059) (derived74403 p h) (h 13360)

theorem derived102363 (p : Nat → Prop) (h : Inputs p) :
    (p 5253) ∨ (¬ p 3461) :=
  ElevenRUP.step102363 (p 3461) (p 5253) (p 6059) (derived74403 p h) (h 13362)

theorem derived102364 (p : Nat → Prop) (h : Inputs p) :
    (p 5254) ∨ (¬ p 3461) :=
  ElevenRUP.step102364 (p 3461) (p 5254) (p 6059) (derived74403 p h) (h 13363)

theorem derived102372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 5284) ∨ (p 3286) ∨ (¬ p 4236) ∨ (¬ p 2427) ∨ (¬ p 2230) ∨ (¬ p 3246) ∨ (¬ p 5236) ∨ (¬ p 4419) :=
  ElevenRUP.step102372 (p 2230) (p 2427) (p 3246) (p 3286) (p 3292) (p 3670) (p 4236) (p 4419) (p 5236) (p 5284) (derived73378 p h) (derived42596 p h)

theorem derived102373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4661) ∨ (¬ p 2352) ∨ (¬ p 4625) ∨ (¬ p 4198) ∨ (p 2383) ∨ (p 2761) ∨ (¬ p 2246) ∨ (p 3125) ∨ (¬ p 3506) ∨ (¬ p 3096) ∨ (¬ p 3645) ∨ (¬ p 2807) ∨ (¬ p 2749) ∨ (¬ p 4202) :=
  ElevenRUP.step102373 (p 2246) (p 2352) (p 2383) (p 2387) (p 2749) (p 2761) (p 2807) (p 3096) (p 3125) (p 3506) (p 3645) (p 3744) (p 4198) (p 4202) (p 4381) (p 4625) (p 4661) (derived73246 p h) (derived73574 p h) (derived73454 p h) (derived72310 p h)

theorem derived102376 (p : Nat → Prop) (h : Inputs p) :
    (p 5176) ∨ (¬ p 3343) :=
  ElevenRUP.step102376 (p 3343) (p 5176) (p 6032) (derived74371 p h) (h 13186)

theorem derived102381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 3461) ∨ (p 2331) ∨ (¬ p 4376) ∨ (¬ p 2373) ∨ (¬ p 5119) ∨ (¬ p 2741) ∨ (p 3323) ∨ (¬ p 2230) ∨ (¬ p 3519) ∨ (¬ p 2252) :=
  ElevenRUP.step102381 (p 2230) (p 2252) (p 2331) (p 2373) (p 2741) (p 2963) (p 3323) (p 3461) (p 3519) (p 3969) (p 4037) (p 4191) (p 4376) (p 5119) (derived73530 p h) (derived73338 p h) (derived73508 p h) (derived57493 p h)

theorem derived102382 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 2717) ∨ (¬ p 4445) ∨ (¬ p 5122) ∨ (¬ p 3969) ∨ (¬ p 4132) :=
  ElevenRUP.step102382 (p 2717) (p 3434) (p 3969) (p 4132) (p 4324) (p 4445) (p 5122) (derived73556 p h) (derived58310 p h)

theorem derived102383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5122) ∨ (¬ p 4419) ∨ (p 3005) ∨ (¬ p 2230) ∨ (p 3256) ∨ (¬ p 2373) ∨ (p 2696) :=
  ElevenRUP.step102383 (p 2230) (p 2373) (p 2696) (p 3005) (p 3256) (p 3365) (p 3877) (p 3969) (p 4118) (p 4419) (p 5122) (derived73488 p h) (derived73520 p h) (derived73390 p h) (derived48261 p h)

theorem derived102384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 2246) ∨ (¬ p 2741) ∨ (p 3323) ∨ (¬ p 3519) ∨ (¬ p 2230) ∨ (p 2331) ∨ (¬ p 2373) ∨ (p 3461) ∨ (¬ p 4376) ∨ (¬ p 5119) :=
  ElevenRUP.step102384 (p 2230) (p 2246) (p 2331) (p 2373) (p 2741) (p 2963) (p 3323) (p 3461) (p 3519) (p 3969) (p 4037) (p 4191) (p 4376) (p 5119) (derived73508 p h) (derived73338 p h) (derived73530 p h) (derived57346 p h)

theorem derived102388 (p : Nat → Prop) (h : Inputs p) :
    (p 3546) ∨ (¬ p 3399) :=
  ElevenRUP.step102388 (p 3399) (p 3546) (p 6044) (derived74383 p h) (h 13262)

theorem derived102391 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (p 2406) :=
  ElevenRUP.step102391 (p 2406) (p 4629) (p 5848) (derived74141 p h) (h 12085)

theorem derived102393 (p : Nat → Prop) (h : Inputs p) :
    (p 2500) ∨ (p 2493) :=
  ElevenRUP.step102393 (p 2493) (p 2500) (p 2502) (derived73261 p h) (h 3132)

theorem derived102400 (p : Nat → Prop) (h : Inputs p) :
    (p 5011) ∨ (¬ p 3083) :=
  ElevenRUP.step102400 (p 3083) (p 5011) (p 5978) (derived74307 p h) (h 12861)

theorem derived102401 (p : Nat → Prop) (h : Inputs p) :
    (p 5012) ∨ (¬ p 3083) :=
  ElevenRUP.step102401 (p 3083) (p 5012) (p 5978) (derived74307 p h) (h 12862)

theorem derived102402 (p : Nat → Prop) (h : Inputs p) :
    (p 4957) ∨ (p 2992) :=
  ElevenRUP.step102402 (p 2992) (p 4957) (p 5959) (derived74285 p h) (h 12741)

theorem derived102406 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 3189) ∨ (¬ p 2749) ∨ (p 2839) :=
  ElevenRUP.step102406 (p 2749) (p 2839) (p 3005) (p 3189) (p 3583) (p 3877) (derived73488 p h) (derived73424 p h) (derived67277 p h)

theorem derived102409 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (¬ p 2246) ∨ (¬ p 2749) ∨ (¬ p 5234) ∨ (¬ p 2807) ∨ (¬ p 4777) :=
  ElevenRUP.step102409 (p 2246) (p 2749) (p 2807) (p 3599) (p 4379) (p 4777) (p 5234) (derived73572 p h) (h 20675)

theorem derived102413 (p : Nat → Prop) (h : Inputs p) :
    (p 4525) ∨ (¬ p 2210) :=
  ElevenRUP.step102413 (p 2210) (p 4525) (p 5807) (derived74087 p h) (h 11845)

theorem derived102415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 4988) :=
  ElevenRUP.step102415 (p 3051) (p 4987) (p 4988) (derived73866 p h) (h 8320)

theorem derived102417 (p : Nat → Prop) (h : Inputs p) :
    (p 4172) ∨ (¬ p 2210) :=
  ElevenRUP.step102417 (p 2210) (p 4172) (p 5807) (derived74087 p h) (h 11844)

theorem derived102418 (p : Nat → Prop) (h : Inputs p) :
    (p 4446) ∨ (¬ p 2166) :=
  ElevenRUP.step102418 (p 2166) (p 4446) (p 5795) (derived74071 p h) (h 11772)

theorem derived102419 (p : Nat → Prop) (h : Inputs p) :
    (p 4283) ∨ (¬ p 3051) :=
  ElevenRUP.step102419 (p 3051) (p 4283) (p 5969) (derived74299 p h) (h 12810)

theorem derived102421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 3005) ∨ (¬ p 2307) ∨ (¬ p 4769) ∨ (¬ p 2797) :=
  ElevenRUP.step102421 (p 2307) (p 2797) (p 3005) (p 3567) (p 3877) (p 4769) (derived73488 p h) (derived72312 p h)

theorem derived102424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2319) ∨ (¬ p 4620) ∨ (p 2177) ∨ (p 3323) ∨ (¬ p 3567) :=
  ElevenRUP.step102424 (p 2177) (p 2299) (p 2319) (p 2341) (p 3323) (p 3567) (p 4037) (p 4620) (derived73234 p h) (derived73508 p h) (derived48301 p h)

theorem derived102427 (p : Nat → Prop) (h : Inputs p) :
    (p 2137) ∨ (p 2132) :=
  ElevenRUP.step102427 (p 2132) (p 2137) (p 2141) (derived73215 p h) (h 2416)

theorem derived102428 (p : Nat → Prop) (h : Inputs p) :
    (p 5020) ∨ (¬ p 3093) :=
  ElevenRUP.step102428 (p 3093) (p 5020) (p 5981) (derived74311 p h) (h 12879)

theorem derived102429 (p : Nat → Prop) (h : Inputs p) :
    (p 3919) ∨ (p 2264) :=
  ElevenRUP.step102429 (p 2264) (p 3919) (p 5815) (derived74097 p h) (h 11890)

theorem derived102431 (p : Nat → Prop) (h : Inputs p) :
    (p 4115) ∨ (¬ p 2220) :=
  ElevenRUP.step102431 (p 2220) (p 4115) (p 5810) (derived74091 p h) (h 11863)

theorem derived102432 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3136) ∨ (¬ p 2951) ∨ (¬ p 3212) ∨ (¬ p 5046) ∨ (¬ p 3745) :=
  ElevenRUP.step102432 (p 2797) (p 2951) (p 3136) (p 3212) (p 3745) (p 4195) (p 5046) (derived73532 p h) (derived52760 p h)

theorem derived102434 (p : Nat → Prop) (h : Inputs p) :
    (p 4448) ∨ (p 2992) :=
  ElevenRUP.step102434 (p 2992) (p 4448) (p 5959) (derived74285 p h) (h 12738)

theorem derived102435 (p : Nat → Prop) (h : Inputs p) :
    (p 4397) ∨ (p 3125) :=
  ElevenRUP.step102435 (p 3125) (p 4397) (p 5989) (derived74321 p h) (h 12926)

theorem derived102437 (p : Nat → Prop) (h : Inputs p) :
    (p 3171) ∨ (p 3166) :=
  ElevenRUP.step102437 (p 3166) (p 3171) (p 3175) (derived73357 p h) (h 4466)

theorem derived102439 (p : Nat → Prop) (h : Inputs p) :
    (p 4364) ∨ (p 3005) :=
  ElevenRUP.step102439 (p 3005) (p 4364) (p 5962) (derived74289 p h) (h 12761)

theorem derived102442 (p : Nat → Prop) (h : Inputs p) :
    (p 4849) ∨ (p 2807) :=
  ElevenRUP.step102442 (p 2807) (p 4849) (p 5920) (derived74233 p h) (h 12504)

theorem derived102443 (p : Nat → Prop) (h : Inputs p) :
    (p 4850) ∨ (p 2807) :=
  ElevenRUP.step102443 (p 2807) (p 4850) (p 5920) (derived74233 p h) (h 12505)

theorem derived102447 (p : Nat → Prop) (h : Inputs p) :
    (p 4078) ∨ (p 2819) :=
  ElevenRUP.step102447 (p 2819) (p 4078) (p 5923) (derived74237 p h) (h 12526)

theorem derived102450 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (p 2363) ∨ (¬ p 2811) ∨ (¬ p 4769) ∨ (p 2641) ∨ (¬ p 2331) :=
  ElevenRUP.step102450 (p 2331) (p 2363) (p 2641) (p 2811) (p 3005) (p 3877) (p 4154) (p 4347) (p 4769) (derived73488 p h) (derived73560 p h) (derived73526 p h) (derived57924 p h)

theorem derived102454 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 5586) ∨ (¬ p 2797) ∨ (¬ p 4769) ∨ (p 3005) :=
  ElevenRUP.step102454 (p 2797) (p 3005) (p 3877) (p 4228) (p 4769) (p 5586) (derived73488 p h) (derived42212 p h)

theorem derived102461 (p : Nat → Prop) (h : Inputs p) :
    (p 4963) ∨ (p 3005) :=
  ElevenRUP.step102461 (p 3005) (p 4963) (p 5962) (derived74289 p h) (h 12759)

theorem derived102464 (p : Nat → Prop) (h : Inputs p) :
    (p 5242) ∨ (¬ p 3449) :=
  ElevenRUP.step102464 (p 3449) (p 5242) (p 6056) (derived74399 p h) (h 13341)

theorem derived102465 (p : Nat → Prop) (h : Inputs p) :
    (p 4232) ∨ (p 2132) ∨ (¬ p 5025) :=
  ElevenRUP.step102465 (p 2132) (p 2138) (p 4232) (p 5025) (derived73214 p h) (h 31905)

theorem derived102471 (p : Nat → Prop) (h : Inputs p) :
    (p 5148) ∨ (p 3319) :=
  ElevenRUP.step102471 (p 3319) (p 5148) (p 6025) (derived74365 p h) (h 13144)

theorem derived102478 (p : Nat → Prop) (h : Inputs p) :
    (p 3599) ∨ (p 5329) :=
  ElevenRUP.step102478 (p 3599) (p 5327) (p 5329) (derived74004 p h) (h 9159)

theorem derived102480 (p : Nat → Prop) (h : Inputs p) :
    (p 4029) ∨ (p 3599) :=
  ElevenRUP.step102480 (p 3599) (p 4029) (p 6085) (derived74429 p h) (h 13618)

theorem derived102484 (p : Nat → Prop) (h : Inputs p) :
    (p 4311) ∨ (¬ p 3156) :=
  ElevenRUP.step102484 (p 3156) (p 4311) (p 5999) (derived74335 p h) (h 12980)

theorem derived102487 (p : Nat → Prop) (h : Inputs p) :
    (p 4429) ∨ (p 2449) :=
  ElevenRUP.step102487 (p 2449) (p 4429) (p 5860) (derived74157 p h) (h 12153)

theorem derived102489 (p : Nat → Prop) (h : Inputs p) :
    (p 4656) ∨ (p 2449) :=
  ElevenRUP.step102489 (p 2449) (p 4656) (p 5860) (derived74157 p h) (h 12151)

theorem derived102490 (p : Nat → Prop) (h : Inputs p) :
    (p 4988) ∨ (¬ p 3051) :=
  ElevenRUP.step102490 (p 3051) (p 4988) (p 5969) (derived74299 p h) (h 12808)

theorem derived102492 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (p 3146) :=
  ElevenRUP.step102492 (p 3146) (p 4450) (p 5995) (derived74329 p h) (h 12961)

theorem derived102493 (p : Nat → Prop) (h : Inputs p) :
    (p 3904) ∨ (p 2230) :=
  ElevenRUP.step102493 (p 2230) (p 3904) (p 5812) (derived74093 p h) (h 11874)

theorem derived102494 (p : Nat → Prop) (h : Inputs p) :
    (p 4349) ∨ (p 3256) :=
  ElevenRUP.step102494 (p 3256) (p 4349) (p 6013) (derived74349 p h) (h 13075)

theorem derived102495 (p : Nat → Prop) (h : Inputs p) :
    (p 5107) ∨ (p 3256) :=
  ElevenRUP.step102495 (p 3256) (p 5107) (p 6013) (derived74349 p h) (h 13073)

theorem derived102496 (p : Nat → Prop) (h : Inputs p) :
    (p 3573) ∨ (p 2352) :=
  ElevenRUP.step102496 (p 2352) (p 3573) (p 5833) (derived74121 p h) (h 11993)

theorem derived102499 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5514) ∨ (p 2573) ∨ (p 2187) :=
  ElevenRUP.step102499 (p 2187) (p 2573) (p 2579) (p 3737) (p 3989) (p 5514) (derived73274 p h) (derived73502 p h) (derived43053 p h)

theorem derived102500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 5514) ∨ (¬ p 4196) ∨ (¬ p 3146) ∨ (p 3256) :=
  ElevenRUP.step102500 (p 3146) (p 3256) (p 4118) (p 4196) (p 4228) (p 5514) (derived73520 p h) (derived47925 p h)

theorem derived102502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4053) ∨ (¬ p 5514) ∨ (p 2406) ∨ (¬ p 2505) ∨ (¬ p 4717) :=
  ElevenRUP.step102502 (p 2406) (p 2505) (p 3238) (p 4053) (p 4717) (p 5514) (derived73374 p h) (derived42564 p h)

theorem derived102503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3737) ∨ (¬ p 5514) ∨ (p 3422) ∨ (p 2187) :=
  ElevenRUP.step102503 (p 2187) (p 3422) (p 3584) (p 3737) (p 3989) (p 5514) (derived73426 p h) (derived73502 p h) (derived56054 p h)

theorem derived102504 (p : Nat → Prop) (h : Inputs p) :
    (p 2950) ∨ (p 2946) :=
  ElevenRUP.step102504 (p 2946) (p 2950) (p 2955) (derived73331 p h) (h 4034)

theorem derived102506 (p : Nat → Prop) (h : Inputs p) :
    (p 3959) ∨ (p 3425) :=
  ElevenRUP.step102506 (p 3425) (p 3959) (p 6062) (derived74407 p h) (h 13381)

theorem derived102507 (p : Nat → Prop) (h : Inputs p) :
    (p 3545) ∨ (¬ p 3399) :=
  ElevenRUP.step102507 (p 3399) (p 3545) (p 6044) (derived74383 p h) (h 13263)

theorem derived102508 (p : Nat → Prop) (h : Inputs p) :
    (p 4550) ∨ (p 2264) :=
  ElevenRUP.step102508 (p 2264) (p 4550) (p 5815) (derived74097 p h) (h 11892)

theorem derived102509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (¬ p 3767) ∨ (¬ p 4790) ∨ (¬ p 3178) ∨ (p 3755) ∨ (¬ p 4461) :=
  ElevenRUP.step102509 (p 3178) (p 3755) (p 3767) (p 4035) (p 4461) (p 4790) (p 5284) (derived73506 p h) (derived53047 p h)

theorem derived102510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5284) ∨ (p 3755) ∨ (¬ p 4207) ∨ (¬ p 3767) ∨ (¬ p 4790) ∨ (¬ p 2958) :=
  ElevenRUP.step102510 (p 2958) (p 3755) (p 3767) (p 4035) (p 4207) (p 4790) (p 5284) (derived73506 p h) (derived61373 p h)

theorem derived102514 (p : Nat → Prop) (h : Inputs p) :
    (p 4658) ∨ (p 2449) :=
  ElevenRUP.step102514 (p 2449) (p 4658) (p 5860) (derived74157 p h) (h 12155)

theorem derived102515 (p : Nat → Prop) (h : Inputs p) :
    (p 3846) ∨ (¬ p 3845) :=
  ElevenRUP.step102515 (p 3845) (p 3846) (p 3851) (derived73475 p h) (h 5686)

theorem derived102516 (p : Nat → Prop) (h : Inputs p) :
    (p 4238) ∨ (¬ p 2220) :=
  ElevenRUP.step102516 (p 2220) (p 4238) (p 5810) (derived74091 p h) (h 11861)

theorem derived102517 (p : Nat → Prop) (h : Inputs p) :
    (p 5370) ∨ (p 3641) :=
  ElevenRUP.step102517 (p 3641) (p 5370) (p 6097) (derived74441 p h) (h 13700)

theorem derived102518 (p : Nat → Prop) (h : Inputs p) :
    (p 4859) ∨ (p 2819) :=
  ElevenRUP.step102518 (p 2819) (p 4859) (p 5923) (derived74237 p h) (h 12528)

theorem derived102519 (p : Nat → Prop) (h : Inputs p) :
    (p 5197) ∨ (p 3389) :=
  ElevenRUP.step102519 (p 3389) (p 5197) (p 6040) (derived74377 p h) (h 13238)

theorem derived102520 (p : Nat → Prop) (h : Inputs p) :
    (p 2577) ∨ (p 2573) :=
  ElevenRUP.step102520 (p 2573) (p 2577) (p 2582) (derived73275 p h) (h 3284)

theorem derived102521 (p : Nat → Prop) (h : Inputs p) :
    (p 2136) ∨ (p 2132) :=
  ElevenRUP.step102521 (p 2132) (p 2136) (p 2141) (derived73215 p h) (h 2413)

theorem derived102523 (p : Nat → Prop) (h : Inputs p) :
    (p 5339) ∨ (p 3609) :=
  ElevenRUP.step102523 (p 3609) (p 5339) (p 6088) (derived74433 p h) (h 13632)

theorem derived102524 (p : Nat → Prop) (h : Inputs p) :
    (p 5338) ∨ (p 3609) :=
  ElevenRUP.step102524 (p 3609) (p 5338) (p 6088) (derived74433 p h) (h 13634)

theorem derived102525 (p : Nat → Prop) (h : Inputs p) :
    (p 4436) ∨ (p 3537) :=
  ElevenRUP.step102525 (p 3537) (p 4436) (p 6079) (derived74421 p h) (h 13507)

theorem derived102527 (p : Nat → Prop) (h : Inputs p) :
    (p 4875) ∨ (p 2839) :=
  ElevenRUP.step102527 (p 2839) (p 4875) (p 5929) (derived74245 p h) (h 12560)

theorem derived102528 (p : Nat → Prop) (h : Inputs p) :
    (p 5369) ∨ (p 3641) :=
  ElevenRUP.step102528 (p 3641) (p 5369) (p 6097) (derived74441 p h) (h 13697)

theorem derived102534 (p : Nat → Prop) (h : Inputs p) :
    (p 3291) ∨ (p 3286) :=
  ElevenRUP.step102534 (p 3286) (p 3291) (p 3295) (derived73379 p h) (h 4707)

theorem derived102536 (p : Nat → Prop) (h : Inputs p) :
    (p 4133) ∨ (p 2177) :=
  ElevenRUP.step102536 (p 2177) (p 4133) (p 5797) (derived74073 p h) (h 11787)

theorem derived102537 (p : Nat → Prop) (h : Inputs p) :
    (p 4744) ∨ (¬ p 2619) :=
  ElevenRUP.step102537 (p 2619) (p 4744) (p 5888) (derived74191 p h) (h 12315)

theorem derived102538 (p : Nat → Prop) (h : Inputs p) :
    (p 4190) ∨ (p 3323) :=
  ElevenRUP.step102538 (p 3323) (p 4190) (p 6067) (derived74409 p h) (h 13423)

theorem derived102539 (p : Nat → Prop) (h : Inputs p) :
    (p 5274) ∨ (p 3323) :=
  ElevenRUP.step102539 (p 3323) (p 5274) (p 6067) (derived74409 p h) (h 13425)

theorem derived102540 (p : Nat → Prop) (h : Inputs p) :
    (p 5276) ∨ (p 3323) :=
  ElevenRUP.step102540 (p 3323) (p 5276) (p 6067) (derived74409 p h) (h 13427)

theorem derived102541 (p : Nat → Prop) (h : Inputs p) :
    (p 4374) ∨ (¬ p 3830) :=
  ElevenRUP.step102541 (p 3830) (p 4374) (p 6128) (derived74463 p h) (h 14013)

theorem derived102542 (p : Nat → Prop) (h : Inputs p) :
    (p 5379) ∨ (p 3654) :=
  ElevenRUP.step102542 (p 3654) (p 5379) (p 6100) (derived74445 p h) (h 13729)

theorem derived102543 (p : Nat → Prop) (h : Inputs p) :
    (p 4771) ∨ (p 2668) :=
  ElevenRUP.step102543 (p 2668) (p 4771) (p 5896) (derived74201 p h) (h 12364)

theorem derived102544 (p : Nat → Prop) (h : Inputs p) :
    (p 5261) ∨ (p 3425) :=
  ElevenRUP.step102544 (p 3425) (p 5261) (p 6062) (derived74407 p h) (h 13383)

theorem derived102546 (p : Nat → Prop) (h : Inputs p) :
    (p 4205) ∨ (p 3125) :=
  ElevenRUP.step102546 (p 3125) (p 4205) (p 5989) (derived74321 p h) (h 12924)

theorem derived102547 (p : Nat → Prop) (h : Inputs p) :
    (p 4953) ∨ (¬ p 2982) :=
  ElevenRUP.step102547 (p 2982) (p 4953) (p 5957) (derived74283 p h) (h 12728)

theorem derived102549 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 3093) :=
  ElevenRUP.step102549 (p 3093) (p 5021) (p 5981) (derived74311 p h) (h 12877)

theorem derived102550 (p : Nat → Prop) (h : Inputs p) :
    (p 4498) ∨ (¬ p 2166) :=
  ElevenRUP.step102550 (p 2166) (p 4498) (p 5795) (derived74071 p h) (h 11776)

theorem derived102551 (p : Nat → Prop) (h : Inputs p) :
    (p 2103) ∨ (p 2098) :=
  ElevenRUP.step102551 (p 2098) (p 2103) (p 2107) (derived73205 p h) (h 2343)

theorem derived102553 (p : Nat → Prop) (h : Inputs p) :
    (p 4440) ∨ (p 2528) :=
  ElevenRUP.step102553 (p 2528) (p 4440) (p 5869) (derived74165 p h) (h 12205)

theorem derived102554 (p : Nat → Prop) (h : Inputs p) :
    (p 3579) ∨ (¬ p 2437) :=
  ElevenRUP.step102554 (p 2437) (p 3579) (p 5858) (derived74155 p h) (h 12140)

theorem derived102555 (p : Nat → Prop) (h : Inputs p) :
    (p 2139) ∨ (p 2132) :=
  ElevenRUP.step102555 (p 2132) (p 2139) (p 2141) (derived73215 p h) (h 2412)

theorem derived102556 (p : Nat → Prop) (h : Inputs p) :
    (p 4914) ∨ (¬ p 2891) :=
  ElevenRUP.step102556 (p 2891) (p 4914) (p 5945) (derived74267 p h) (h 12657)

theorem derived102557 (p : Nat → Prop) (h : Inputs p) :
    (p 4777) ∨ (p 2685) :=
  ElevenRUP.step102557 (p 2685) (p 4777) (p 5899) (derived74205 p h) (h 12377)

theorem derived102559 (p : Nat → Prop) (h : Inputs p) :
    (p 5199) ∨ (p 3389) :=
  ElevenRUP.step102559 (p 3389) (p 5199) (p 6040) (derived74377 p h) (h 13239)

theorem derived102560 (p : Nat → Prop) (h : Inputs p) :
    (p 5142) ∨ (p 3309) :=
  ElevenRUP.step102560 (p 3309) (p 5142) (p 6022) (derived74361 p h) (h 13131)

theorem derived102561 (p : Nat → Prop) (h : Inputs p) :
    (p 3440) ∨ (p 3073) :=
  ElevenRUP.step102561 (p 3073) (p 3440) (p 5974) (derived74301 p h) (h 12836)

theorem derived102563 (p : Nat → Prop) (h : Inputs p) :
    (p 5102) ∨ (p 3246) :=
  ElevenRUP.step102563 (p 3246) (p 5102) (p 6010) (derived74345 p h) (h 13056)

theorem derived102564 (p : Nat → Prop) (h : Inputs p) :
    (p 4653) ∨ (¬ p 2437) :=
  ElevenRUP.step102564 (p 2437) (p 4653) (p 5858) (derived74155 p h) (h 12144)

theorem derived102565 (p : Nat → Prop) (h : Inputs p) :
    (p 4810) ∨ (p 2727) :=
  ElevenRUP.step102565 (p 2727) (p 4810) (p 5911) (derived74221 p h) (h 12450)

theorem derived102571 (p : Nat → Prop) (h : Inputs p) :
    (p 5210) ∨ (¬ p 3399) :=
  ElevenRUP.step102571 (p 3399) (p 5210) (p 6044) (derived74383 p h) (h 13259)

theorem derived102575 (p : Nat → Prop) (h : Inputs p) :
    (p 3858) ∨ (¬ p 3449) :=
  ElevenRUP.step102575 (p 3449) (p 3858) (p 6056) (derived74399 p h) (h 13340)

theorem derived102578 (p : Nat → Prop) (h : Inputs p) :
    (p 5038) ∨ (¬ p 3115) :=
  ElevenRUP.step102578 (p 3115) (p 5038) (p 5987) (derived74319 p h) (h 12912)

theorem derived102581 (p : Nat → Prop) (h : Inputs p) :
    (p 4637) ∨ (p 2417) :=
  ElevenRUP.step102581 (p 2417) (p 4637) (p 5851) (derived74145 p h) (h 12103)

theorem derived102583 (p : Nat → Prop) (h : Inputs p) :
    (p 4332) ∨ (p 2528) :=
  ElevenRUP.step102583 (p 2528) (p 4332) (p 5869) (derived74165 p h) (h 12209)

theorem derived102584 (p : Nat → Prop) (h : Inputs p) :
    (p 2501) ∨ (p 2493) :=
  ElevenRUP.step102584 (p 2493) (p 2501) (p 2502) (derived73261 p h) (h 3131)

theorem derived102586 (p : Nat → Prop) (h : Inputs p) :
    (p 4870) ∨ (¬ p 2829) :=
  ElevenRUP.step102586 (p 2829) (p 4870) (p 5927) (derived74243 p h) (h 12549)

theorem derived102587 (p : Nat → Prop) (h : Inputs p) :
    (p 4636) ∨ (p 2417) :=
  ElevenRUP.step102587 (p 2417) (p 4636) (p 5851) (derived74145 p h) (h 12100)

theorem derived102591 (p : Nat → Prop) (h : Inputs p) :
    (p 4901) ∨ (p 2881) :=
  ElevenRUP.step102591 (p 2881) (p 4901) (p 5941) (derived74261 p h) (h 12633)

theorem derived102592 (p : Nat → Prop) (h : Inputs p) :
    (p 5065) ∨ (¬ p 3156) :=
  ElevenRUP.step102592 (p 3156) (p 5065) (p 5999) (derived74335 p h) (h 12983)

theorem derived102594 (p : Nat → Prop) (h : Inputs p) :
    (p 5321) ∨ (p 3564) :=
  ElevenRUP.step102594 (p 3564) (p 5321) (p 6082) (derived74425 p h) (h 13546)

theorem derived102595 (p : Nat → Prop) (h : Inputs p) :
    (p 5322) ∨ (p 3564) :=
  ElevenRUP.step102595 (p 3564) (p 5322) (p 6082) (derived74425 p h) (h 13547)

theorem derived102596 (p : Nat → Prop) (h : Inputs p) :
    (p 5131) ∨ (¬ p 3276) :=
  ElevenRUP.step102596 (p 3276) (p 5131) (p 6020) (derived74359 p h) (h 13114)

theorem derived102597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3807) ∨ (¬ p 3901) ∨ (p 3379) ∨ (p 3016) :=
  ElevenRUP.step102597 (p 3016) (p 3379) (p 3452) (p 3574) (p 3807) (p 3901) (derived73394 p h) (derived73422 p h) (derived44697 p h)

theorem derived102605 (p : Nat → Prop) (h : Inputs p) :
    (p 4746) ∨ (¬ p 2619) :=
  ElevenRUP.step102605 (p 2619) (p 4746) (p 5888) (derived74191 p h) (h 12318)

theorem derived102606 (p : Nat → Prop) (h : Inputs p) :
    (p 4952) ∨ (¬ p 2982) :=
  ElevenRUP.step102606 (p 2982) (p 4952) (p 5957) (derived74283 p h) (h 12725)

theorem derived102607 (p : Nat → Prop) (h : Inputs p) :
    (p 5674) ∨ (¬ p 4149) :=
  ElevenRUP.step102607 (p 4149) (p 5674) (p 6176) (derived74467 p h) (h 15086)

theorem derived102611 (p : Nat → Prop) (h : Inputs p) :
    (p 4043) ∨ (¬ p 3156) :=
  ElevenRUP.step102611 (p 3156) (p 4043) (p 5999) (derived74335 p h) (h 12984)

theorem derived102612 (p : Nat → Prop) (h : Inputs p) :
    (p 5454) ∨ (p 3755) :=
  ElevenRUP.step102612 (p 3755) (p 5454) (p 6121) (derived74457 p h) (h 13913)

theorem derived102616 (p : Nat → Prop) (h : Inputs p) :
    (p 5312) ∨ (p 3537) :=
  ElevenRUP.step102616 (p 3537) (p 5312) (p 6079) (derived74421 p h) (h 13504)

theorem derived102617 (p : Nat → Prop) (h : Inputs p) :
    (p 4353) ∨ (p 3537) :=
  ElevenRUP.step102617 (p 3537) (p 4353) (p 6079) (derived74421 p h) (h 13506)

theorem derived102623 (p : Nat → Prop) (h : Inputs p) :
    (p 5229) ∨ (p 3434) :=
  ElevenRUP.step102623 (p 3434) (p 5229) (p 6052) (derived74393 p h) (h 13310)

theorem derived102624 (p : Nat → Prop) (h : Inputs p) :
    (p 5228) ∨ (p 3434) :=
  ElevenRUP.step102624 (p 3434) (p 5228) (p 6052) (derived74393 p h) (h 13312)

theorem derived102628 (p : Nat → Prop) (h : Inputs p) :
    (p 4439) ∨ (¬ p 3830) :=
  ElevenRUP.step102628 (p 3830) (p 4439) (p 6128) (derived74463 p h) (h 14014)

theorem derived102632 (p : Nat → Prop) (h : Inputs p) :
    (p 5413) ∨ (¬ p 3707) :=
  ElevenRUP.step102632 (p 3707) (p 5413) (p 6110) (derived74455 p h) (h 13832)

theorem derived102633 (p : Nat → Prop) (h : Inputs p) :
    (p 5414) ∨ (¬ p 3707) :=
  ElevenRUP.step102633 (p 3707) (p 5414) (p 6110) (derived74455 p h) (h 13833)

theorem derived102636 (p : Nat → Prop) (h : Inputs p) :
    (p 5391) ∨ (¬ p 3670) :=
  ElevenRUP.step102636 (p 3670) (p 5391) (p 6104) (derived74451 p h) (h 13770)

theorem derived102640 (p : Nat → Prop) (h : Inputs p) :
    (p 5378) ∨ (p 3654) :=
  ElevenRUP.step102640 (p 3654) (p 5378) (p 6100) (derived74445 p h) (h 13728)

theorem derived102645 (p : Nat → Prop) (h : Inputs p) :
    (p 5294) ∨ (p 3516) :=
  ElevenRUP.step102645 (p 3516) (p 5294) (p 6073) (derived74413 p h) (h 13466)

theorem derived102648 (p : Nat → Prop) (h : Inputs p) :
    (p 5295) ∨ (p 3516) :=
  ElevenRUP.step102648 (p 3516) (p 5295) (p 6073) (derived74413 p h) (h 13470)

theorem derived102649 (p : Nat → Prop) (h : Inputs p) :
    (p 5260) ∨ (p 3425) :=
  ElevenRUP.step102649 (p 3425) (p 5260) (p 6062) (derived74407 p h) (h 13379)

theorem derived102651 (p : Nat → Prop) (h : Inputs p) :
    (p 5175) ∨ (¬ p 3343) :=
  ElevenRUP.step102651 (p 3343) (p 5175) (p 6032) (derived74371 p h) (h 13185)

theorem derived102652 (p : Nat → Prop) (h : Inputs p) :
    (p 5177) ∨ (¬ p 3343) :=
  ElevenRUP.step102652 (p 3343) (p 5177) (p 6032) (derived74371 p h) (h 13188)

theorem derived102655 (p : Nat → Prop) (h : Inputs p) :
    (p 4184) ∨ (¬ p 3276) :=
  ElevenRUP.step102655 (p 3276) (p 4184) (p 6020) (derived74359 p h) (h 13115)

theorem derived102657 (p : Nat → Prop) (h : Inputs p) :
    (p 5133) ∨ (¬ p 3276) :=
  ElevenRUP.step102657 (p 3276) (p 5133) (p 6020) (derived74359 p h) (h 13118)

theorem derived102658 (p : Nat → Prop) (h : Inputs p) :
    (p 5121) ∨ (¬ p 3266) :=
  ElevenRUP.step102658 (p 3266) (p 5121) (p 6017) (derived74355 p h) (h 13097)

theorem derived102660 (p : Nat → Prop) (h : Inputs p) :
    (p 5109) ∨ (p 3256) :=
  ElevenRUP.step102660 (p 3256) (p 5109) (p 6013) (derived74349 p h) (h 13077)

theorem derived102661 (p : Nat → Prop) (h : Inputs p) :
    (p 5082) ∨ (p 3201) :=
  ElevenRUP.step102661 (p 3201) (p 5082) (p 6004) (derived74341 p h) (h 13017)

theorem derived102664 (p : Nat → Prop) (h : Inputs p) :
    (p 5056) ∨ (p 3146) :=
  ElevenRUP.step102664 (p 3146) (p 5056) (p 5995) (derived74329 p h) (h 12960)

theorem derived102665 (p : Nat → Prop) (h : Inputs p) :
    (p 4039) ∨ (¬ p 3115) :=
  ElevenRUP.step102665 (p 3115) (p 4039) (p 5987) (derived74319 p h) (h 12911)

theorem derived102666 (p : Nat → Prop) (h : Inputs p) :
    (p 5039) ∨ (¬ p 3115) :=
  ElevenRUP.step102666 (p 3115) (p 5039) (p 5987) (derived74319 p h) (h 12914)

theorem derived102668 (p : Nat → Prop) (h : Inputs p) :
    (p 5030) ∨ (¬ p 3105) :=
  ElevenRUP.step102668 (p 3105) (p 5030) (p 5984) (derived74315 p h) (h 12893)

theorem derived102669 (p : Nat → Prop) (h : Inputs p) :
    (p 5031) ∨ (¬ p 3105) :=
  ElevenRUP.step102669 (p 3105) (p 5031) (p 5984) (derived74315 p h) (h 12894)

theorem derived102672 (p : Nat → Prop) (h : Inputs p) :
    (p 3438) ∨ (p 3073) :=
  ElevenRUP.step102672 (p 3073) (p 3438) (p 5974) (derived74301 p h) (h 12834)

theorem derived102677 (p : Nat → Prop) (h : Inputs p) :
    (p 4387) ∨ (¬ p 2972) :=
  ElevenRUP.step102677 (p 2972) (p 4387) (p 5954) (derived74279 p h) (h 12707)

theorem derived102680 (p : Nat → Prop) (h : Inputs p) :
    (p 4919) ∨ (¬ p 2901) :=
  ElevenRUP.step102680 (p 2901) (p 4919) (p 5948) (derived74271 p h) (h 12673)

theorem derived102683 (p : Nat → Prop) (h : Inputs p) :
    (p 4828) ∨ (¬ p 2761) :=
  ElevenRUP.step102683 (p 2761) (p 4828) (p 5915) (derived74227 p h) (h 12471)

theorem derived102684 (p : Nat → Prop) (h : Inputs p) :
    (p 4830) ∨ (¬ p 2761) :=
  ElevenRUP.step102684 (p 2761) (p 4830) (p 5915) (derived74227 p h) (h 12474)

theorem derived102685 (p : Nat → Prop) (h : Inputs p) :
    (p 4797) ∨ (¬ p 2707) :=
  ElevenRUP.step102685 (p 2707) (p 4797) (p 5906) (derived74215 p h) (h 12419)

theorem derived102691 (p : Nat → Prop) (h : Inputs p) :
    (p 4614) ∨ (p 2383) :=
  ElevenRUP.step102691 (p 2383) (p 4614) (p 5842) (derived74133 p h) (h 12050)

theorem derived102693 (p : Nat → Prop) (h : Inputs p) :
    (p 4588) ∨ (p 2341) :=
  ElevenRUP.step102693 (p 2341) (p 4588) (p 5830) (derived74117 p h) (h 11978)

theorem derived102694 (p : Nat → Prop) (h : Inputs p) :
    (p 4580) ∨ (p 2331) :=
  ElevenRUP.step102694 (p 2331) (p 4580) (p 5827) (derived74113 p h) (h 11960)

theorem derived102696 (p : Nat → Prop) (h : Inputs p) :
    (p 4569) ∨ (p 2295) :=
  ElevenRUP.step102696 (p 2295) (p 4569) (p 5824) (derived74109 p h) (h 11943)

theorem derived102703 (p : Nat → Prop) (h : Inputs p) :
    (p 4472) ∨ (p 2122) :=
  ElevenRUP.step102703 (p 2122) (p 4472) (p 5788) (derived74061 p h) (h 11734)

theorem derived102704 (p : Nat → Prop) (h : Inputs p) :
    (p 4456) ∨ (p 2088) :=
  ElevenRUP.step102704 (p 2088) (p 4456) (p 5785) (derived74057 p h) (h 11714)

theorem derived102705 (p : Nat → Prop) (h : Inputs p) :
    (p 4455) ∨ (p 2088) :=
  ElevenRUP.step102705 (p 2088) (p 4455) (p 5785) (derived74057 p h) (h 11715)

theorem derived102792 (p : Nat → Prop) (h : Inputs p) :
    (p 3847) ∨ (¬ p 3845) :=
  ElevenRUP.step102792 (p 3845) (p 3847) (p 3851) (derived73475 p h) (h 5685)

theorem derived102798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3811) ∨ (p 5481) :=
  ElevenRUP.step102798 (p 3811) (p 3816) (p 5481) (derived73465 p h) (h 9508)

theorem derived102803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3804) ∨ (p 5480) :=
  ElevenRUP.step102803 (p 3804) (p 3810) (p 5480) (derived73463 p h) (h 9504)

theorem derived102812 (p : Nat → Prop) (h : Inputs p) :
    (p 3229) ∨ (¬ p 3193) :=
  ElevenRUP.step102812 (p 3193) (p 3229) (p 3230) (derived73367 p h) (h 4576)

theorem derived102813 (p : Nat → Prop) (h : Inputs p) :
    (p 3226) ∨ (¬ p 3193) :=
  ElevenRUP.step102813 (p 3193) (p 3226) (p 3230) (derived73367 p h) (h 4579)

theorem derived102816 (p : Nat → Prop) (h : Inputs p) :
    (p 3034) ∨ (¬ p 2996) :=
  ElevenRUP.step102816 (p 2996) (p 3034) (p 3035) (derived73343 p h) (h 4189)

theorem derived102822 (p : Nat → Prop) (h : Inputs p) :
    (p 2478) ∨ (p 2470) :=
  ElevenRUP.step102822 (p 2470) (p 2478) (p 2479) (derived73251 p h) (h 3083)

theorem derived102827 (p : Nat → Prop) (h : Inputs p) :
    (p 2102) ∨ (p 2098) :=
  ElevenRUP.step102827 (p 2098) (p 2102) (p 2107) (derived73205 p h) (h 2346)

theorem derived102828 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (p 2284) ∨ (¬ p 2192) :=
  ElevenRUP.step102828 (p 2192) (p 2284) (p 2727) (p 3952) (p 4111) (p 4173) (p 4704) (derived73518 p h) (derived73496 p h) (derived73527 p h) (derived73046 p h) (derived67933 p h)

theorem derived102837 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2274) ∨ (¬ p 3389) ∨ (¬ p 4718) ∨ (p 2230) :=
  ElevenRUP.step102837 (p 2230) (p 2274) (p 2553) (p 2589) (p 3097) (p 3389) (p 4709) (p 4718) (derived73718 p h) (derived73352 p h) (derived73284 p h) (derived67551 p h)

theorem derived102838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2881) ∨ (¬ p 2177) :=
  ElevenRUP.step102838 (p 2177) (p 2295) (p 2881) (p 3568) (derived73415 p h) (derived67448 p h)

theorem derived102840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (p 2797) ∨ (p 2440) ∨ (¬ p 2630) ∨ (¬ p 4389) ∨ (¬ p 4715) :=
  ElevenRUP.step102840 (p 2440) (p 2542) (p 2630) (p 2651) (p 2797) (p 4195) (p 4389) (p 4715) (derived73532 p h) (derived73270 p h) (derived67793 p h)

theorem derived102841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2274) ∨ (¬ p 2493) ∨ (¬ p 2696) ∨ (¬ p 2578) ∨ (¬ p 2630) ∨ (¬ p 4389) ∨ (¬ p 4814) ∨ (¬ p 4194) :=
  ElevenRUP.step102841 (p 2274) (p 2307) (p 2493) (p 2578) (p 2630) (p 2696) (p 3097) (p 4194) (p 4389) (p 4814) (derived73352 p h) (derived67534 p h)

theorem derived102842 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2177) ∨ (¬ p 3609) ∨ (¬ p 2132) ∨ (p 2459) ∨ (¬ p 4509) ∨ (¬ p 2274) :=
  ElevenRUP.step102842 (p 2132) (p 2177) (p 2274) (p 2299) (p 2459) (p 2881) (p 3609) (p 4509) (p 4557) (p 4665) (p 4903) (derived73820 p h) (derived73234 p h) (derived73696 p h) (derived73636 p h) (derived68257 p h)

theorem derived102843 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2696) ∨ (p 2630) :=
  ElevenRUP.step102843 (p 2132) (p 2630) (p 2696) (p 2810) (p 3365) (p 4704) (derived73390 p h) (derived73316 p h) (derived73046 p h) (derived67974 p h)

theorem derived102848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 3016) ∨ (p 3367) ∨ (¬ p 4753) :=
  ElevenRUP.step102848 (p 2829) (p 3016) (p 3367) (p 3574) (p 3585) (p 4753) (derived73422 p h) (derived73428 p h) (derived67852 p h)

theorem derived102850 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 2829) ∨ (¬ p 2187) ∨ (¬ p 4889) :=
  ElevenRUP.step102850 (p 2187) (p 2829) (p 3537) (p 4242) (p 4889) (derived73538 p h) (derived67881 p h)

theorem derived102851 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2122) ∨ (p 2737) ∨ (¬ p 4328) ∨ (¬ p 2177) :=
  ElevenRUP.step102851 (p 2122) (p 2177) (p 2737) (p 2743) (p 2829) (p 4328) (derived73298 p h) (derived67839 p h)

theorem derived102852 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2829) ∨ (¬ p 2230) ∨ (¬ p 2598) :=
  ElevenRUP.step102852 (p 2230) (p 2598) (p 2774) (p 2829) (p 4728) (derived73730 p h) (derived67931 p h)

theorem derived102853 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2608) ∨ (p 2630) ∨ (¬ p 2737) ∨ (¬ p 2797) :=
  ElevenRUP.step102853 (p 2122) (p 2608) (p 2630) (p 2737) (p 2797) (p 2810) (p 4844) (derived73316 p h) (derived73788 p h) (derived67869 p h)

theorem derived102854 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2696) ∨ (¬ p 3609) ∨ (¬ p 2737) :=
  ElevenRUP.step102854 (p 2098) (p 2696) (p 2737) (p 3365) (p 3609) (derived73390 p h) (derived68206 p h)

theorem derived102856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3698) ∨ (p 2850) ∨ (p 2839) ∨ (¬ p 4730) ∨ (¬ p 2230) ∨ (¬ p 3362) :=
  ElevenRUP.step102856 (p 2230) (p 2839) (p 2850) (p 3362) (p 3583) (p 3684) (p 3698) (p 4730) (derived73442 p h) (derived73424 p h) (derived72320 p h)

theorem derived102857 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 3367) ∨ (p 2608) ∨ (¬ p 2230) ∨ (¬ p 2210) :=
  ElevenRUP.step102857 (p 2210) (p 2230) (p 2608) (p 2850) (p 3367) (p 3684) (p 3954) (p 5215) (derived73442 p h) (derived73962 p h) (derived73498 p h) (derived68094 p h)

theorem derived102858 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2230) ∨ (¬ p 5217) ∨ (p 3379) ∨ (¬ p 2210) :=
  ElevenRUP.step102858 (p 2210) (p 2230) (p 2850) (p 3379) (p 3684) (p 5189) (p 5217) (derived73442 p h) (derived73948 p h) (derived68093 p h)

theorem derived102859 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2210) ∨ (¬ p 2651) ∨ (p 2608) ∨ (¬ p 2241) ∨ (¬ p 2750) :=
  ElevenRUP.step102859 (p 2210) (p 2241) (p 2251) (p 2608) (p 2651) (p 2657) (p 2750) (p 2946) (p 2952) (p 3555) (p 3954) (derived73330 p h) (derived73412 p h) (derived73287 p h) (derived73498 p h) (derived73230 p h) (derived67516 p h)

theorem derived102861 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4807) ∨ (¬ p 3609) ∨ (¬ p 2881) :=
  ElevenRUP.step102861 (p 2881) (p 3246) (p 3609) (p 3690) (p 4807) (derived73446 p h) (derived67759 p h)

theorem derived102864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 3201) ∨ (¬ p 3051) ∨ (¬ p 4730) ∨ (p 2427) :=
  ElevenRUP.step102864 (p 2427) (p 2891) (p 3051) (p 3201) (p 3876) (p 4643) (p 4730) (derived73486 p h) (derived73684 p h) (derived67403 p h)

theorem derived102866 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2190) ∨ (¬ p 2563) ∨ (¬ p 2727) ∨ (p 2220) ∨ (¬ p 2651) ∨ (p 3016) :=
  ElevenRUP.step102866 (p 2190) (p 2220) (p 2563) (p 2641) (p 2651) (p 2727) (p 3016) (p 4120) (p 4154) (p 4716) (derived73526 p h) (derived73722 p h) (derived73522 p h) (derived67774 p h)

theorem derived102867 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2156) ∨ (¬ p 2563) ∨ (¬ p 2651) :=
  ElevenRUP.step102867 (p 2156) (p 2563) (p 2651) (p 2946) (p 2949) (p 3646) (derived73328 p h) (derived73436 p h) (derived69710 p h)

theorem derived102868 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (p 2608) ∨ (¬ p 2651) ∨ (¬ p 2750) :=
  ElevenRUP.step102868 (p 2608) (p 2651) (p 2727) (p 2750) (p 3954) (p 4111) (derived73518 p h) (derived73498 p h) (derived68054 p h)

theorem derived102869 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2651) ∨ (¬ p 4715) ∨ (p 2440) :=
  ElevenRUP.step102869 (p 2331) (p 2440) (p 2542) (p 2651) (p 4715) (derived73270 p h) (derived67886 p h)

theorem derived102871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2210) ∨ (¬ p 2663) ∨ (¬ p 3955) ∨ (¬ p 4902) ∨ (p 3146) ∨ (¬ p 2839) ∨ (¬ p 2696) ∨ (¬ p 2230) ∨ (¬ p 2132) ∨ (¬ p 4433) ∨ (p 2274) ∨ (¬ p 4814) ∨ (¬ p 2088) ∨ (¬ p 3988) ∨ (¬ p 2284) ∨ (¬ p 2459) ∨ (¬ p 2651) ∨ (¬ p 2619) ∨ (¬ p 4489) ∨ (¬ p 2563) :=
  ElevenRUP.step102871 (p 2088) (p 2132) (p 2210) (p 2230) (p 2274) (p 2284) (p 2307) (p 2459) (p 2563) (p 2619) (p 2651) (p 2663) (p 2696) (p 2839) (p 3097) (p 3146) (p 3955) (p 3988) (p 4433) (p 4489) (p 4788) (p 4814) (p 4902) (p 5055) (derived73896 p h) (derived73760 p h) (derived73352 p h) (derived67624 p h)

theorem derived102872 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2651) ∨ (p 2598) :=
  ElevenRUP.step102872 (p 2598) (p 2630) (p 2651) (p 3055) (p 4748) (derived73740 p h) (derived73350 p h) (derived67393 p h)

theorem derived102873 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2230) ∨ (¬ p 2651) :=
  ElevenRUP.step102873 (p 2230) (p 2651) (p 2661) (p 2946) (p 2949) (p 4537) (derived73328 p h) (derived73624 p h) (derived73292 p h) (derived67499 p h)

theorem derived102874 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3389) ∨ (¬ p 2651) ∨ (p 2230) ∨ (¬ p 4646) :=
  ElevenRUP.step102874 (p 2230) (p 2589) (p 2651) (p 2661) (p 2946) (p 2952) (p 3389) (p 4646) (derived73330 p h) (derived73292 p h) (derived73284 p h) (derived67497 p h)

theorem derived102883 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2331) ∨ (p 2668) ∨ (¬ p 3136) ∨ (¬ p 2187) ∨ (¬ p 4790) :=
  ElevenRUP.step102883 (p 2187) (p 2331) (p 2668) (p 2797) (p 3136) (p 3324) (p 4195) (p 4582) (p 4790) (derived73532 p h) (derived73650 p h) (derived73386 p h) (derived67716 p h)

theorem derived102884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4365) ∨ (p 2331) ∨ (¬ p 3745) ∨ (¬ p 4960) ∨ (p 2284) ∨ (¬ p 2192) ∨ (¬ p 2249) :=
  ElevenRUP.step102884 (p 2192) (p 2249) (p 2284) (p 2331) (p 2963) (p 3745) (p 3952) (p 4365) (p 4960) (derived73338 p h) (derived73496 p h) (derived67660 p h)

theorem derived102887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2363) ∨ (¬ p 3487) ∨ (¬ p 4610) ∨ (¬ p 2440) ∨ (¬ p 2510) ∨ (p 2406) ∨ (¬ p 3016) :=
  ElevenRUP.step102887 (p 2363) (p 2406) (p 2440) (p 2510) (p 3016) (p 3073) (p 3238) (p 3487) (p 4347) (p 4610) (derived73560 p h) (derived73374 p h) (derived67608 p h)

theorem derived102889 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2881) ∨ (¬ p 2088) :=
  ElevenRUP.step102889 (p 2088) (p 2459) (p 2881) (p 3570) (p 4348) (derived73562 p h) (derived73418 p h) (derived68274 p h)

theorem derived102890 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (p 2241) ∨ (¬ p 2098) ∨ (¬ p 2608) :=
  ElevenRUP.step102890 (p 2098) (p 2241) (p 2247) (p 2608) (p 3537) (p 4242) (p 4735) (derived73538 p h) (derived73226 p h) (derived73734 p h) (derived67772 p h)

theorem derived102891 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2608) ∨ (¬ p 2696) ∨ (¬ p 3589) :=
  ElevenRUP.step102891 (p 2241) (p 2247) (p 2608) (p 2696) (p 3589) (derived73226 p h) (derived67786 p h)

theorem derived102894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2274) ∨ (¬ p 3166) ∨ (p 2187) :=
  ElevenRUP.step102894 (p 2187) (p 2274) (p 2668) (p 3166) (p 3989) (p 4560) (p 4772) (derived73752 p h) (derived72955 p h) (derived73502 p h) (derived67495 p h)

theorem derived102895 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 3083) ∨ (¬ p 4608) ∨ (p 2651) :=
  ElevenRUP.step102895 (p 2651) (p 2657) (p 2946) (p 2952) (p 3083) (p 4256) (p 4608) (derived73329 p h) (derived73542 p h) (derived73288 p h) (derived67669 p h)

theorem derived102896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 2946) ∨ (¬ p 2440) :=
  ElevenRUP.step102896 (p 2440) (p 2850) (p 2946) (p 2952) (derived73330 p h) (derived67447 p h)

theorem derived102898 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2881) ∨ (¬ p 2437) ∨ (p 3201) ∨ (¬ p 4750) ∨ (¬ p 2850) :=
  ElevenRUP.step102898 (p 2437) (p 2717) (p 2850) (p 2881) (p 3201) (p 3659) (p 4750) (p 5081) (derived73438 p h) (derived73912 p h) (derived67951 p h)

theorem derived102899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2946) ∨ (p 2807) :=
  ElevenRUP.step102899 (p 2807) (p 2946) (p 2956) (p 3051) (p 3414) (derived73334 p h) (derived73392 p h) (derived67401 p h)

theorem derived102900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2331) ∨ (¬ p 2563) ∨ (¬ p 4702) :=
  ElevenRUP.step102900 (p 2331) (p 2563) (p 2946) (p 2963) (p 4702) (derived73338 p h) (derived67395 p h)

theorem derived102901 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 2210) ∨ (¬ p 2750) ∨ (p 2608) ∨ (¬ p 2946) :=
  ElevenRUP.step102901 (p 2210) (p 2241) (p 2251) (p 2608) (p 2750) (p 2946) (p 3555) (p 3954) (derived73230 p h) (derived73412 p h) (derived73498 p h) (derived67574 p h)

theorem derived102902 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2946) ∨ (p 2230) ∨ (p 2563) :=
  ElevenRUP.step102902 (p 2230) (p 2563) (p 2589) (p 2651) (p 2654) (p 2946) (p 4110) (derived73286 p h) (derived73284 p h) (derived73516 p h) (derived67425 p h)

theorem derived102904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2528) ∨ (p 3422) ∨ (¬ p 2230) ∨ (¬ p 3693) ∨ (¬ p 2850) ∨ (p 2440) ∨ (p 2373) ∨ (¬ p 4715) ∨ (¬ p 3362) :=
  ElevenRUP.step102904 (p 2230) (p 2373) (p 2440) (p 2528) (p 2850) (p 3156) (p 3362) (p 3422) (p 3584) (p 3693) (p 3880) (p 4703) (p 4715) (derived73426 p h) (derived73714 p h) (derived73490 p h) (derived68084 p h)

theorem derived102905 (p : Nat → Prop) (h : Inputs p) :
    (p 2246) ∨ (p 2641) ∨ (¬ p 2177) ∨ (¬ p 2608) ∨ (¬ p 2331) ∨ (¬ p 2737) ∨ (¬ p 2295) :=
  ElevenRUP.step102905 (p 2177) (p 2246) (p 2295) (p 2331) (p 2608) (p 2641) (p 2737) (p 2747) (p 4154) (derived73526 p h) (derived73302 p h) (derived67428 p h)

theorem derived102910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2363) ∨ (¬ p 2177) :=
  ElevenRUP.step102910 (p 2122) (p 2177) (p 2363) (p 2774) (p 4502) (derived73604 p h) (derived67990 p h)

theorem derived102911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4392) ∨ (¬ p 2132) ∨ (¬ p 2156) ∨ (p 2563) ∨ (¬ p 4749) ∨ (p 2598) :=
  ElevenRUP.step102911 (p 2132) (p 2156) (p 2563) (p 2598) (p 3055) (p 4110) (p 4392) (p 4749) (derived73516 p h) (derived73350 p h) (derived68213 p h)

theorem derived102919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2427) ∨ (p 2493) ∨ (¬ p 4715) :=
  ElevenRUP.step102919 (p 2427) (p 2493) (p 2499) (p 2891) (p 4235) (p 4715) (derived73536 p h) (derived73260 p h) (derived67749 p h)

theorem derived102922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (¬ p 2341) ∨ (¬ p 4525) ∨ (p 2881) ∨ (p 2166) :=
  ElevenRUP.step102922 (p 2166) (p 2191) (p 2341) (p 2881) (p 4525) (p 4900) (p 4988) (derived73818 p h) (derived73222 p h) (derived68273 p h)

theorem derived102925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (p 2210) ∨ (p 2156) ∨ (¬ p 3371) ∨ (¬ p 3369) ∨ (¬ p 2750) ∨ (¬ p 2241) :=
  ElevenRUP.step102925 (p 2156) (p 2210) (p 2241) (p 2563) (p 2750) (p 3369) (p 3371) (p 3555) (p 3646) (derived73412 p h) (derived73436 p h) (derived68033 p h)

theorem derived102928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3743) ∨ (¬ p 2363) ∨ (p 2284) ∨ (¬ p 2992) ∨ (¬ p 4558) ∨ (¬ p 2891) ∨ (p 2727) :=
  ElevenRUP.step102928 (p 2284) (p 2363) (p 2383) (p 2727) (p 2891) (p 2992) (p 3743) (p 4111) (p 4558) (p 4562) (p 4704) (p 4958) (derived73638 p h) (derived73852 p h) (derived73046 p h) (derived73518 p h) (derived67929 p h)

theorem derived102931 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 2210) ∨ (p 2922) ∨ (¬ p 3741) ∨ (¬ p 4811) ∨ (p 2440) :=
  ElevenRUP.step102931 (p 2210) (p 2440) (p 2542) (p 2922) (p 2925) (p 3399) (p 3555) (p 3741) (p 4811) (derived73412 p h) (derived73318 p h) (derived73270 p h) (derived67566 p h)

theorem derived102932 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2156) ∨ (¬ p 2563) ∨ (¬ p 2088) :=
  ElevenRUP.step102932 (p 2088) (p 2156) (p 2563) (p 3146) (p 3646) (p 3692) (derived73448 p h) (derived73436 p h) (derived67632 p h)

theorem derived102934 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2156) ∨ (¬ p 4509) ∨ (¬ p 2088) :=
  ElevenRUP.step102934 (p 2088) (p 2156) (p 3146) (p 3646) (p 3692) (p 4509) (derived73448 p h) (derived73436 p h) (derived67673 p h)

theorem derived102936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 3146) ∨ (p 2383) ∨ (¬ p 4356) ∨ (¬ p 2088) :=
  ElevenRUP.step102936 (p 2088) (p 2274) (p 2383) (p 3146) (p 3692) (p 3857) (p 4356) (p 4612) (derived73448 p h) (derived73668 p h) (derived73479 p h) (derived72336 p h)

theorem derived102939 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2274) ∨ (¬ p 4717) ∨ (p 2230) ∨ (¬ p 3389) ∨ (¬ p 4718) :=
  ElevenRUP.step102939 (p 2230) (p 2274) (p 2307) (p 2589) (p 3097) (p 3389) (p 4717) (p 4718) (derived73352 p h) (derived73284 p h) (derived67622 p h)

theorem derived102940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 4711) ∨ (¬ p 2352) ∨ (¬ p 2295) ∨ (p 2383) ∨ (p 2668) :=
  ElevenRUP.step102940 (p 2295) (p 2352) (p 2383) (p 2387) (p 2668) (p 3324) (p 3389) (p 4711) (derived73246 p h) (derived73386 p h) (derived67543 p h)

theorem derived102941 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2608) ∨ (¬ p 3399) ∨ (¬ p 3389) :=
  ElevenRUP.step102941 (p 2608) (p 2922) (p 2925) (p 3389) (p 3399) (p 3954) (p 4366) (derived73318 p h) (derived73498 p h) (derived73569 p h) (derived72337 p h)

theorem derived102942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 4383) ∨ (p 3641) ∨ (¬ p 3201) ∨ (¬ p 4277) ∨ (¬ p 2881) ∨ (¬ p 5203) :=
  ElevenRUP.step102942 (p 2481) (p 2881) (p 3201) (p 3641) (p 3874) (p 4277) (p 4383) (p 5203) (derived73484 p h) (derived68045 p h)

theorem derived102947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2307) ∨ (p 2651) ∨ (¬ p 2727) :=
  ElevenRUP.step102947 (p 2307) (p 2331) (p 2651) (p 2657) (p 2727) (p 4582) (derived73650 p h) (derived73288 p h) (derived67659 p h)

theorem derived102948 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3256) ∨ (p 2363) ∨ (¬ p 3449) :=
  ElevenRUP.step102948 (p 2363) (p 3189) (p 3256) (p 3449) (p 4347) (p 5077) (derived73910 p h) (derived73560 p h) (derived67819 p h)

theorem derived102951 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 2284) ∨ (¬ p 2156) ∨ (p 3125) :=
  ElevenRUP.step102951 (p 2156) (p 2284) (p 3125) (p 3654) (p 3744) (derived73454 p h) (derived67467 p h)

theorem derived102952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2156) ∨ (p 2563) :=
  ElevenRUP.step102952 (p 2156) (p 2440) (p 2563) (p 3646) (p 4714) (derived73435 p h) (derived73720 p h) (derived68210 p h)

theorem derived102954 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 2608) ∨ (p 2651) ∨ (¬ p 3361) :=
  ElevenRUP.step102954 (p 2608) (p 2651) (p 2657) (p 2727) (p 3361) (derived73288 p h) (derived67780 p h)

theorem derived102955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3286) ∨ (¬ p 3256) ∨ (p 2331) ∨ (p 2363) ∨ (¬ p 4774) :=
  ElevenRUP.step102955 (p 2331) (p 2363) (p 2963) (p 3256) (p 3286) (p 4347) (p 4774) (p 5110) (derived73924 p h) (derived73338 p h) (derived73560 p h) (derived67441 p h)

theorem derived102960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3872) ∨ (¬ p 4705) ∨ (¬ p 2274) ∨ (¬ p 2807) ∨ (p 2427) ∨ (p 2651) :=
  ElevenRUP.step102960 (p 2274) (p 2284) (p 2427) (p 2651) (p 2657) (p 2807) (p 3872) (p 4235) (p 4705) (derived73536 p h) (derived73288 p h) (derived67593 p h)

theorem derived102961 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2641) ∨ (p 2352) ∨ (¬ p 2807) ∨ (¬ p 2249) ∨ (¬ p 4976) ∨ (¬ p 2307) :=
  ElevenRUP.step102961 (p 2249) (p 2307) (p 2313) (p 2331) (p 2352) (p 2641) (p 2807) (p 3956) (p 4579) (p 4976) (derived73648 p h) (derived73500 p h) (derived73237 p h) (derived72343 p h)

theorem derived102964 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2662) ∨ (p 2563) ∨ (p 3051) ∨ (p 2230) ∨ (p 2881) :=
  ElevenRUP.step102964 (p 2230) (p 2563) (p 2630) (p 2662) (p 2810) (p 2881) (p 3051) (p 3556) (p 3570) (p 4110) (p 4535) (derived73316 p h) (derived73516 p h) (derived73414 p h) (derived73622 p h) (derived73418 p h) (derived67782 p h)

theorem derived102967 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 3367) ∨ (¬ p 4117) ∨ (¬ p 2598) ∨ (¬ p 4972) ∨ (p 2641) ∨ (¬ p 2440) ∨ (¬ p 4257) ∨ (¬ p 3362) ∨ (¬ p 2663) ∨ (¬ p 4281) :=
  ElevenRUP.step102967 (p 2230) (p 2440) (p 2598) (p 2641) (p 2663) (p 3362) (p 3367) (p 3585) (p 4117) (p 4154) (p 4257) (p 4281) (p 4972) (derived73428 p h) (derived73526 p h) (derived72344 p h)

theorem derived102969 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (p 2727) ∨ (¬ p 4975) ∨ (¬ p 2363) ∨ (¬ p 2641) :=
  ElevenRUP.step102969 (p 2363) (p 2641) (p 2727) (p 3063) (p 4111) (p 4758) (p 4975) (derived73518 p h) (derived73746 p h) (derived67936 p h)

theorem derived102974 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (p 3016) ∨ (¬ p 2187) ∨ (p 2440) ∨ (¬ p 4715) :=
  ElevenRUP.step102974 (p 2187) (p 2440) (p 2542) (p 2668) (p 3016) (p 3324) (p 4715) (p 4971) (derived73386 p h) (derived73858 p h) (derived73270 p h) (derived67835 p h)

theorem derived102976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 2274) ∨ (p 2177) ∨ (¬ p 4564) ∨ (¬ p 4138) ∨ (p 2668) :=
  ElevenRUP.step102976 (p 2177) (p 2274) (p 2299) (p 2668) (p 2881) (p 3324) (p 4138) (p 4557) (p 4564) (derived73636 p h) (derived73234 p h) (derived73386 p h) (derived67804 p h)

theorem derived102977 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2440) ∨ (¬ p 2352) ∨ (¬ p 4715) ∨ (p 2668) :=
  ElevenRUP.step102977 (p 2352) (p 2440) (p 2542) (p 2668) (p 3083) (p 3324) (p 4597) (p 4715) (derived73270 p h) (derived73658 p h) (derived73386 p h) (derived67740 p h)

theorem derived102979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3355) ∨ (¬ p 4438) ∨ (p 2573) ∨ (¬ p 2528) ∨ (p 2459) :=
  ElevenRUP.step102979 (p 2459) (p 2528) (p 2573) (p 2579) (p 3355) (p 4348) (p 4438) (p 4694) (derived73274 p h) (derived73710 p h) (derived73562 p h) (derived67762 p h)

theorem derived102985 (p : Nat → Prop) (h : Inputs p) :
    (p 2177) ∨ (¬ p 4559) ∨ (p 2156) ∨ (p 2459) ∨ (¬ p 2088) ∨ (¬ p 3743) :=
  ElevenRUP.step102985 (p 2088) (p 2156) (p 2177) (p 2459) (p 3646) (p 3743) (p 4500) (p 4559) (p 4665) (derived73602 p h) (derived73436 p h) (derived73696 p h) (derived67674 p h)

theorem derived102990 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2264) ∨ (p 2727) ∨ (p 3016) ∨ (¬ p 4711) ∨ (¬ p 2881) ∨ (¬ p 3872) :=
  ElevenRUP.step102990 (p 2264) (p 2727) (p 2881) (p 2911) (p 3016) (p 3574) (p 3644) (p 3872) (p 4111) (p 4711) (derived73434 p h) (derived73518 p h) (derived73422 p h) (derived68057 p h)

theorem derived102999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 3379) ∨ (¬ p 2509) ∨ (p 2563) ∨ (¬ p 4608) ∨ (¬ p 2210) :=
  ElevenRUP.step102999 (p 2210) (p 2241) (p 2509) (p 2563) (p 3379) (p 3452) (p 4110) (p 4608) (derived73394 p h) (derived73516 p h) (derived68043 p h)

theorem derived103009 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2241) ∨ (¬ p 4749) ∨ (p 3367) :=
  ElevenRUP.step103009 (p 2241) (p 2608) (p 3367) (p 3585) (p 3954) (p 4749) (derived73498 p h) (derived73428 p h) (derived67972 p h)

theorem derived103015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2668) ∨ (¬ p 4846) ∨ (p 2774) :=
  ElevenRUP.step103015 (p 2098) (p 2668) (p 2774) (p 3324) (p 4846) (derived73386 p h) (derived67849 p h)

theorem derived103018 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 2230) ∨ (¬ p 4715) ∨ (p 2440) ∨ (¬ p 2630) :=
  ElevenRUP.step103018 (p 2230) (p 2440) (p 2542) (p 2630) (p 2797) (p 2810) (p 4195) (p 4715) (derived73532 p h) (derived73270 p h) (derived73315 p h) (derived67833 p h)

theorem derived103019 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 2992) ∨ (¬ p 2493) ∨ (p 2797) ∨ (¬ p 4814) ∨ (¬ p 2630) :=
  ElevenRUP.step103019 (p 2493) (p 2630) (p 2797) (p 2992) (p 3136) (p 4195) (p 4315) (p 4814) (derived73550 p h) (derived73532 p h) (derived67544 p h)

theorem derived103020 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (p 2797) ∨ (¬ p 3367) ∨ (¬ p 2630) :=
  ElevenRUP.step103020 (p 2630) (p 2737) (p 2743) (p 2797) (p 2810) (p 3367) (p 4195) (derived73298 p h) (derived73532 p h) (derived73315 p h) (derived67830 p h)

theorem derived103023 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2630) ∨ (¬ p 2598) :=
  ElevenRUP.step103023 (p 2598) (p 2630) (p 2727) (p 4111) (p 4751) (derived73518 p h) (derived73742 p h) (derived72364 p h)

theorem derived103025 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 3367) ∨ (p 2850) ∨ (p 3136) :=
  ElevenRUP.step103025 (p 2737) (p 2743) (p 2850) (p 3136) (p 3367) (p 3684) (p 4315) (derived73298 p h) (derived73442 p h) (derived73550 p h) (derived67476 p h)

theorem derived103030 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2881) ∨ (¬ p 4559) ∨ (¬ p 2459) :=
  ElevenRUP.step103030 (p 2363) (p 2459) (p 2881) (p 4347) (p 4559) (derived73560 p h) (derived68020 p h)

theorem derived103032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 2274) ∨ (p 2352) ∨ (¬ p 3958) ∨ (p 2177) :=
  ElevenRUP.step103032 (p 2177) (p 2274) (p 2352) (p 2881) (p 3956) (p 3958) (p 4500) (p 4557) (derived73636 p h) (derived73500 p h) (derived73602 p h) (derived67995 p h)

theorem derived103037 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 3366) ∨ (p 2563) ∨ (¬ p 2440) ∨ (p 3367) ∨ (¬ p 2598) :=
  ElevenRUP.step103037 (p 2440) (p 2563) (p 2598) (p 2727) (p 3366) (p 3367) (p 3585) (p 4110) (p 4111) (p 4728) (derived73518 p h) (derived73516 p h) (derived73428 p h) (derived73730 p h) (derived72368 p h)

theorem derived103039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (p 2608) ∨ (p 2563) ∨ (¬ p 2440) ∨ (¬ p 4753) ∨ (p 3367) :=
  ElevenRUP.step103039 (p 2440) (p 2563) (p 2608) (p 2839) (p 3367) (p 3585) (p 3954) (p 4110) (p 4753) (derived73498 p h) (derived73516 p h) (derived73428 p h) (derived67826 p h)

theorem derived103040 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2230) :=
  ElevenRUP.step103040 (p 2230) (p 2589) (p 2659) (derived73284 p h) (derived67571 p h)

theorem derived103041 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 3355) ∨ (p 3146) ∨ (p 2230) ∨ (¬ p 4434) ∨ (¬ p 2528) :=
  ElevenRUP.step103041 (p 2230) (p 2363) (p 2528) (p 2589) (p 3146) (p 3355) (p 3692) (p 4347) (p 4434) (p 4694) (derived73560 p h) (derived73448 p h) (derived73284 p h) (derived73710 p h) (derived67609 p h)

theorem derived103042 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (¬ p 3363) ∨ (¬ p 4140) ∨ (p 2563) ∨ (p 2230) ∨ (p 2187) ∨ (p 2177) :=
  ElevenRUP.step103042 (p 2177) (p 2187) (p 2230) (p 2563) (p 2589) (p 3363) (p 3367) (p 3585) (p 3989) (p 4110) (p 4140) (p 4500) (derived73428 p h) (derived73516 p h) (derived73284 p h) (derived73502 p h) (derived73602 p h) (derived67797 p h)

theorem derived103043 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (p 2230) :=
  ElevenRUP.step103043 (p 2210) (p 2230) (p 2589) (p 3379) (p 5189) (derived73948 p h) (derived73284 p h) (derived68186 p h)

theorem derived103044 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2630) ∨ (¬ p 2696) :=
  ElevenRUP.step103044 (p 2630) (p 2696) (p 2727) (p 4111) (derived73518 p h) (derived72370 p h)

theorem derived103045 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2737) ∨ (¬ p 4972) ∨ (¬ p 2696) ∨ (¬ p 2630) :=
  ElevenRUP.step103045 (p 2630) (p 2696) (p 2737) (p 2774) (p 2780) (p 4972) (derived73308 p h) (derived68080 p h)

theorem derived103047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2319) ∨ (¬ p 3246) ∨ (¬ p 2274) ∨ (¬ p 3872) ∨ (¬ p 4138) ∨ (p 2187) ∨ (¬ p 4668) ∨ (¬ p 2318) ∨ (¬ p 3743) :=
  ElevenRUP.step103047 (p 2187) (p 2274) (p 2318) (p 2319) (p 3246) (p 3743) (p 3872) (p 3989) (p 4138) (p 4668) (derived73502 p h) (derived72372 p h)

theorem derived103049 (p : Nat → Prop) (h : Inputs p) :
    (p 3461) ∨ (¬ p 2761) ∨ (p 2177) ∨ (p 3266) ∨ (¬ p 3246) ∨ (¬ p 4559) :=
  ElevenRUP.step103049 (p 2177) (p 2299) (p 2761) (p 3246) (p 3266) (p 3461) (p 4191) (p 4444) (p 4559) (derived73530 p h) (derived73234 p h) (derived73580 p h) (derived67895 p h)

theorem derived103053 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2427) ∨ (¬ p 4558) ∨ (p 2563) ∨ (p 2396) :=
  ElevenRUP.step103053 (p 2396) (p 2417) (p 2427) (p 2563) (p 4107) (p 4110) (p 4558) (p 4645) (derived73686 p h) (derived73516 p h) (derived73514 p h) (derived67382 p h)

theorem derived103054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 3461) ∨ (¬ p 3192) ∨ (¬ p 4140) ∨ (¬ p 2417) ∨ (p 3246) ∨ (¬ p 4712) :=
  ElevenRUP.step103054 (p 2417) (p 3192) (p 3246) (p 3276) (p 3461) (p 3690) (p 4140) (p 4191) (p 4712) (derived73530 p h) (derived73446 p h) (derived67677 p h)

theorem derived103056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 2264) ∨ (p 2177) ∨ (¬ p 4361) ∨ (p 2363) :=
  ElevenRUP.step103056 (p 2177) (p 2264) (p 2363) (p 3256) (p 4347) (p 4361) (p 4500) (p 4551) (derived73632 p h) (derived73602 p h) (derived73560 p h) (derived67489 p h)

theorem derived103057 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2295) ∨ (¬ p 2696) ∨ (¬ p 2177) ∨ (¬ p 2331) :=
  ElevenRUP.step103057 (p 2177) (p 2295) (p 2331) (p 2696) (p 2774) (p 2780) (p 4788) (derived73308 p h) (derived73760 p h) (derived67429 p h)

theorem derived103059 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2839) ∨ (¬ p 2563) ∨ (p 2860) ∨ (¬ p 4428) :=
  ElevenRUP.step103059 (p 2563) (p 2829) (p 2839) (p 2860) (p 3688) (p 3758) (p 4428) (derived73444 p h) (derived73456 p h) (derived67777 p h)

theorem derived103066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 3389) ∨ (p 2553) :=
  ElevenRUP.step103066 (p 2307) (p 2553) (p 3389) (p 4707) (derived73716 p h) (derived67536 p h)

theorem derived103068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2132) ∨ (¬ p 2881) ∨ (p 2177) :=
  ElevenRUP.step103068 (p 2132) (p 2177) (p 2299) (p 2860) (p 2881) (p 3570) (derived73417 p h) (derived73234 p h) (derived67626 p h)

theorem derived103069 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2668) ∨ (p 2819) ∨ (¬ p 2630) ∨ (¬ p 4972) :=
  ElevenRUP.step103069 (p 2630) (p 2668) (p 2819) (p 3005) (p 4358) (p 4772) (p 4972) (derived73752 p h) (derived73564 p h) (derived68190 p h)

theorem derived103070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3166) ∨ (p 2383) ∨ (¬ p 2651) ∨ (¬ p 4972) :=
  ElevenRUP.step103070 (p 2383) (p 2387) (p 2651) (p 2668) (p 3166) (p 4772) (p 4972) (derived73752 p h) (derived73246 p h) (derived67501 p h)

theorem derived103071 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3589) ∨ (¬ p 4117) ∨ (p 2630) ∨ (¬ p 4842) ∨ (¬ p 2651) ∨ (¬ p 2727) :=
  ElevenRUP.step103071 (p 2630) (p 2651) (p 2727) (p 2810) (p 2829) (p 3589) (p 3688) (p 4117) (p 4842) (derived73444 p h) (derived73316 p h) (derived72375 p h)

theorem derived103074 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2427) ∨ (¬ p 4202) ∨ (p 2563) ∨ (¬ p 4119) ∨ (p 3379) :=
  ElevenRUP.step103074 (p 2427) (p 2563) (p 2891) (p 3379) (p 3452) (p 3486) (p 4110) (p 4119) (p 4202) (derived73398 p h) (derived73516 p h) (derived73394 p h) (derived67685 p h)

theorem derived103075 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 2528) ∨ (¬ p 4558) ∨ (¬ p 2427) ∨ (¬ p 3146) :=
  ElevenRUP.step103075 (p 2190) (p 2427) (p 2528) (p 2534) (p 3146) (p 4558) (p 5057) (derived73268 p h) (derived73898 p h) (derived68249 p h)

theorem derived103078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2608) ∨ (¬ p 2166) ∨ (¬ p 2210) :=
  ElevenRUP.step103078 (p 2166) (p 2210) (p 2608) (p 3073) (p 3954) (derived73498 p h) (derived67554 p h)

theorem derived103079 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3146) ∨ (¬ p 4632) ∨ (¬ p 4539) ∨ (¬ p 2088) ∨ (¬ p 4607) ∨ (¬ p 2166) :=
  ElevenRUP.step103079 (p 2088) (p 2166) (p 2528) (p 2534) (p 3146) (p 4539) (p 4607) (p 4632) (derived73268 p h) (derived68245 p h)

theorem derived103080 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2210) ∨ (¬ p 4877) ∨ (¬ p 2156) ∨ (p 2563) :=
  ElevenRUP.step103080 (p 2156) (p 2210) (p 2563) (p 2608) (p 3954) (p 4110) (p 4523) (p 4877) (derived73498 p h) (derived73616 p h) (derived73516 p h) (derived68207 p h)

theorem derived103081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 2274) ∨ (¬ p 2363) ∨ (¬ p 2210) ∨ (¬ p 2192) :=
  ElevenRUP.step103081 (p 2192) (p 2210) (p 2274) (p 2363) (p 3063) (p 4515) (derived73612 p h) (derived67404 p h)

theorem derived103082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 3389) ∨ (p 2727) ∨ (¬ p 2662) ∨ (p 2437) ∨ (¬ p 2608) ∨ (¬ p 2911) :=
  ElevenRUP.step103082 (p 2437) (p 2608) (p 2662) (p 2727) (p 2911) (p 3201) (p 3389) (p 3540) (p 3742) (p 3876) (p 4111) (derived73485 p h) (derived73402 p h) (derived73518 p h) (derived73452 p h) (derived67427 p h)

theorem derived103084 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (¬ p 3146) ∨ (¬ p 4705) ∨ (¬ p 2284) ∨ (p 2528) :=
  ElevenRUP.step103084 (p 2190) (p 2284) (p 2528) (p 2534) (p 3146) (p 4705) (p 5057) (derived73898 p h) (derived73268 p h) (derived68232 p h)

theorem derived103085 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (p 2274) ∨ (p 2177) :=
  ElevenRUP.step103085 (p 2177) (p 2264) (p 2274) (p 2299) (p 3097) (p 3553) (p 4560) (derived73409 p h) (derived73352 p h) (derived73234 p h) (derived72955 p h) (derived67600 p h)

theorem derived103086 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 3389) ∨ (¬ p 3425) :=
  ElevenRUP.step103086 (p 3201) (p 3389) (p 3425) (p 5081) (derived73912 p h) (derived67371 p h)

theorem derived103087 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (p 2241) ∨ (¬ p 4972) ∨ (¬ p 3379) ∨ (¬ p 2727) :=
  ElevenRUP.step103087 (p 2241) (p 2244) (p 2331) (p 2727) (p 2963) (p 3379) (p 4812) (p 4972) (derived73338 p h) (derived73224 p h) (derived73772 p h) (derived67682 p h)

theorem derived103089 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2727) ∨ (p 2156) ∨ (p 2651) ∨ (p 2563) :=
  ElevenRUP.step103089 (p 2156) (p 2284) (p 2563) (p 2651) (p 2657) (p 2727) (p 3646) (p 4110) (p 4565) (derived73640 p h) (derived73436 p h) (derived73288 p h) (derived73516 p h) (derived67665 p h)

theorem derived103091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2156) ∨ (p 2352) ∨ (¬ p 3958) :=
  ElevenRUP.step103091 (p 2156) (p 2220) (p 2352) (p 3646) (p 3956) (p 3958) (p 4120) (derived73521 p h) (derived73436 p h) (derived73500 p h) (derived68110 p h)

theorem derived103093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 5022) ∨ (¬ p 2177) ∨ (¬ p 3093) ∨ (¬ p 2459) ∨ (p 3527) :=
  ElevenRUP.step103093 (p 2177) (p 2307) (p 2459) (p 3093) (p 3527) (p 3548) (p 5022) (derived73404 p h) (derived67394 p h)

theorem derived103100 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2088) ∨ (¬ p 2737) ∨ (¬ p 2274) ∨ (¬ p 2363) :=
  ElevenRUP.step103100 (p 2088) (p 2274) (p 2363) (p 2608) (p 2737) (p 2747) (p 4557) (p 4602) (p 4732) (derived73732 p h) (derived73302 p h) (derived73636 p h) (derived73662 p h) (derived68870 p h)

theorem derived103101 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2088) ∨ (p 2563) ∨ (¬ p 2363) ∨ (¬ p 2737) :=
  ElevenRUP.step103101 (p 2088) (p 2363) (p 2563) (p 2608) (p 2737) (p 2747) (p 4602) (p 4714) (p 4732) (derived73732 p h) (derived73720 p h) (derived73662 p h) (derived73302 p h) (derived69075 p h)

theorem derived103102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2850) ∨ (¬ p 2274) ∨ (p 2696) ∨ (¬ p 3367) ∨ (¬ p 2563) :=
  ElevenRUP.step103102 (p 2274) (p 2563) (p 2696) (p 2737) (p 2850) (p 3365) (p 3367) (p 4734) (p 4883) (derived73808 p h) (derived73390 p h) (derived72735 p h) (derived68819 p h)

theorem derived103103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3367) ∨ (¬ p 2363) ∨ (p 3379) ∨ (p 2608) ∨ (¬ p 2088) ∨ (¬ p 2696) ∨ (¬ p 2737) :=
  ElevenRUP.step103103 (p 2088) (p 2363) (p 2608) (p 2696) (p 2737) (p 2747) (p 3323) (p 3367) (p 3379) (p 4602) (p 4732) (p 4788) (p 5189) (derived73662 p h) (derived73948 p h) (derived73732 p h) (derived73760 p h) (derived73302 p h) (derived69459 p h)

theorem derived103108 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2363) ∨ (¬ p 3367) ∨ (¬ p 2088) ∨ (¬ p 2696) ∨ (¬ p 2459) ∨ (¬ p 2737) :=
  ElevenRUP.step103108 (p 2088) (p 2363) (p 2459) (p 2608) (p 2696) (p 2737) (p 2747) (p 3367) (p 4602) (p 4667) (p 4732) (p 4788) (p 5215) (derived73732 p h) (derived73662 p h) (derived73962 p h) (derived73760 p h) (derived73698 p h) (derived73302 p h) (derived69424 p h)

theorem derived103109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2274) ∨ (¬ p 2493) ∨ (¬ p 2696) ∨ (¬ p 2630) ∨ (¬ p 2578) ∨ (p 3016) ∨ (¬ p 2577) ∨ (¬ p 5191) ∨ (¬ p 4814) :=
  ElevenRUP.step103109 (p 2274) (p 2493) (p 2553) (p 2577) (p 2578) (p 2630) (p 2696) (p 3016) (p 3097) (p 4814) (p 4971) (p 5191) (derived73352 p h) (derived73858 p h) (derived69286 p h)

theorem derived103110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2972) ∨ (¬ p 2839) ∨ (p 3367) ∨ (p 2982) ∨ (¬ p 4884) :=
  ElevenRUP.step103110 (p 2839) (p 2972) (p 2982) (p 3367) (p 3585) (p 4876) (p 4884) (p 4948) (derived73804 p h) (derived73428 p h) (derived73846 p h) (derived68851 p h)

theorem derived103121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2274) ∨ (p 2563) ∨ (p 2630) ∨ (¬ p 4790) :=
  ElevenRUP.step103121 (p 2274) (p 2440) (p 2563) (p 2630) (p 2810) (p 3097) (p 4110) (p 4790) (derived73352 p h) (derived73516 p h) (derived73316 p h) (derived69022 p h)

theorem derived103122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 4814) ∨ (p 2563) ∨ (¬ p 2440) :=
  ElevenRUP.step103122 (p 2192) (p 2440) (p 2563) (p 4110) (p 4173) (p 4814) (derived73527 p h) (derived73516 p h) (derived69039 p h)

theorem derived103123 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 4204) ∨ (¬ p 2440) ∨ (¬ p 2177) ∨ (p 2563) ∨ (p 3051) :=
  ElevenRUP.step103123 (p 2177) (p 2440) (p 2563) (p 2881) (p 3051) (p 3556) (p 3570) (p 4110) (p 4204) (derived73418 p h) (derived73516 p h) (derived73414 p h) (derived69026 p h)

theorem derived103124 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 2630) ∨ (¬ p 4790) ∨ (¬ p 2440) :=
  ElevenRUP.step103124 (p 2230) (p 2440) (p 2630) (p 2810) (p 4790) (derived73316 p h) (derived68522 p h)

theorem derived103128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 5197) ∨ (p 3389) ∨ (¬ p 3575) ∨ (¬ p 2459) ∨ (¬ p 2437) ∨ (¬ p 2264) ∨ (¬ p 2659) :=
  ElevenRUP.step103128 (p 2264) (p 2437) (p 2440) (p 2459) (p 2659) (p 3389) (p 3540) (p 3575) (p 4651) (p 5197) (derived73402 p h) (derived73690 p h) (derived69408 p h)

theorem derived103131 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3581) ∨ (¬ p 2437) :=
  ElevenRUP.step103131 (p 2437) (p 3016) (p 3574) (p 3581) (p 4651) (derived73422 p h) (derived73690 p h) (derived69008 p h)

theorem derived103137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3319) ∨ (p 3564) ∨ (¬ p 5224) ∨ (p 3367) ∨ (p 2839) :=
  ElevenRUP.step103137 (p 2829) (p 2839) (p 3319) (p 3367) (p 3564) (p 3583) (p 3585) (p 4137) (p 4868) (p 5224) (derived73800 p h) (derived73524 p h) (derived73428 p h) (derived73424 p h) (derived69441 p h)

theorem derived103141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 4749) ∨ (¬ p 2696) ∨ (p 2230) :=
  ElevenRUP.step103141 (p 2230) (p 2589) (p 2696) (p 2850) (p 4749) (derived73284 p h) (derived69262 p h)

theorem derived103145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2274) ∨ (¬ p 4338) ∨ (p 2373) ∨ (¬ p 3660) ∨ (¬ p 2504) :=
  ElevenRUP.step103145 (p 2274) (p 2373) (p 2504) (p 2553) (p 3097) (p 3660) (p 3880) (p 4338) (derived73352 p h) (derived73490 p h) (derived69434 p h)

theorem derived103147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 2230) ∨ (¬ p 4558) ∨ (p 2573) ∨ (p 2563) :=
  ElevenRUP.step103147 (p 2230) (p 2563) (p 2573) (p 2579) (p 3051) (p 4537) (p 4558) (p 4714) (derived73624 p h) (derived73274 p h) (derived73720 p h) (derived68728 p h)

theorem derived103149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (p 3125) ∨ (¬ p 5201) ∨ (¬ p 3581) ∨ (¬ p 2311) ∨ (¬ p 2177) ∨ (p 2911) ∨ (¬ p 4624) ∨ (¬ p 2386) :=
  ElevenRUP.step103149 (p 2177) (p 2311) (p 2386) (p 2911) (p 3125) (p 3564) (p 3581) (p 3644) (p 3744) (p 4624) (p 5201) (derived73454 p h) (derived73434 p h) (derived69440 p h)

theorem derived103156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 4067) ∨ (¬ p 2177) ∨ (p 2295) ∨ (¬ p 4973) ∨ (¬ p 2696) ∨ (¬ p 2459) ∨ (¬ p 2630) :=
  ElevenRUP.step103156 (p 2177) (p 2295) (p 2459) (p 2553) (p 2630) (p 2696) (p 3568) (p 4067) (p 4973) (derived73416 p h) (derived69383 p h)

theorem derived103157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 2901) ∨ (p 2870) ∨ (¬ p 4906) ∨ (¬ p 2696) :=
  ElevenRUP.step103157 (p 2696) (p 2870) (p 2901) (p 3425) (p 4893) (p 4906) (derived73814 p h) (derived69425 p h)

theorem derived103159 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 3246) ∨ (¬ p 2417) ∨ (¬ p 4882) ∨ (¬ p 4283) ∨ (¬ p 4988) ∨ (¬ p 3741) :=
  ElevenRUP.step103159 (p 2417) (p 2870) (p 3246) (p 3690) (p 3741) (p 4244) (p 4283) (p 4882) (p 4988) (derived73540 p h) (derived73446 p h) (derived72406 p h)

theorem derived103160 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2437) ∨ (¬ p 2440) ∨ (¬ p 4882) :=
  ElevenRUP.step103160 (p 2437) (p 2440) (p 2870) (p 4244) (p 4882) (derived73540 p h) (derived69404 p h)

theorem derived103162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2396) ∨ (p 2187) ∨ (¬ p 3872) ∨ (¬ p 4356) :=
  ElevenRUP.step103162 (p 2187) (p 2396) (p 3246) (p 3872) (p 3989) (p 4107) (p 4356) (derived73514 p h) (derived73502 p h) (derived72408 p h)

theorem derived103163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2319) ∨ (¬ p 2911) ∨ (¬ p 2563) ∨ (¬ p 2427) ∨ (¬ p 3741) ∨ (¬ p 3246) ∨ (¬ p 2396) ∨ (p 2156) ∨ (p 2177) ∨ (¬ p 4533) :=
  ElevenRUP.step103163 (p 2156) (p 2177) (p 2299) (p 2319) (p 2396) (p 2427) (p 2563) (p 2911) (p 3246) (p 3741) (p 4484) (p 4533) (derived73594 p h) (derived73234 p h) (derived68643 p h)

theorem derived103166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 4814) ∨ (¬ p 3005) ∨ (¬ p 2696) ∨ (¬ p 2441) ∨ (¬ p 4031) ∨ (¬ p 4733) ∨ (p 3051) ∨ (¬ p 2665) ∨ (¬ p 2440) ∨ (p 3379) ∨ (¬ p 3389) ∨ (p 2881) ∨ (¬ p 4668) ∨ (¬ p 2685) ∨ (¬ p 2230) ∨ (¬ p 4669) :=
  ElevenRUP.step103166 (p 2230) (p 2440) (p 2441) (p 2589) (p 2665) (p 2685) (p 2696) (p 2881) (p 3005) (p 3051) (p 3256) (p 3379) (p 3389) (p 3556) (p 3570) (p 4031) (p 4668) (p 4669) (p 4733) (p 4814) (p 5189) (derived73414 p h) (derived73948 p h) (derived73418 p h) (derived73283 p h) (derived68503 p h)

theorem derived103170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 2437) ∨ (¬ p 4281) ∨ (¬ p 2249) ∨ (¬ p 4790) ∨ (¬ p 2751) ∨ (p 2630) :=
  ElevenRUP.step103170 (p 2249) (p 2437) (p 2630) (p 2751) (p 2810) (p 2922) (p 3742) (p 4281) (p 4790) (derived73452 p h) (derived73316 p h) (derived68962 p h)

theorem derived103178 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2245) ∨ (¬ p 3487) ∨ (¬ p 2737) ∨ (¬ p 4281) ∨ (p 2563) ∨ (p 2608) ∨ (p 2241) ∨ (¬ p 2274) ∨ (¬ p 2249) ∨ (¬ p 3367) ∨ (¬ p 4814) ∨ (p 2177) ∨ (¬ p 2363) ∨ (¬ p 2727) :=
  ElevenRUP.step103178 (p 2098) (p 2177) (p 2241) (p 2245) (p 2247) (p 2249) (p 2274) (p 2363) (p 2563) (p 2608) (p 2727) (p 2737) (p 2747) (p 3367) (p 3487) (p 4281) (p 4500) (p 4557) (p 4602) (p 4714) (p 4732) (p 4814) (p 5215) (derived73302 p h) (derived73720 p h) (derived73732 p h) (derived73226 p h) (derived73636 p h) (derived73962 p h) (derived73602 p h) (derived73662 p h) (derived68799 p h)

theorem derived103179 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2210) ∨ (¬ p 4814) ∨ (¬ p 2440) :=
  ElevenRUP.step103179 (p 2210) (p 2440) (p 3379) (p 3452) (p 4814) (derived73394 p h) (derived69095 p h)

theorem derived103181 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2331) ∨ (¬ p 4564) ∨ (¬ p 4769) ∨ (¬ p 4584) ∨ (¬ p 2187) ∨ (¬ p 2797) :=
  ElevenRUP.step103181 (p 2187) (p 2331) (p 2797) (p 3005) (p 3877) (p 4564) (p 4584) (p 4769) (derived73488 p h) (derived68508 p h)

theorem derived103190 (p : Nat → Prop) (h : Inputs p) :
    (p 2619) ∨ (p 2440) ∨ (¬ p 4750) ∨ (¬ p 4109) ∨ (¬ p 3413) ∨ (¬ p 3156) ∨ (p 2230) ∨ (¬ p 2220) ∨ (¬ p 2659) :=
  ElevenRUP.step103190 (p 2220) (p 2230) (p 2440) (p 2542) (p 2589) (p 2619) (p 2659) (p 3156) (p 3413) (p 3694) (p 4109) (p 4750) (derived73450 p h) (derived73270 p h) (derived73284 p h) (derived69232 p h)

theorem derived103196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 2122) ∨ (¬ p 2563) :=
  ElevenRUP.step103196 (p 2122) (p 2274) (p 2563) (p 3822) (derived73472 p h) (derived68702 p h)

theorem derived103197 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2850) ∨ (¬ p 5217) ∨ (p 3379) ∨ (p 2881) ∨ (p 2427) :=
  ElevenRUP.step103197 (p 2132) (p 2138) (p 2427) (p 2850) (p 2881) (p 3379) (p 3452) (p 3570) (p 4235) (p 4880) (p 5217) (derived73214 p h) (derived73806 p h) (derived73394 p h) (derived73418 p h) (derived73536 p h) (derived68785 p h)

theorem derived103199 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2440) ∨ (¬ p 4750) ∨ (¬ p 2696) ∨ (p 2850) :=
  ElevenRUP.step103199 (p 2132) (p 2138) (p 2440) (p 2542) (p 2696) (p 2850) (p 3684) (p 4750) (derived73214 p h) (derived73270 p h) (derived73442 p h) (derived68805 p h)

theorem derived103200 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 2246) ∨ (¬ p 2946) :=
  ElevenRUP.step103200 (p 2246) (p 2946) (p 2956) (p 2992) (p 3662) (derived73440 p h) (derived73334 p h) (derived69287 p h)

theorem derived103201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2901) ∨ (¬ p 2246) ∨ (p 2685) ∨ (¬ p 2751) ∨ (¬ p 2946) :=
  ElevenRUP.step103201 (p 2246) (p 2685) (p 2751) (p 2901) (p 2946) (p 2956) (p 3051) (p 3572) (p 4916) (derived73826 p h) (derived73420 p h) (derived73334 p h) (derived69418 p h)

theorem derived103206 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2901) ∨ (¬ p 4705) ∨ (¬ p 3096) ∨ (¬ p 2850) ∨ (p 3422) :=
  ElevenRUP.step103206 (p 2850) (p 2901) (p 3096) (p 3201) (p 3422) (p 3584) (p 4705) (derived73426 p h) (derived68379 p h)

theorem derived103207 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2246) ∨ (¬ p 2331) :=
  ElevenRUP.step103207 (p 2246) (p 2331) (p 2641) (p 4755) (derived73744 p h) (derived68481 p h)

theorem derived103220 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2363) ∨ (¬ p 2737) ∨ (¬ p 2696) ∨ (¬ p 2088) ∨ (¬ p 2459) :=
  ElevenRUP.step103220 (p 2088) (p 2363) (p 2459) (p 2608) (p 2696) (p 2737) (p 2747) (p 4602) (p 4667) (p 4732) (p 4788) (derived73732 p h) (derived73662 p h) (derived73302 p h) (derived73760 p h) (derived73698 p h) (derived69451 p h)

theorem derived103224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2132) ∨ (¬ p 2363) ∨ (¬ p 2187) :=
  ElevenRUP.step103224 (p 2132) (p 2138) (p 2187) (p 2363) (p 2774) (derived73214 p h) (derived68726 p h)

theorem derived103226 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2122) ∨ (¬ p 2829) ∨ (¬ p 2774) :=
  ElevenRUP.step103226 (p 2098) (p 2104) (p 2122) (p 2774) (p 2829) (derived73204 p h) (derived72437 p h)

theorem derived103227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 4841) ∨ (¬ p 4389) ∨ (p 2122) ∨ (¬ p 2786) ∨ (¬ p 2274) ∨ (¬ p 2785) ∨ (¬ p 2630) ∨ (¬ p 2363) ∨ (¬ p 4972) :=
  ElevenRUP.step103227 (p 2122) (p 2274) (p 2363) (p 2630) (p 2668) (p 2785) (p 2786) (p 3822) (p 4389) (p 4841) (p 4972) (derived73472 p h) (derived68514 p h)

theorem derived103229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2751) ∨ (p 3136) ∨ (¬ p 4392) ∨ (¬ p 2220) ∨ (¬ p 2166) ∨ (¬ p 2630) ∨ (¬ p 2246) ∨ (p 2619) :=
  ElevenRUP.step103229 (p 2166) (p 2220) (p 2246) (p 2619) (p 2630) (p 2751) (p 3136) (p 3694) (p 4315) (p 4392) (derived73550 p h) (derived73450 p h) (derived69734 p h)

theorem derived103236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3370) ∨ (¬ p 2341) ∨ (¬ p 2590) ∨ (p 2911) ∨ (¬ p 3581) ∨ (p 2427) ∨ (¬ p 4632) ∨ (¬ p 4705) :=
  ElevenRUP.step103236 (p 2341) (p 2427) (p 2590) (p 2901) (p 2911) (p 3370) (p 3581) (p 3644) (p 4235) (p 4632) (p 4705) (derived73434 p h) (derived73536 p h) (derived68990 p h)

theorem derived103241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 2210) ∨ (p 2274) ∨ (p 2177) ∨ (p 2166) :=
  ElevenRUP.step103241 (p 2166) (p 2177) (p 2191) (p 2210) (p 2274) (p 3097) (p 3399) (p 3555) (p 4500) (derived73412 p h) (derived73352 p h) (derived73602 p h) (derived73222 p h) (derived69130 p h)

theorem derived103242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2166) ∨ (¬ p 4556) ∨ (¬ p 2177) ∨ (p 2881) :=
  ElevenRUP.step103242 (p 2166) (p 2177) (p 2191) (p 2192) (p 2881) (p 4556) (p 4900) (derived73222 p h) (derived73818 p h) (derived69078 p h)

theorem derived103243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2166) ∨ (p 2274) ∨ (¬ p 2210) ∨ (p 2608) ∨ (¬ p 3073) ∨ (¬ p 2177) :=
  ElevenRUP.step103243 (p 2166) (p 2177) (p 2191) (p 2192) (p 2210) (p 2274) (p 2608) (p 3073) (p 3954) (p 4554) (derived73222 p h) (derived73634 p h) (derived73498 p h) (derived69108 p h)

theorem derived103244 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 2563) ∨ (p 2406) ∨ (¬ p 2493) :=
  ElevenRUP.step103244 (p 2166) (p 2191) (p 2406) (p 2493) (p 2563) (p 4627) (p 4716) (derived73222 p h) (derived73722 p h) (derived73676 p h) (derived69557 p h)

theorem derived103247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (¬ p 3412) ∨ (¬ p 3051) ∨ (¬ p 2630) ∨ (p 2870) :=
  ElevenRUP.step103247 (p 2630) (p 2870) (p 3051) (p 3370) (p 3412) (p 4244) (derived73540 p h) (derived69736 p h)

theorem derived103249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 3323) ∨ (¬ p 2298) ∨ (¬ p 2264) ∨ (p 2274) ∨ (¬ p 4624) ∨ (¬ p 2881) ∨ (¬ p 4336) ∨ (¬ p 2459) ∨ (¬ p 2284) :=
  ElevenRUP.step103249 (p 2264) (p 2274) (p 2284) (p 2298) (p 2459) (p 2641) (p 2881) (p 3323) (p 4336) (p 4554) (p 4624) (derived73634 p h) (derived69389 p h)

theorem derived103250 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3146) ∨ (¬ p 2563) :=
  ElevenRUP.step103250 (p 2528) (p 2534) (p 2563) (p 3146) (p 5057) (derived73268 p h) (derived73898 p h) (derived69461 p h)

theorem derived103253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2274) ∨ (p 2187) ∨ (p 2177) :=
  ElevenRUP.step103253 (p 2177) (p 2187) (p 2264) (p 2274) (p 3553) (p 3989) (p 4500) (derived73409 p h) (derived73502 p h) (derived73602 p h) (derived68692 p h)

theorem derived103255 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2132) ∨ (p 3201) ∨ (¬ p 2850) ∨ (¬ p 2753) ∨ (¬ p 4715) ∨ (¬ p 4644) :=
  ElevenRUP.step103255 (p 2132) (p 2753) (p 2774) (p 2780) (p 2850) (p 3201) (p 3876) (p 4644) (p 4715) (p 4883) (derived73308 p h) (derived73486 p h) (derived73808 p h) (derived68722 p h)

theorem derived103258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2619) ∨ (¬ p 2751) ∨ (¬ p 2166) ∨ (p 3136) ∨ (¬ p 4392) :=
  ElevenRUP.step103258 (p 2166) (p 2619) (p 2751) (p 2992) (p 3136) (p 3694) (p 4315) (p 4392) (p 4958) (derived73852 p h) (derived73450 p h) (derived73550 p h) (derived69198 p h)

theorem derived103259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (p 2630) ∨ (¬ p 2751) ∨ (¬ p 4790) ∨ (p 2440) ∨ (¬ p 2230) ∨ (p 2850) :=
  ElevenRUP.step103259 (p 2230) (p 2440) (p 2630) (p 2751) (p 2850) (p 2992) (p 3684) (p 4703) (p 4748) (p 4790) (derived73740 p h) (derived73714 p h) (derived73442 p h) (derived68369 p h)

theorem derived103260 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2992) ∨ (p 2922) ∨ (¬ p 4644) ∨ (p 2440) :=
  ElevenRUP.step103260 (p 2440) (p 2727) (p 2922) (p 2928) (p 2992) (p 4644) (p 4703) (p 4809) (derived73770 p h) (derived73320 p h) (derived73714 p h) (derived68948 p h)

theorem derived103263 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (¬ p 2727) ∨ (p 2553) ∨ (p 2630) ∨ (¬ p 2245) ∨ (¬ p 4790) ∨ (¬ p 4976) ∨ (p 2295) :=
  ElevenRUP.step103263 (p 2245) (p 2295) (p 2553) (p 2588) (p 2630) (p 2641) (p 2727) (p 2810) (p 3568) (p 4154) (p 4790) (p 4976) (derived73526 p h) (derived73282 p h) (derived73316 p h) (derived73416 p h) (derived69371 p h)

theorem derived103264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2951) ∨ (¬ p 3051) ∨ (p 3156) ∨ (¬ p 4668) :=
  ElevenRUP.step103264 (p 2951) (p 3051) (p 3156) (p 3246) (p 3497) (p 4668) (derived73400 p h) (derived69310 p h)

theorem derived103265 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 2088) ∨ (p 2651) ∨ (¬ p 5011) :=
  ElevenRUP.step103265 (p 2088) (p 2651) (p 2657) (p 3256) (p 5011) (p 5106) (derived73922 p h) (derived73288 p h) (derived68884 p h)

theorem derived103267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2331) ∨ (p 2187) ∨ (p 2156) :=
  ElevenRUP.step103267 (p 2156) (p 2187) (p 2331) (p 2668) (p 3646) (derived73436 p h) (derived68542 p h)

theorem derived103271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2727) ∨ (p 2192) :=
  ElevenRUP.step103271 (p 2192) (p 2284) (p 2727) (p 4511) (derived73610 p h) (derived69741 p h)

theorem derived103273 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (p 2274) ∨ (¬ p 2295) ∨ (¬ p 2249) ∨ (p 2996) ∨ (p 2807) :=
  ElevenRUP.step103273 (p 2249) (p 2274) (p 2295) (p 2307) (p 2313) (p 2807) (p 2996) (p 3027) (p 3097) (p 4560) (p 4571) (derived73238 p h) (derived73352 p h) (derived73644 p h) (derived73340 p h) (derived72955 p h) (derived69138 p h)

theorem derived103276 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2406) ∨ (¬ p 2210) ∨ (¬ p 5217) ∨ (p 2850) :=
  ElevenRUP.step103276 (p 2210) (p 2406) (p 2608) (p 2850) (p 3684) (p 3954) (p 4630) (p 5217) (derived73498 p h) (derived73678 p h) (derived73442 p h) (derived68905 p h)

theorem derived103290 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 3399) ∨ (p 2274) ∨ (¬ p 4518) :=
  ElevenRUP.step103290 (p 2274) (p 3093) (p 3097) (p 3399) (p 4518) (derived73352 p h) (derived69131 p h)

theorem derived103292 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (p 2241) ∨ (p 3309) ∨ (p 3146) ∨ (¬ p 2363) ∨ (p 2274) ∨ (p 2177) :=
  ElevenRUP.step103292 (p 2177) (p 2241) (p 2247) (p 2274) (p 2363) (p 2641) (p 3097) (p 3146) (p 3309) (p 3549) (p 3692) (p 4500) (p 4755) (derived73744 p h) (derived73226 p h) (derived73406 p h) (derived73448 p h) (derived73352 p h) (derived73602 p h) (derived69259 p h)

theorem derived103294 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (p 3379) ∨ (p 2177) ∨ (p 3309) ∨ (p 2406) ∨ (¬ p 2563) :=
  ElevenRUP.step103294 (p 2177) (p 2299) (p 2373) (p 2406) (p 2563) (p 3238) (p 3309) (p 3379) (p 3452) (p 3549) (p 3880) (p 4716) (derived73490 p h) (derived73394 p h) (derived73234 p h) (derived73406 p h) (derived73374 p h) (derived73722 p h) (derived69583 p h)

theorem derived103296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (p 3146) ∨ (¬ p 3988) ∨ (¬ p 4433) ∨ (¬ p 2363) :=
  ElevenRUP.step103296 (p 2363) (p 3146) (p 3323) (p 3692) (p 3988) (p 4433) (p 4560) (p 4602) (derived73448 p h) (derived72955 p h) (derived73662 p h) (derived69433 p h)

theorem derived103301 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3266) ∨ (¬ p 2563) ∨ (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 4433) ∨ (¬ p 2363) :=
  ElevenRUP.step103301 (p 2363) (p 2563) (p 2598) (p 2850) (p 3146) (p 3266) (p 4433) (p 5055) (derived73896 p h) (derived69126 p h)

theorem derived103308 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (¬ p 2132) ∨ (p 3083) ∨ (¬ p 3367) ∨ (¬ p 2590) ∨ (¬ p 4608) ∨ (¬ p 2737) ∨ (¬ p 2493) ∨ (p 2774) ∨ (¬ p 5217) ∨ (¬ p 2440) :=
  ElevenRUP.step103308 (p 2132) (p 2440) (p 2493) (p 2590) (p 2696) (p 2737) (p 2774) (p 2780) (p 3083) (p 3365) (p 3367) (p 4256) (p 4608) (p 5217) (derived73390 p h) (derived73542 p h) (derived73308 p h) (derived68798 p h)

theorem derived103315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2132) ∨ (p 2220) :=
  ElevenRUP.step103315 (p 2098) (p 2132) (p 2135) (p 2220) (p 4120) (derived73212 p h) (derived73522 p h) (derived68650 p h)

theorem derived103316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2696) ∨ (¬ p 3256) ∨ (¬ p 2737) :=
  ElevenRUP.step103316 (p 2098) (p 2696) (p 2737) (p 3256) (p 3365) (derived73390 p h) (derived68552 p h)

theorem derived103320 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 2641) ∨ (¬ p 2192) ∨ (p 2563) ∨ (p 2440) :=
  ElevenRUP.step103320 (p 2192) (p 2440) (p 2563) (p 2641) (p 2727) (p 4110) (p 4111) (p 4173) (p 4703) (derived73518 p h) (derived73527 p h) (derived73516 p h) (derived73714 p h) (derived68889 p h)

theorem derived103321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 3367) ∨ (p 2727) ∨ (¬ p 2737) :=
  ElevenRUP.step103321 (p 2641) (p 2727) (p 2737) (p 2747) (p 3367) (p 3585) (p 4111) (derived73428 p h) (derived73518 p h) (derived73302 p h) (derived69449 p h)

theorem derived103325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2641) ∨ (¬ p 4717) ∨ (¬ p 3016) ∨ (p 2230) ∨ (p 2406) ∨ (p 2727) :=
  ElevenRUP.step103325 (p 2230) (p 2246) (p 2406) (p 2589) (p 2641) (p 2727) (p 3016) (p 3238) (p 4717) (p 4809) (p 4974) (derived73860 p h) (derived73284 p h) (derived73374 p h) (derived73770 p h) (derived69212 p h)

theorem derived103326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2641) ∨ (p 2406) ∨ (p 2727) ∨ (¬ p 4717) ∨ (p 2553) ∨ (p 2241) ∨ (p 2230) :=
  ElevenRUP.step103326 (p 2230) (p 2241) (p 2246) (p 2247) (p 2406) (p 2553) (p 2588) (p 2589) (p 2641) (p 2727) (p 3238) (p 4717) (p 4809) (derived73374 p h) (derived73770 p h) (derived73282 p h) (derived73226 p h) (derived73284 p h) (derived69348 p h)

theorem derived103331 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 4516) ∨ (p 2177) ∨ (¬ p 2563) ∨ (p 2373) ∨ (p 3309) ∨ (¬ p 4034) ∨ (p 2406) :=
  ElevenRUP.step103331 (p 2177) (p 2210) (p 2299) (p 2373) (p 2406) (p 2563) (p 3238) (p 3309) (p 3549) (p 3555) (p 3880) (p 4034) (p 4516) (p 4716) (derived73412 p h) (derived73234 p h) (derived73722 p h) (derived73490 p h) (derived73406 p h) (derived73374 p h) (derived69589 p h)

theorem derived103341 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2727) ∨ (p 2264) ∨ (¬ p 4112) ∨ (p 2437) :=
  ElevenRUP.step103341 (p 2241) (p 2247) (p 2264) (p 2437) (p 2727) (p 3553) (p 3742) (p 4111) (p 4112) (derived73226 p h) (derived73518 p h) (derived73410 p h) (derived73452 p h) (derived68685 p h)

theorem derived103343 (p : Nat → Prop) (h : Inputs p) :
    (p 2982) ∨ (¬ p 2363) ∨ (¬ p 4433) ∨ (¬ p 2373) :=
  ElevenRUP.step103343 (p 2363) (p 2373) (p 2982) (p 4433) (p 4948) (derived73846 p h) (derived68919 p h)

theorem derived103345 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (p 2341) ∨ (¬ p 2156) ∨ (¬ p 2881) ∨ (¬ p 4555) :=
  ElevenRUP.step103345 (p 2156) (p 2220) (p 2341) (p 2881) (p 3551) (p 4527) (p 4555) (p 4903) (derived73618 p h) (derived73408 p h) (derived73820 p h) (derived69094 p h)

theorem derived103346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3747) ∨ (p 2220) :=
  ElevenRUP.step103346 (p 2220) (p 3051) (p 3747) (p 4527) (derived73618 p h) (derived69454 p h)

theorem derived103347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (p 2274) ∨ (¬ p 4718) ∨ (p 2177) :=
  ElevenRUP.step103347 (p 2177) (p 2274) (p 2299) (p 2911) (p 3097) (p 4718) (derived73352 p h) (derived73234 p h) (derived69101 p h)

theorem derived103358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 4972) ∨ (¬ p 2630) ∨ (p 2819) ∨ (¬ p 2363) ∨ (¬ p 2696) :=
  ElevenRUP.step103358 (p 2363) (p 2630) (p 2668) (p 2696) (p 2819) (p 4358) (p 4972) (derived73564 p h) (derived68500 p h)

theorem derived103361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2122) ∨ (¬ p 3347) ∨ (¬ p 4750) ∨ (¬ p 4811) ∨ (¬ p 3016) ∨ (p 2573) :=
  ElevenRUP.step103361 (p 2122) (p 2295) (p 2573) (p 2579) (p 3016) (p 3347) (p 3822) (p 4750) (p 4811) (p 4974) (derived73472 p h) (derived73860 p h) (derived73274 p h) (derived69180 p h)

theorem derived103364 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3073) ∨ (¬ p 2341) ∨ (¬ p 3399) :=
  ElevenRUP.step103364 (p 2341) (p 2608) (p 3073) (p 3399) (p 3954) (p 5209) (derived73498 p h) (derived73958 p h) (derived69113 p h)

theorem derived103365 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3073) ∨ (¬ p 3527) ∨ (¬ p 3399) :=
  ElevenRUP.step103365 (p 2608) (p 3073) (p 3399) (p 3527) (p 3954) (p 5306) (derived73498 p h) (derived73994 p h) (derived68430 p h)

theorem derived103369 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2717) ∨ (¬ p 2264) ∨ (¬ p 2630) ∨ (¬ p 4117) ∨ (¬ p 4357) ∨ (¬ p 4650) :=
  ElevenRUP.step103369 (p 2264) (p 2341) (p 2630) (p 2717) (p 3553) (p 3659) (p 4117) (p 4357) (p 4650) (derived73438 p h) (derived73409 p h) (derived69384 p h)

theorem derived103374 (p : Nat → Prop) (h : Inputs p) :
    (p 2132) ∨ (p 2440) ∨ (¬ p 2598) ∨ (¬ p 4750) :=
  ElevenRUP.step103374 (p 2132) (p 2138) (p 2440) (p 2542) (p 2598) (p 4750) (derived73214 p h) (derived73270 p h) (derived68314 p h)

theorem derived103375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2553) ∨ (¬ p 2177) ∨ (¬ p 2598) ∨ (¬ p 2363) :=
  ElevenRUP.step103375 (p 2122) (p 2177) (p 2363) (p 2553) (p 2588) (p 2598) (p 3822) (p 4502) (derived73471 p h) (derived73282 p h) (derived73604 p h) (derived68432 p h)

theorem derived103376 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 3083) ∨ (¬ p 4750) ∨ (¬ p 2598) :=
  ElevenRUP.step103376 (p 2098) (p 2104) (p 2598) (p 3083) (p 4750) (derived73204 p h) (derived68764 p h)

theorem derived103380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2274) ∨ (p 2563) ∨ (¬ p 4632) :=
  ElevenRUP.step103380 (p 2274) (p 2563) (p 3097) (p 3309) (p 3549) (p 4110) (p 4632) (derived73405 p h) (derived73352 p h) (derived73516 p h) (derived68871 p h)

theorem derived103381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (p 2210) ∨ (¬ p 4632) ∨ (p 2563) :=
  ElevenRUP.step103381 (p 2210) (p 2563) (p 3093) (p 4110) (p 4520) (p 4632) (derived73614 p h) (derived73516 p h) (derived68879 p h)

theorem derived103384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 3266) ∨ (¬ p 4953) ∨ (¬ p 2440) ∨ (¬ p 3343) :=
  ElevenRUP.step103384 (p 2440) (p 3266) (p 3343) (p 3506) (p 4444) (p 4953) (p 5174) (derived73580 p h) (derived73946 p h) (derived68840 p h)

theorem derived103394 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2352) ∨ (¬ p 2850) ∨ (¬ p 3955) ∨ (¬ p 4715) :=
  ElevenRUP.step103394 (p 2122) (p 2352) (p 2850) (p 3822) (p 3955) (p 4715) (derived73472 p h) (derived68287 p h)

theorem derived103395 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 3687) ∨ (¬ p 3093) ∨ (¬ p 2177) ∨ (¬ p 4870) ∨ (¬ p 3379) ∨ (p 2341) :=
  ElevenRUP.step103395 (p 2177) (p 2341) (p 3093) (p 3379) (p 3399) (p 3551) (p 3687) (p 4870) (p 5205) (derived73956 p h) (derived73408 p h) (derived69119 p h)

theorem derived103403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2992) ∨ (p 2996) ∨ (p 2274) :=
  ElevenRUP.step103403 (p 2274) (p 2295) (p 2992) (p 2996) (p 3027) (p 3097) (p 3662) (p 4560) (p 4571) (derived73644 p h) (derived73440 p h) (derived73340 p h) (derived73352 p h) (derived72955 p h) (derived69165 p h)

theorem derived103404 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (p 2727) ∨ (¬ p 2459) :=
  ElevenRUP.step103404 (p 2459) (p 2727) (p 2911) (p 2922) (p 2996) (p 3027) (p 4809) (derived73340 p h) (derived73770 p h) (derived68946 p h)

theorem derived103409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2493) ∨ (p 2187) ∨ (¬ p 2352) ∨ (¬ p 2274) :=
  ElevenRUP.step103409 (p 2187) (p 2274) (p 2307) (p 2352) (p 2493) (p 3989) (derived73502 p h) (derived68842 p h)

theorem derived103413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (p 3093) ∨ (p 2274) ∨ (¬ p 4503) ∨ (p 2459) ∨ (¬ p 2363) ∨ (p 2563) ∨ (¬ p 4632) :=
  ElevenRUP.step103413 (p 2274) (p 2363) (p 2459) (p 2563) (p 3093) (p 3097) (p 3125) (p 3591) (p 4348) (p 4503) (p 4602) (p 4632) (p 4714) (derived73432 p h) (derived73352 p h) (derived73562 p h) (derived73662 p h) (derived73720 p h) (derived68961 p h)

theorem derived103414 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2982) ∨ (¬ p 2850) ∨ (¬ p 2459) ∨ (¬ p 4733) ∨ (p 2177) ∨ (¬ p 3367) ∨ (¬ p 2230) ∨ (¬ p 4335) ∨ (¬ p 4355) ∨ (¬ p 4420) ∨ (p 3146) ∨ (¬ p 4902) ∨ (¬ p 5190) ∨ (p 3309) ∨ (¬ p 2373) :=
  ElevenRUP.step103414 (p 2177) (p 2230) (p 2299) (p 2373) (p 2459) (p 2850) (p 2982) (p 3093) (p 3146) (p 3309) (p 3367) (p 3549) (p 3591) (p 3692) (p 4335) (p 4355) (p 4420) (p 4667) (p 4733) (p 4902) (p 5190) (derived73432 p h) (derived73698 p h) (derived73234 p h) (derived73448 p h) (derived73406 p h) (derived69260 p h)

theorem derived103418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2553) ∨ (¬ p 5191) ∨ (p 2406) ∨ (¬ p 2505) ∨ (p 2230) ∨ (¬ p 4717) :=
  ElevenRUP.step103418 (p 2230) (p 2406) (p 2505) (p 2553) (p 2588) (p 2589) (p 3238) (p 3309) (p 4717) (p 5191) (derived73282 p h) (derived73374 p h) (derived73284 p h) (derived69208 p h)

theorem derived103431 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 4877) ∨ (p 2651) ∨ (¬ p 2749) ∨ (¬ p 2210) :=
  ElevenRUP.step103431 (p 2210) (p 2241) (p 2244) (p 2651) (p 2657) (p 2749) (p 4704) (p 4877) (derived73224 p h) (derived73046 p h) (derived73288 p h) (derived68417 p h)

theorem derived103432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4877) ∨ (p 2241) ∨ (p 2630) ∨ (¬ p 2284) ∨ (¬ p 2737) ∨ (¬ p 2210) ∨ (¬ p 4117) :=
  ElevenRUP.step103432 (p 2210) (p 2241) (p 2244) (p 2284) (p 2630) (p 2737) (p 2747) (p 2810) (p 4117) (p 4704) (p 4877) (derived73224 p h) (derived73316 p h) (derived73046 p h) (derived73302 p h) (derived69087 p h)

theorem derived103438 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 2608) ∨ (¬ p 2088) ∨ (¬ p 5317) :=
  ElevenRUP.step103438 (p 2088) (p 2608) (p 3073) (p 3954) (p 5000) (p 5317) (derived73868 p h) (derived73498 p h) (derived68592 p h)

theorem derived103443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2284) ∨ (p 2406) ∨ (¬ p 3660) ∨ (¬ p 4702) ∨ (p 2274) ∨ (¬ p 4203) :=
  ElevenRUP.step103443 (p 2274) (p 2284) (p 2406) (p 3097) (p 3238) (p 3309) (p 3660) (p 3952) (p 4203) (p 4702) (derived73496 p h) (derived73374 p h) (derived73352 p h) (derived69276 p h)

theorem derived103444 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2284) ∨ (p 2274) ∨ (¬ p 4702) ∨ (p 2406) ∨ (¬ p 3660) ∨ (¬ p 4203) ∨ (p 2177) :=
  ElevenRUP.step103444 (p 2177) (p 2274) (p 2284) (p 2299) (p 2406) (p 3097) (p 3238) (p 3379) (p 3452) (p 3660) (p 3952) (p 4203) (p 4702) (derived73394 p h) (derived73496 p h) (derived73352 p h) (derived73374 p h) (derived73234 p h) (derived69295 p h)

theorem derived103452 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2284) ∨ (¬ p 4790) ∨ (¬ p 2156) ∨ (¬ p 2192) ∨ (¬ p 4960) :=
  ElevenRUP.step103452 (p 2156) (p 2192) (p 2284) (p 2797) (p 4195) (p 4790) (p 4960) (derived73532 p h) (derived68659 p h)

theorem derived103453 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2249) ∨ (¬ p 4790) ∨ (p 3422) ∨ (p 2440) ∨ (p 2630) ∨ (¬ p 2590) ∨ (¬ p 2751) ∨ (p 2241) ∨ (p 2553) :=
  ElevenRUP.step103453 (p 2241) (p 2247) (p 2249) (p 2274) (p 2440) (p 2553) (p 2588) (p 2590) (p 2630) (p 2751) (p 3422) (p 4703) (p 4748) (p 4790) (p 5219) (derived73964 p h) (derived73714 p h) (derived73740 p h) (derived73226 p h) (derived73282 p h) (derived68443 p h)

theorem derived103463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2829) ∨ (p 2860) ∨ (¬ p 2737) ∨ (¬ p 4906) :=
  ElevenRUP.step103463 (p 2284) (p 2737) (p 2829) (p 2860) (p 3688) (p 3758) (p 4906) (derived73444 p h) (derived73456 p h) (derived68532 p h)

theorem derived103464 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 2850) ∨ (¬ p 4650) ∨ (¬ p 2440) ∨ (¬ p 3475) ∨ (¬ p 2663) ∨ (¬ p 3363) :=
  ElevenRUP.step103464 (p 2440) (p 2663) (p 2685) (p 2850) (p 3363) (p 3475) (p 3572) (p 4650) (derived73420 p h) (derived69031 p h)

theorem derived103466 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2850) ∨ (¬ p 2753) ∨ (¬ p 2187) ∨ (¬ p 4715) ∨ (¬ p 2598) :=
  ElevenRUP.step103466 (p 2098) (p 2104) (p 2187) (p 2598) (p 2753) (p 2850) (p 4508) (p 4715) (p 4883) (derived73204 p h) (derived73808 p h) (derived73608 p h) (derived68775 p h)

theorem derived103471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 2274) ∨ (p 2440) ∨ (¬ p 3363) ∨ (p 2850) ∨ (¬ p 4203) :=
  ElevenRUP.step103471 (p 2274) (p 2440) (p 2542) (p 2850) (p 3363) (p 3422) (p 3684) (p 4203) (derived73270 p h) (derived73442 p h) (derived68676 p h)

theorem derived103475 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 2608) ∨ (¬ p 2230) :=
  ElevenRUP.step103475 (p 2230) (p 2406) (p 2608) (p 3238) (p 3954) (derived73374 p h) (derived73498 p h) (derived72550 p h)

theorem derived103484 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3125) ∨ (p 2274) ∨ (¬ p 4276) :=
  ElevenRUP.step103484 (p 2274) (p 2417) (p 3097) (p 3125) (p 3744) (p 4276) (p 4278) (derived73546 p h) (derived73453 p h) (derived73352 p h) (derived69057 p h)

theorem derived103486 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 3016) ∨ (¬ p 2630) ∨ (¬ p 3879) ∨ (¬ p 4717) ∨ (¬ p 2727) :=
  ElevenRUP.step103486 (p 2630) (p 2727) (p 3016) (p 3136) (p 3879) (p 4315) (p 4717) (derived73550 p h) (derived69285 p h)

theorem derived103488 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2737) ∨ (p 2608) ∨ (¬ p 2241) :=
  ElevenRUP.step103488 (p 2241) (p 2608) (p 2737) (p 2747) (p 2774) (p 2780) (p 4732) (derived73308 p h) (derived73302 p h) (derived73732 p h) (derived68705 p h)

theorem derived103489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3541) ∨ (p 3379) ∨ (¬ p 2750) ∨ (p 2881) ∨ (¬ p 4558) ∨ (p 2563) ∨ (p 2573) :=
  ElevenRUP.step103489 (p 2241) (p 2563) (p 2573) (p 2579) (p 2750) (p 2881) (p 3379) (p 3541) (p 3570) (p 4558) (p 4714) (p 5189) (derived73948 p h) (derived73418 p h) (derived73720 p h) (derived73274 p h) (derived68344 p h)

theorem derived103493 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2352) ∨ (¬ p 3016) ∨ (¬ p 4811) ∨ (¬ p 3379) ∨ (¬ p 2363) :=
  ElevenRUP.step103493 (p 2352) (p 2363) (p 3016) (p 3093) (p 3379) (p 3591) (p 4811) (derived73432 p h) (derived68334 p h)

theorem derived103494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2122) ∨ (¬ p 4750) ∨ (¬ p 3016) :=
  ElevenRUP.step103494 (p 2122) (p 2553) (p 3016) (p 3822) (p 4750) (derived73472 p h) (derived68291 p h)

theorem derived103498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 2774) ∨ (¬ p 4715) ∨ (¬ p 2850) ∨ (¬ p 2753) :=
  ElevenRUP.step103498 (p 2598) (p 2753) (p 2774) (p 2780) (p 2850) (p 4715) (derived73308 p h) (derived68713 p h)

theorem derived103500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (p 3609) ∨ (¬ p 2528) ∨ (¬ p 4608) :=
  ElevenRUP.step103500 (p 2528) (p 2850) (p 3609) (p 4340) (p 4608) (derived73558 p h) (derived68560 p h)

theorem derived103502 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2641) ∨ (p 2187) ∨ (¬ p 2274) ∨ (p 2946) ∨ (¬ p 4153) ∨ (¬ p 2249) :=
  ElevenRUP.step103502 (p 2187) (p 2249) (p 2274) (p 2307) (p 2313) (p 2641) (p 2946) (p 3989) (p 4153) (derived73238 p h) (derived73502 p h) (derived68427 p h)

theorem derived103503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (p 2528) ∨ (¬ p 2363) :=
  ElevenRUP.step103503 (p 2363) (p 2528) (p 2534) (p 2553) (p 4602) (derived73268 p h) (derived73662 p h) (derived72563 p h)

theorem derived103509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4121) ∨ (p 3609) ∨ (¬ p 3256) ∨ (¬ p 3136) :=
  ElevenRUP.step103509 (p 3136) (p 3256) (p 3609) (p 4121) (p 4704) (derived73046 p h) (derived68588 p h)

theorem derived103511 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 2122) ∨ (¬ p 2088) ∨ (¬ p 2098) ∨ (¬ p 2363) :=
  ElevenRUP.step103511 (p 2088) (p 2098) (p 2104) (p 2122) (p 2363) (p 3609) (p 4340) (derived73558 p h) (derived73203 p h) (derived72567 p h)

theorem derived103514 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (p 3323) ∨ (¬ p 4153) ∨ (¬ p 3125) ∨ (p 2274) :=
  ElevenRUP.step103514 (p 2274) (p 3097) (p 3125) (p 3286) (p 3292) (p 3323) (p 4153) (p 5273) (derived73378 p h) (derived73984 p h) (derived73352 p h) (derived68959 p h)

theorem derived103531 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2088) ∨ (¬ p 2210) ∨ (¬ p 2166) :=
  ElevenRUP.step103531 (p 2088) (p 2166) (p 2210) (p 2608) (p 3954) (p 4495) (derived73498 p h) (derived73600 p h) (derived69089 p h)

theorem derived103535 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2274) ∨ (¬ p 3923) ∨ (¬ p 2210) ∨ (¬ p 3399) :=
  ElevenRUP.step103535 (p 2210) (p 2274) (p 3093) (p 3399) (p 3591) (p 3923) (derived73432 p h) (derived72580 p h)

theorem derived103536 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 2210) ∨ (p 2406) ∨ (¬ p 4607) ∨ (¬ p 3083) ∨ (¬ p 4811) :=
  ElevenRUP.step103536 (p 2210) (p 2406) (p 3083) (p 3449) (p 3860) (p 4607) (p 4627) (p 4811) (derived73482 p h) (derived73676 p h) (derived68901 p h)

theorem derived103537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 3201) ∨ (¬ p 2210) ∨ (¬ p 5217) ∨ (p 3379) ∨ (¬ p 4644) ∨ (¬ p 4210) :=
  ElevenRUP.step103537 (p 2210) (p 3201) (p 3379) (p 3399) (p 3452) (p 3876) (p 4210) (p 4644) (p 5217) (derived73486 p h) (derived73394 p h) (derived68340 p h)

theorem derived103553 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2774) ∨ (¬ p 2187) ∨ (¬ p 4889) :=
  ElevenRUP.step103553 (p 2098) (p 2104) (p 2187) (p 2774) (p 4889) (derived73204 p h) (derived68704 p h)

theorem derived103556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2528) ∨ (p 2406) ∨ (¬ p 4610) :=
  ElevenRUP.step103556 (p 2406) (p 2528) (p 3073) (p 3238) (p 4610) (derived73374 p h) (derived69219 p h)

theorem derived103558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2553) ∨ (¬ p 4717) ∨ (p 2406) ∨ (p 2230) ∨ (¬ p 5191) :=
  ElevenRUP.step103558 (p 2230) (p 2406) (p 2553) (p 2589) (p 3238) (p 3309) (p 4717) (p 5191) (derived73374 p h) (derived73284 p h) (derived69221 p h)

theorem derived103559 (p : Nat → Prop) (h : Inputs p) :
    (p 3276) ∨ (p 2241) ∨ (¬ p 3193) ∨ (p 3083) ∨ (p 2727) :=
  ElevenRUP.step103559 (p 2241) (p 2247) (p 2727) (p 3083) (p 3193) (p 3276) (p 4256) (p 4425) (p 4809) (derived73578 p h) (derived73226 p h) (derived73542 p h) (derived73770 p h) (derived68639 p h)

theorem derived103567 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3425) ∨ (¬ p 2177) ∨ (¬ p 4778) ∨ (¬ p 2696) :=
  ElevenRUP.step103567 (p 2177) (p 2341) (p 2696) (p 3425) (p 3551) (p 4778) (p 5256) (derived73408 p h) (derived73980 p h) (derived69000 p h)

theorem derived103571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (¬ p 2220) ∨ (¬ p 4632) ∨ (p 2427) ∨ (¬ p 4555) ∨ (¬ p 2177) ∨ (p 2911) ∨ (¬ p 2563) :=
  ElevenRUP.step103571 (p 2177) (p 2220) (p 2427) (p 2563) (p 2911) (p 3370) (p 3644) (p 4120) (p 4555) (p 4632) (p 4643) (derived73521 p h) (derived73684 p h) (derived73434 p h) (derived69327 p h)

theorem derived103572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (p 3379) ∨ (¬ p 4646) ∨ (p 2406) :=
  ElevenRUP.step103572 (p 2406) (p 3238) (p 3379) (p 3399) (p 3452) (p 4366) (p 4646) (derived73394 p h) (derived73569 p h) (derived73374 p h) (derived68629 p h)

theorem derived103575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3146) ∨ (¬ p 4509) ∨ (p 2563) :=
  ElevenRUP.step103575 (p 2528) (p 2563) (p 3146) (p 3692) (p 4110) (p 4509) (derived73448 p h) (derived73516 p h) (derived71236 p h)

theorem derived103577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4558) ∨ (p 2563) ∨ (p 2685) ∨ (¬ p 2655) ∨ (p 2651) ∨ (¬ p 2528) ∨ (p 2156) ∨ (¬ p 2659) ∨ (¬ p 2737) ∨ (p 2696) ∨ (¬ p 2901) ∨ (p 2132) ∨ (¬ p 5190) :=
  ElevenRUP.step103577 (p 2132) (p 2138) (p 2156) (p 2528) (p 2563) (p 2651) (p 2655) (p 2657) (p 2659) (p 2685) (p 2696) (p 2737) (p 2747) (p 2901) (p 3051) (p 3572) (p 3646) (p 4558) (p 4714) (p 4785) (p 5190) (derived73720 p h) (derived73420 p h) (derived73288 p h) (derived73436 p h) (derived73302 p h) (derived73758 p h) (derived73214 p h) (derived71237 p h)

theorem derived103582 (p : Nat → Prop) (h : Inputs p) :
    (p 3323) ∨ (¬ p 2528) ∨ (¬ p 3146) ∨ (¬ p 4384) ∨ (¬ p 2190) ∨ (p 2363) ∨ (¬ p 4564) :=
  ElevenRUP.step103582 (p 2190) (p 2363) (p 2528) (p 3146) (p 3323) (p 4037) (p 4384) (p 4564) (p 4600) (derived73508 p h) (derived73660 p h) (derived71021 p h)

theorem derived103584 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2274) ∨ (¬ p 2901) :=
  ElevenRUP.step103584 (p 2274) (p 2295) (p 2901) (p 3568) (p 4320) (p 4557) (derived73416 p h) (derived73636 p h) (derived73551 p h) (derived71162 p h)

theorem derived103586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3434) ∨ (¬ p 2656) ∨ (¬ p 4556) ∨ (¬ p 2177) ∨ (¬ p 4555) ∨ (¬ p 2363) ∨ (¬ p 3422) ∨ (¬ p 4204) ∨ (p 2274) ∨ (¬ p 5214) ∨ (¬ p 3389) ∨ (¬ p 2459) ∨ (¬ p 2641) ∨ (¬ p 2230) ∨ (p 2727) ∨ (p 3323) ∨ (¬ p 4992) ∨ (¬ p 3031) ∨ (¬ p 2264) ∨ (¬ p 2341) ∨ (¬ p 2996) ∨ (¬ p 4975) ∨ (¬ p 2437) ∨ (¬ p 5201) ∨ (p 2651) ∨ (¬ p 2911) ∨ (¬ p 2331) :=
  ElevenRUP.step103586 (p 2088) (p 2177) (p 2230) (p 2264) (p 2274) (p 2331) (p 2341) (p 2363) (p 2437) (p 2459) (p 2641) (p 2651) (p 2656) (p 2657) (p 2727) (p 2911) (p 2996) (p 3031) (p 3097) (p 3323) (p 3389) (p 3422) (p 3434) (p 3584) (p 4037) (p 4204) (p 4502) (p 4555) (p 4556) (p 4602) (p 4667) (p 4809) (p 4975) (p 4992) (p 5201) (p 5214) (derived73604 p h) (derived73662 p h) (derived73425 p h) (derived73352 p h) (derived73698 p h) (derived73770 p h) (derived73508 p h) (derived73288 p h) (derived70030 p h)

end ElevenLogic
