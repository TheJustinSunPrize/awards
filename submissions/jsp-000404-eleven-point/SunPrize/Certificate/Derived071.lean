import SunPrize.Certificate.Derived070
import SunPrize.Certificate.Logic071
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived123337 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3554) ∨ (¬ p 2192) ∨ (¬ p 2881) :=
  ElevenRUP.step123337 (p 2192) (p 2881) (p 3527) (p 3554) (p 4555) (derived105542 p h) (derived93506 p h)

theorem derived123338 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3554) ∨ (¬ p 2192) ∨ (¬ p 3246) ∨ (p 3631) :=
  ElevenRUP.step123338 (p 2192) (p 3246) (p 3554) (p 3631) (p 4555) (derived105542 p h) (derived93509 p h)

theorem derived123340 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3554) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 4202) ∨ (p 3527) :=
  ElevenRUP.step123340 (p 2911) (p 3389) (p 3527) (p 3554) (p 4202) (p 5194) (derived105489 p h) (derived93514 p h)

theorem derived123346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2190) ∨ (p 3201) ∨ (p 2363) ∨ (¬ p 4172) ∨ (p 2911) ∨ (¬ p 3146) ∨ (p 2598) ∨ (¬ p 2156) :=
  ElevenRUP.step123346 (p 2156) (p 2190) (p 2363) (p 2598) (p 2911) (p 3146) (p 3201) (p 4133) (p 4172) (p 4736) (derived105431 p h) (derived105712 p h) (derived93532 p h)

theorem derived123347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4283) ∨ (¬ p 2911) ∨ (p 2341) ∨ (p 2901) ∨ (¬ p 3741) :=
  ElevenRUP.step123347 (p 2341) (p 2901) (p 2911) (p 3741) (p 4283) (p 4702) (derived106079 p h) (derived93542 p h)

theorem derived123349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 4283) ∨ (p 2901) ∨ (p 3516) ∨ (¬ p 4431) :=
  ElevenRUP.step123349 (p 2901) (p 3516) (p 3631) (p 4283) (p 4431) (p 4960) (derived106209 p h) (derived93550 p h)

theorem derived123350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4283) ∨ (¬ p 4452) ∨ (p 2427) ∨ (¬ p 4338) ∨ (¬ p 3631) ∨ (p 3516) :=
  ElevenRUP.step123350 (p 2427) (p 3516) (p 3631) (p 4283) (p 4338) (p 4452) (p 4632) (derived106257 p h) (derived93551 p h)

theorem derived123354 (p : Nat → Prop) (h : Inputs p) :
    (p 2727) ∨ (¬ p 3093) ∨ (¬ p 3922) ∨ (p 2241) :=
  ElevenRUP.step123354 (p 2241) (p 2727) (p 3093) (p 3922) (p 4975) (derived105464 p h) (derived93584 p h)

theorem derived123356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3922) ∨ (p 4514) :=
  ElevenRUP.step123356 (p 3922) (p 4514) (p 4564) (derived105401 p h) (h 18259)

theorem derived123358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (p 4525) :=
  ElevenRUP.step123358 (p 2137) (p 4525) (p 4875) (derived106227 p h) (h 34840)

theorem derived123360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2187) ∨ (¬ p 4204) ∨ (p 2295) ∨ (p 2696) ∨ (¬ p 2839) ∨ (¬ p 2748) ∨ (p 2641) ∨ (¬ p 3051) :=
  ElevenRUP.step123360 (p 2137) (p 2187) (p 2295) (p 2641) (p 2696) (p 2748) (p 2839) (p 3051) (p 4204) (p 4405) (derived105512 p h) (derived93602 p h)

theorem derived123362 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5020) ∨ (p 2781) :=
  ElevenRUP.step123362 (p 2781) (p 4736) (p 5020) (derived105431 p h) (h 34674)

theorem derived123370 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2307) ∨ (¬ p 5020) ∨ (p 3309) ∨ (¬ p 3953) :=
  ElevenRUP.step123370 (p 2210) (p 2307) (p 3309) (p 3953) (p 4377) (p 5020) (derived106170 p h) (derived93637 p h)

theorem derived123372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3953) ∨ (p 3309) ∨ (¬ p 3367) ∨ (¬ p 4426) :=
  ElevenRUP.step123372 (p 2122) (p 3309) (p 3367) (p 3953) (p 4426) (p 4752) (derived105434 p h) (derived93640 p h)

theorem derived123374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3953) ∨ (¬ p 2737) ∨ (¬ p 2584) ∨ (¬ p 3759) ∨ (¬ p 2307) ∨ (p 3309) :=
  ElevenRUP.step123374 (p 2307) (p 2584) (p 2737) (p 3309) (p 3759) (p 3953) (p 4749) (derived105432 p h) (derived93645 p h)

theorem derived123376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2807) ∨ (p 3256) ∨ (¬ p 3919) ∨ (¬ p 2459) ∨ (¬ p 2210) ∨ (¬ p 2187) :=
  ElevenRUP.step123376 (p 2187) (p 2192) (p 2210) (p 2254) (p 2459) (p 2807) (p 3256) (p 3919) (p 4133) (derived105366 p h) (derived105712 p h) (derived93649 p h)

theorem derived123377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 3256) ∨ (¬ p 2459) ∨ (¬ p 3919) :=
  ElevenRUP.step123377 (p 2459) (p 2881) (p 3256) (p 3919) (p 4280) (derived105599 p h) (derived93650 p h)

theorem derived123378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3919) ∨ (p 5011) :=
  ElevenRUP.step123378 (p 3919) (p 4652) (p 5011) (derived105413 p h) (h 31996)

theorem derived123391 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2144) ∨ (p 2696) ∨ (¬ p 2156) :=
  ElevenRUP.step123391 (p 2144) (p 2156) (p 2696) (p 2860) (p 5052) (derived105473 p h) (derived93705 p h)

theorem derived123394 (p : Nat → Prop) (h : Inputs p) :
    (p 3366) ∨ (¬ p 2252) ∨ (p 2264) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (p 2807) ∨ (¬ p 2156) ∨ (¬ p 2144) ∨ (¬ p 5558) ∨ (¬ p 5123) :=
  ElevenRUP.step123394 (p 2144) (p 2156) (p 2252) (p 2264) (p 2750) (p 2807) (p 3125) (p 3366) (p 3461) (p 5123) (p 5558) (derived106345 p h) (derived93710 p h)

theorem derived123396 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 3487) ∨ (¬ p 4281) ∨ (p 2651) ∨ (¬ p 2946) :=
  ElevenRUP.step123396 (p 2651) (p 2751) (p 2946) (p 3136) (p 3487) (p 4281) (derived106343 p h) (derived93765 p h)

theorem derived123399 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (¬ p 4399) ∨ (¬ p 3051) ∨ (¬ p 2727) ∨ (¬ p 3699) ∨ (¬ p 2656) :=
  ElevenRUP.step123399 (p 2249) (p 2656) (p 2727) (p 2807) (p 3051) (p 3699) (p 4399) (derived106513 p h) (derived93793 p h)

theorem derived123403 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (¬ p 4364) ∨ (¬ p 3166) ∨ (¬ p 3256) :=
  ElevenRUP.step123403 (p 3166) (p 3256) (p 3609) (p 4364) (p 4790) (derived106424 p h) (derived93801 p h)

theorem derived123417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3519) ∨ (¬ p 3246) ∨ (p 2363) ∨ (¬ p 2427) ∨ (¬ p 2230) ∨ (p 2331) ∨ (¬ p 3366) ∨ (p 2819) ∨ (¬ p 4236) ∨ (¬ p 4328) ∨ (¬ p 3950) :=
  ElevenRUP.step123417 (p 2230) (p 2331) (p 2363) (p 2427) (p 2819) (p 3246) (p 3366) (p 3519) (p 3950) (p 4236) (p 4328) (p 4376) (derived106320 p h) (derived93873 p h)

theorem derived123418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (p 3166) ∨ (p 2630) ∨ (¬ p 3366) ∨ (¬ p 2187) ∨ (¬ p 3005) ∨ (¬ p 2230) ∨ (¬ p 2563) ∨ (¬ p 4236) ∨ (¬ p 3519) :=
  ElevenRUP.step123418 (p 2187) (p 2230) (p 2563) (p 2630) (p 3005) (p 3166) (p 3366) (p 3519) (p 3979) (p 4236) (p 4376) (derived106320 p h) (derived93874 p h)

theorem derived123420 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 3005) ∨ (¬ p 4236) ∨ (p 2459) ∨ (¬ p 4041) ∨ (¬ p 2220) ∨ (¬ p 3366) ∨ (¬ p 3146) ∨ (¬ p 2630) ∨ (¬ p 3370) :=
  ElevenRUP.step123420 (p 2220) (p 2459) (p 2630) (p 2651) (p 3005) (p 3146) (p 3366) (p 3370) (p 4041) (p 4236) (p 4377) (derived106170 p h) (derived93876 p h)

theorem derived123423 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2696) ∨ (¬ p 2742) ∨ (p 3051) ∨ (¬ p 3189) ∨ (p 2839) ∨ (p 3246) ∨ (¬ p 3256) :=
  ElevenRUP.step123423 (p 2143) (p 2696) (p 2742) (p 2839) (p 3051) (p 3189) (p 3246) (p 3256) (p 4669) (derived105415 p h) (derived93924 p h)

theorem derived123426 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3363) ∨ (¬ p 2696) ∨ (p 3367) ∨ (¬ p 2992) ∨ (¬ p 2742) ∨ (¬ p 3156) ∨ (p 2911) ∨ (p 3389) :=
  ElevenRUP.step123426 (p 2696) (p 2742) (p 2911) (p 2992) (p 3156) (p 3363) (p 3367) (p 3389) (p 4902) (derived105456 p h) (derived93929 p h)

theorem derived123429 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2911) ∨ (¬ p 2156) ∨ (p 3399) ∨ (¬ p 4521) ∨ (¬ p 2901) ∨ (p 2284) :=
  ElevenRUP.step123429 (p 2156) (p 2284) (p 2901) (p 2911) (p 3399) (p 3527) (p 4521) (p 4647) (derived105412 p h) (derived93934 p h)

theorem derived123432 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (p 3641) ∨ (p 2608) ∨ (¬ p 2962) ∨ (p 2274) ∨ (¬ p 2307) ∨ (¬ p 2187) ∨ (¬ p 4521) :=
  ElevenRUP.step123432 (p 2187) (p 2274) (p 2307) (p 2608) (p 2962) (p 3367) (p 3641) (p 4384) (p 4521) (derived106167 p h) (derived93941 p h)

theorem derived123435 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3171) ∨ (¬ p 2509) ∨ (p 2630) ∨ (¬ p 3005) ∨ (¬ p 2481) :=
  ElevenRUP.step123435 (p 2481) (p 2509) (p 2630) (p 3005) (p 3171) (p 4811) (derived105633 p h) (derived93965 p h)

theorem derived123436 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2252) ∨ (¬ p 3005) ∨ (p 2177) ∨ (p 3379) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (p 3166) ∨ (¬ p 2741) :=
  ElevenRUP.step123436 (p 2177) (p 2252) (p 2630) (p 2741) (p 3005) (p 3166) (p 3379) (p 3399) (p 3527) (p 4376) (derived106320 p h) (derived93979 p h)

theorem derived123443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3005) ∨ (p 2427) ∨ (p 2230) ∨ (p 3246) ∨ (¬ p 3256) :=
  ElevenRUP.step123443 (p 2230) (p 2427) (p 2696) (p 3005) (p 3246) (p 3256) (p 4669) (p 4729) (derived105415 p h) (derived105429 p h) (derived94000 p h)

theorem derived123444 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (p 2220) ∨ (¬ p 3005) ∨ (¬ p 4311) :=
  ElevenRUP.step123444 (p 2220) (p 2954) (p 3005) (p 3136) (p 4311) (derived106494 p h) (derived94001 p h)

theorem derived123445 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (¬ p 2696) ∨ (¬ p 5119) ∨ (p 2982) ∨ (¬ p 3005) ∨ (p 2230) ∨ (¬ p 4322) :=
  ElevenRUP.step123445 (p 2230) (p 2696) (p 2982) (p 3005) (p 4009) (p 4322) (p 4729) (p 5119) (derived105429 p h) (derived94005 p h)

theorem derived123451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (¬ p 2696) ∨ (p 2417) ∨ (¬ p 5119) ∨ (¬ p 3005) ∨ (p 2761) ∨ (p 3389) :=
  ElevenRUP.step123451 (p 2417) (p 2696) (p 2761) (p 3005) (p 3389) (p 4009) (p 4729) (p 5119) (derived105429 p h) (derived94016 p h)

theorem derived123456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 4236) ∨ (¬ p 2563) ∨ (p 3166) ∨ (¬ p 2230) ∨ (¬ p 2274) ∨ (¬ p 3366) ∨ (p 2685) ∨ (¬ p 3519) :=
  ElevenRUP.step123456 (p 2230) (p 2274) (p 2563) (p 2685) (p 3005) (p 3166) (p 3366) (p 3519) (p 4236) (p 4361) (p 4376) (derived106320 p h) (derived105382 p h) (derived94027 p h)

theorem derived123457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (p 2563) ∨ (p 2230) ∨ (p 3125) :=
  ElevenRUP.step123457 (p 2230) (p 2563) (p 2696) (p 3005) (p 3125) (p 3256) (p 4604) (p 4729) (derived106293 p h) (derived105429 p h) (derived94029 p h)

theorem derived123459 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (p 2563) ∨ (¬ p 2737) ∨ (¬ p 2608) ∨ (¬ p 4771) ∨ (p 2187) ∨ (¬ p 3005) :=
  ElevenRUP.step123459 (p 2187) (p 2230) (p 2563) (p 2608) (p 2737) (p 3005) (p 4771) (p 5193) (derived105488 p h) (derived94031 p h)

theorem derived123464 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (¬ p 2696) ∨ (¬ p 3005) ∨ (p 2352) ∨ (p 2573) ∨ (p 2363) :=
  ElevenRUP.step123464 (p 2352) (p 2363) (p 2573) (p 2696) (p 3005) (p 4009) (p 4729) (p 5122) (derived105483 p h) (derived105429 p h) (derived94044 p h)

theorem derived123465 (p : Nat → Prop) (h : Inputs p) :
    (p 3166) ∨ (¬ p 3005) ∨ (¬ p 2598) ∨ (¬ p 4236) :=
  ElevenRUP.step123465 (p 2598) (p 3005) (p 3166) (p 4236) (p 4752) (derived105434 p h) (derived94047 p h)

theorem derived123466 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (p 3051) ∨ (¬ p 3904) ∨ (p 2797) ∨ (¬ p 4117) ∨ (¬ p 2427) ∨ (¬ p 3005) ∨ (¬ p 2331) :=
  ElevenRUP.step123466 (p 2331) (p 2373) (p 2427) (p 2797) (p 3005) (p 3051) (p 3904) (p 4117) (p 4729) (p 5063) (derived105474 p h) (derived105429 p h) (derived94053 p h)

theorem derived123472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 3576) ∨ (¬ p 3759) ∨ (¬ p 3425) ∨ (¬ p 2373) ∨ (¬ p 2230) ∨ (¬ p 4119) ∨ (¬ p 2177) ∨ (p 3527) :=
  ElevenRUP.step123472 (p 2177) (p 2230) (p 2373) (p 3367) (p 3425) (p 3527) (p 3576) (p 3759) (p 4119) (p 4556) (derived105399 p h) (derived94092 p h)

theorem derived123474 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 3166) ∨ (¬ p 2951) ∨ (¬ p 2459) ∨ (¬ p 2187) ∨ (¬ p 2992) ∨ (¬ p 2156) ∨ (¬ p 4288) :=
  ElevenRUP.step123474 (p 2156) (p 2187) (p 2249) (p 2459) (p 2951) (p 2992) (p 3073) (p 3166) (p 4133) (p 4288) (derived105712 p h) (derived106513 p h) (derived94096 p h)

theorem derived123479 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4325) ∨ (p 2717) ∨ (¬ p 2630) ∨ (¬ p 2528) ∨ (p 2807) ∨ (¬ p 2470) ∨ (¬ p 2656) ∨ (¬ p 5558) :=
  ElevenRUP.step123479 (p 2470) (p 2528) (p 2630) (p 2656) (p 2717) (p 2807) (p 4325) (p 5118) (p 5558) (derived105482 p h) (derived94122 p h)

theorem derived123480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 3519) ∨ (p 3073) ∨ (¬ p 3389) ∨ (p 3449) ∨ (¬ p 2608) ∨ (¬ p 2911) :=
  ElevenRUP.step123480 (p 2608) (p 2911) (p 3073) (p 3389) (p 3449) (p 3519) (p 3941) (p 4376) (p 5122) (derived106320 p h) (derived105483 p h) (derived94123 p h)

theorem derived123487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2685) ∨ (¬ p 3699) ∨ (¬ p 2284) :=
  ElevenRUP.step123487 (p 2284) (p 2685) (p 3136) (p 3699) (p 4555) (derived105542 p h) (derived94171 p h)

theorem derived123493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5242) ∨ (¬ p 5693) ∨ (¬ p 3998) ∨ (p 2241) ∨ (¬ p 4436) :=
  ElevenRUP.step123493 (p 2241) (p 2744) (p 3998) (p 4436) (p 5242) (p 5693) (derived106503 p h) (derived94192 p h)

theorem derived123494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4492) ∨ (¬ p 5693) ∨ (¬ p 4874) ∨ (¬ p 5242) ∨ (p 3379) ∨ (¬ p 3998) :=
  ElevenRUP.step123494 (p 3379) (p 3998) (p 4376) (p 4492) (p 4874) (p 5242) (p 5693) (derived106320 p h) (derived94194 p h)

theorem derived123497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5693) ∨ (¬ p 4257) ∨ (¬ p 2807) ∨ (¬ p 2264) ∨ (¬ p 3379) ∨ (¬ p 2459) ∨ (¬ p 2246) ∨ (p 3449) :=
  ElevenRUP.step123497 (p 2246) (p 2264) (p 2459) (p 2744) (p 2807) (p 3379) (p 3449) (p 4257) (p 5118) (p 5693) (derived106503 p h) (derived105482 p h) (derived94209 p h)

theorem derived123500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 3449) ∨ (¬ p 5693) ∨ (¬ p 5123) ∨ (¬ p 3115) ∨ (¬ p 2608) ∨ (¬ p 2246) ∨ (¬ p 2946) :=
  ElevenRUP.step123500 (p 2246) (p 2608) (p 2744) (p 2946) (p 3115) (p 3449) (p 3680) (p 5123) (p 5693) (derived106503 p h) (derived94222 p h)

theorem derived123501 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5693) ∨ (p 3449) ∨ (¬ p 2482) ∨ (¬ p 3998) :=
  ElevenRUP.step123501 (p 2482) (p 3449) (p 3998) (p 5190) (p 5693) (derived105487 p h) (derived94223 p h)

theorem derived123502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 5693) ∨ (¬ p 2241) ∨ (p 3449) ∨ (¬ p 2753) ∨ (¬ p 3333) ∨ (¬ p 2598) ∨ (¬ p 5123) :=
  ElevenRUP.step123502 (p 2241) (p 2598) (p 2750) (p 2753) (p 3276) (p 3333) (p 3449) (p 5123) (p 5693) (derived106345 p h) (derived94224 p h)

theorem derived123506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5269) ∨ (¬ p 2778) ∨ (¬ p 2528) ∨ (¬ p 2761) ∨ (p 3654) ∨ (p 3670) ∨ (¬ p 3083) ∨ (¬ p 2651) :=
  ElevenRUP.step123506 (p 2528) (p 2651) (p 2761) (p 2778) (p 3083) (p 3654) (p 3670) (p 4669) (p 4786) (p 5269) (derived105415 p h) (derived106425 p h) (derived94241 p h)

theorem derived123507 (p : Nat → Prop) (h : Inputs p) :
    (p 3670) ∨ (p 3599) ∨ (¬ p 2437) ∨ (¬ p 2417) ∨ (¬ p 3266) ∨ (¬ p 2651) ∨ (¬ p 2246) ∨ (¬ p 3950) :=
  ElevenRUP.step123507 (p 2246) (p 2417) (p 2437) (p 2651) (p 2744) (p 3266) (p 3599) (p 3670) (p 3950) (derived106503 p h) (derived94243 p h)

theorem derived123515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 3599) ∨ (¬ p 2437) ∨ (p 2608) ∨ (¬ p 2651) ∨ (p 3670) :=
  ElevenRUP.step123515 (p 2248) (p 2437) (p 2608) (p 2651) (p 3599) (p 3670) (p 3868) (p 4826) (derived105365 p h) (derived105444 p h) (derived94292 p h)

theorem derived123517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (p 3670) ∨ (¬ p 2352) ∨ (p 2608) ∨ (¬ p 2573) ∨ (p 3599) ∨ (¬ p 5119) :=
  ElevenRUP.step123517 (p 2352) (p 2573) (p 2608) (p 3599) (p 3670) (p 3979) (p 5119) (p 5190) (derived105487 p h) (derived94297 p h)

theorem derived123520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 4153) ∨ (¬ p 2470) ∨ (p 2295) ∨ (p 2946) ∨ (¬ p 2493) ∨ (¬ p 2274) ∨ (¬ p 4079) :=
  ElevenRUP.step123520 (p 2254) (p 2274) (p 2295) (p 2470) (p 2493) (p 2509) (p 2946) (p 3958) (p 4079) (p 4153) (derived105378 p h) (derived105366 p h) (derived94325 p h)

theorem derived123522 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2528) ∨ (p 2363) ∨ (¬ p 2510) :=
  ElevenRUP.step123522 (p 2363) (p 2383) (p 2510) (p 2528) (p 2581) (derived105371 p h) (derived94332 p h)

theorem derived123524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3920) ∨ (¬ p 4386) ∨ (¬ p 3156) ∨ (¬ p 3096) ∨ (p 2449) ∨ (¬ p 2417) :=
  ElevenRUP.step123524 (p 2417) (p 2449) (p 3096) (p 3156) (p 3920) (p 4386) (p 4509) (derived105392 p h) (derived94342 p h)

theorem derived123525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4386) ∨ (¬ p 2284) ∨ (¬ p 3246) ∨ (p 2449) :=
  ElevenRUP.step123525 (p 2284) (p 2449) (p 3246) (p 4386) (p 4555) (derived105542 p h) (derived94344 p h)

theorem derived123526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 4386) ∨ (¬ p 2284) ∨ (¬ p 3691) ∨ (p 2264) :=
  ElevenRUP.step123526 (p 2264) (p 2284) (p 2341) (p 3691) (p 4386) (p 4555) (derived105542 p h) (derived94346 p h)

theorem derived123527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2573) ∨ (p 2264) ∨ (¬ p 4386) ∨ (¬ p 5201) ∨ (¬ p 4241) :=
  ElevenRUP.step123527 (p 2264) (p 2341) (p 2573) (p 4241) (p 4386) (p 4715) (p 5201) (derived105423 p h) (derived94347 p h)

theorem derived123528 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 4311) ∨ (¬ p 3189) ∨ (p 2992) :=
  ElevenRUP.step123528 (p 2220) (p 2954) (p 2992) (p 3189) (p 4311) (derived106494 p h) (derived94351 p h)

theorem derived123533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 5123) ∨ (p 2573) ∨ (p 2352) ∨ (¬ p 5580) ∨ (¬ p 2241) :=
  ElevenRUP.step123533 (p 2241) (p 2352) (p 2573) (p 3506) (p 3842) (p 5123) (p 5193) (p 5580) (derived105488 p h) (derived94388 p h)

theorem derived123534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 5558) ∨ (¬ p 5123) ∨ (p 3389) ∨ (p 2911) ∨ (¬ p 3842) ∨ (¬ p 2241) :=
  ElevenRUP.step123534 (p 2241) (p 2911) (p 3389) (p 3506) (p 3842) (p 5123) (p 5193) (p 5558) (derived105488 p h) (derived94389 p h)

theorem derived123535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 5568) ∨ (p 2373) ∨ (p 2230) ∨ (¬ p 2241) ∨ (¬ p 5123) :=
  ElevenRUP.step123535 (p 2230) (p 2241) (p 2373) (p 3506) (p 3842) (p 5123) (p 5193) (p 5568) (derived105488 p h) (derived94403 p h)

theorem derived123537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 2241) ∨ (p 2573) ∨ (p 2553) ∨ (¬ p 4260) :=
  ElevenRUP.step123537 (p 2241) (p 2553) (p 2573) (p 3506) (p 3842) (p 4260) (p 4831) (p 5193) (derived105488 p h) (derived105445 p h) (derived94406 p h)

theorem derived123538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (p 3286) ∨ (¬ p 3246) ∨ (¬ p 4656) :=
  ElevenRUP.step123538 (p 2807) (p 3246) (p 3286) (p 4280) (p 4656) (derived105599 p h) (derived94419 p h)

theorem derived123539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (p 3286) ∨ (¬ p 2264) ∨ (¬ p 4656) :=
  ElevenRUP.step123539 (p 2264) (p 2807) (p 3286) (p 4656) (p 4666) (derived105658 p h) (derived94421 p h)

theorem derived123544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 2630) ∨ (¬ p 4781) ∨ (p 2449) :=
  ElevenRUP.step123544 (p 2449) (p 2630) (p 3434) (p 4652) (p 4781) (derived105413 p h) (derived94442 p h)

theorem derived123548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 3820) ∨ (¬ p 2598) ∨ (¬ p 4781) ∨ (p 3516) :=
  ElevenRUP.step123548 (p 2598) (p 3434) (p 3516) (p 3820) (p 4752) (p 4781) (derived105434 p h) (derived94454 p h)

theorem derived123553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 5020) ∨ (¬ p 4512) ∨ (p 2608) ∨ (p 3309) :=
  ElevenRUP.step123553 (p 2307) (p 2608) (p 3309) (p 4512) (p 4877) (p 5020) (derived105451 p h) (derived94500 p h)

theorem derived123554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 2166) ∨ (¬ p 2274) ∨ (p 3309) :=
  ElevenRUP.step123554 (p 2166) (p 2274) (p 3309) (p 4509) (p 4512) (derived105392 p h) (derived94501 p h)

theorem derived123555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 3743) ∨ (¬ p 2307) ∨ (p 3309) ∨ (¬ p 2166) :=
  ElevenRUP.step123555 (p 2166) (p 2307) (p 3309) (p 3743) (p 4509) (p 4512) (derived105392 p h) (derived94502 p h)

theorem derived123557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 3743) ∨ (¬ p 2891) ∨ (¬ p 3654) ∨ (p 3319) :=
  ElevenRUP.step123557 (p 2891) (p 3319) (p 3654) (p 3743) (p 4512) (p 4558) (derived105400 p h) (derived94514 p h)

theorem derived123563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 2972) ∨ (p 3309) ∨ (¬ p 2274) :=
  ElevenRUP.step123563 (p 2274) (p 2972) (p 3309) (p 4512) (p 5046) (derived105472 p h) (derived94526 p h)

theorem derived123564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 3564) ∨ (¬ p 3016) ∨ (¬ p 4202) ∨ (p 3319) :=
  ElevenRUP.step123564 (p 3016) (p 3319) (p 3564) (p 4202) (p 4512) (p 4811) (derived105633 p h) (derived94527 p h)

theorem derived123568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (p 3399) ∨ (¬ p 3093) ∨ (¬ p 4512) ∨ (¬ p 3286) ∨ (p 3631) ∨ (¬ p 2753) ∨ (¬ p 4117) ∨ (p 3276) :=
  ElevenRUP.step123568 (p 2753) (p 3093) (p 3276) (p 3286) (p 3399) (p 3506) (p 3631) (p 4117) (p 4512) (p 4638) (p 4877) (derived105451 p h) (derived105409 p h) (derived94536 p h)

theorem derived123570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4282) ∨ (p 3319) ∨ (¬ p 3125) ∨ (¬ p 4512) ∨ (¬ p 2901) :=
  ElevenRUP.step123570 (p 2901) (p 3125) (p 3319) (p 4282) (p 4512) (p 4558) (derived105400 p h) (derived94539 p h)

theorem derived123574 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (p 2459) ∨ (¬ p 3325) ∨ (¬ p 2363) :=
  ElevenRUP.step123574 (p 2315) (p 2341) (p 2363) (p 2459) (p 3325) (derived105368 p h) (derived94545 p h)

theorem derived123579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3691) ∨ (p 2264) ∨ (¬ p 2427) ∨ (¬ p 4386) :=
  ElevenRUP.step123579 (p 2264) (p 2341) (p 2427) (p 3691) (p 4386) (p 4702) (derived106079 p h) (derived94577 p h)

theorem derived123580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3691) ∨ (¬ p 2341) ∨ (¬ p 2901) ∨ (p 2911) ∨ (¬ p 2441) :=
  ElevenRUP.step123580 (p 2341) (p 2441) (p 2901) (p 2911) (p 3691) (p 4705) (derived106238 p h) (derived94579 p h)

theorem derived123588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4492) ∨ (¬ p 2192) ∨ (p 2553) ∨ (p 3422) ∨ (¬ p 4172) ∨ (p 3073) ∨ (¬ p 2220) ∨ (p 2598) ∨ (¬ p 3146) :=
  ElevenRUP.step123588 (p 2192) (p 2220) (p 2553) (p 2598) (p 3073) (p 3146) (p 3422) (p 4172) (p 4492) (p 4736) (derived105431 p h) (derived94602 p h)

theorem derived123590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 4492) ∨ (¬ p 2891) ∨ (¬ p 3096) ∨ (p 3073) ∨ (¬ p 2528) :=
  ElevenRUP.step123590 (p 2510) (p 2528) (p 2891) (p 3073) (p 3096) (p 4492) (p 4558) (derived105400 p h) (derived94609 p h)

theorem derived123595 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 3906) ∨ (¬ p 2753) ∨ (¬ p 2696) ∨ (¬ p 2210) ∨ (¬ p 2685) ∨ (¬ p 2449) ∨ (¬ p 3950) ∨ (p 3146) :=
  ElevenRUP.step123595 (p 2210) (p 2449) (p 2685) (p 2696) (p 2753) (p 3146) (p 3449) (p 3906) (p 3950) (p 4877) (derived105451 p h) (derived94629 p h)

theorem derived123598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (p 2839) ∨ (¬ p 2668) ∨ (¬ p 2742) ∨ (¬ p 2696) ∨ (¬ p 2641) ∨ (p 2088) ∨ (¬ p 3697) ∨ (¬ p 3146) :=
  ElevenRUP.step123598 (p 2088) (p 2143) (p 2641) (p 2668) (p 2696) (p 2742) (p 2839) (p 3146) (p 3697) (p 4134) (derived105379 p h) (derived94640 p h)

theorem derived123599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3697) ∨ (p 2088) ∨ (¬ p 3146) ∨ (¬ p 3156) :=
  ElevenRUP.step123599 (p 2088) (p 2954) (p 3146) (p 3156) (p 3697) (derived106494 p h) (derived94641 p h)

theorem derived123600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3697) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (p 2088) :=
  ElevenRUP.step123600 (p 2088) (p 2373) (p 3146) (p 3697) (p 4533) (derived105394 p h) (derived94644 p h)

theorem derived123603 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3697) ∨ (¬ p 2510) ∨ (¬ p 3096) ∨ (¬ p 2528) ∨ (p 2088) ∨ (¬ p 3051) :=
  ElevenRUP.step123603 (p 2088) (p 2510) (p 2528) (p 3051) (p 3096) (p 3697) (p 4558) (derived105400 p h) (derived94651 p h)

theorem derived123609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5584) ∨ (¬ p 4228) ∨ (p 2668) ∨ (¬ p 5558) :=
  ElevenRUP.step123609 (p 2668) (p 4228) (p 4503) (p 5558) (p 5584) (derived106530 p h) (derived94690 p h)

theorem derived123612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 2220) ∨ (¬ p 2331) ∨ (¬ p 2166) ∨ (¬ p 3948) ∨ (¬ p 4116) :=
  ElevenRUP.step123612 (p 2166) (p 2220) (p 2331) (p 2950) (p 3948) (p 4116) (p 4975) (derived105464 p h) (derived94754 p h)

theorem derived123615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4198) ∨ (¬ p 3051) ∨ (p 2383) ∨ (¬ p 2187) :=
  ElevenRUP.step123615 (p 2187) (p 2383) (p 3051) (p 4198) (p 4558) (derived105400 p h) (derived94768 p h)

theorem derived123625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4198) ∨ (p 2088) ∨ (¬ p 3146) ∨ (¬ p 4197) ∨ (¬ p 3156) :=
  ElevenRUP.step123625 (p 2088) (p 2954) (p 3146) (p 3156) (p 4197) (p 4198) (derived106494 p h) (derived94788 p h)

theorem derived123630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2957) ∨ (¬ p 4198) ∨ (p 2307) ∨ (¬ p 3156) ∨ (¬ p 2274) :=
  ElevenRUP.step123630 (p 2274) (p 2307) (p 2957) (p 3156) (p 4198) (p 4509) (derived105392 p h) (derived94800 p h)

theorem derived123633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 4198) ∨ (p 3516) ∨ (¬ p 2311) ∨ (¬ p 3246) :=
  ElevenRUP.step123633 (p 2311) (p 2891) (p 3246) (p 3516) (p 4198) (p 4522) (derived105393 p h) (derived94810 p h)

theorem derived123639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 4169) ∨ (¬ p 4445) ∨ (¬ p 2717) ∨ (p 3246) :=
  ElevenRUP.step123639 (p 2717) (p 3246) (p 3941) (p 4169) (p 4445) (p 5122) (derived105483 p h) (derived94831 p h)

theorem derived123640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4169) ∨ (p 4477) :=
  ElevenRUP.step123640 (p 4169) (p 4477) (p 4559) (derived105701 p h) (h 22439)

theorem derived123642 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 4136) ∨ (¬ p 2891) ∨ (¬ p 2881) :=
  ElevenRUP.step123642 (p 2717) (p 2881) (p 2891) (p 4136) (p 4878) (derived105452 p h) (derived94839 p h)

theorem derived123646 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4136) ∨ (¬ p 2860) ∨ (p 3434) ∨ (¬ p 3246) :=
  ElevenRUP.step123646 (p 2860) (p 3246) (p 3434) (p 4136) (p 4555) (derived105542 p h) (derived94850 p h)

theorem derived123647 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (p 3051) ∨ (¬ p 2136) ∨ (¬ p 2860) ∨ (¬ p 4136) :=
  ElevenRUP.step123647 (p 2136) (p 2860) (p 3051) (p 3425) (p 4136) (p 4555) (derived105542 p h) (derived94851 p h)

theorem derived123651 (p : Nat → Prop) (h : Inputs p) :
    (p 3434) ∨ (¬ p 4136) ∨ (¬ p 3246) ∨ (¬ p 3872) ∨ (¬ p 2619) :=
  ElevenRUP.step123651 (p 2619) (p 3246) (p 3434) (p 3872) (p 4136) (p 4509) (derived105392 p h) (derived94860 p h)

theorem derived123653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 4136) ∨ (¬ p 2427) ∨ (p 3434) :=
  ElevenRUP.step123653 (p 2427) (p 3246) (p 3434) (p 4136) (p 4882) (derived105453 p h) (derived94870 p h)

theorem derived123662 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4194) ∨ (¬ p 4109) ∨ (¬ p 2962) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 2437) :=
  ElevenRUP.step123662 (p 2383) (p 2437) (p 2668) (p 2962) (p 4109) (p 4194) (p 4646) (derived105534 p h) (derived94895 p h)

theorem derived123664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2352) ∨ (p 2668) ∨ (¬ p 4194) :=
  ElevenRUP.step123664 (p 2352) (p 2573) (p 2665) (p 2668) (p 4194) (derived105373 p h) (derived94897 p h)

theorem derived123667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4194) ∨ (p 2440) ∨ (¬ p 2553) ∨ (p 2295) :=
  ElevenRUP.step123667 (p 2295) (p 2440) (p 2553) (p 4194) (p 4715) (derived105423 p h) (derived94902 p h)

theorem derived123668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2177) ∨ (p 2264) ∨ (¬ p 4067) :=
  ElevenRUP.step123668 (p 2177) (p 2264) (p 2307) (p 4067) (p 4584) (derived105406 p h) (derived94903 p h)

theorem derived123670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2630) ∨ (¬ p 2667) ∨ (¬ p 4426) ∨ (p 2383) :=
  ElevenRUP.step123670 (p 2383) (p 2630) (p 2667) (p 2819) (p 4426) (p 4975) (derived105464 p h) (derived94909 p h)

theorem derived123672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4426) ∨ (¬ p 2122) ∨ (p 2641) ∨ (p 2295) :=
  ElevenRUP.step123672 (p 2122) (p 2295) (p 2641) (p 2745) (p 4426) (derived105523 p h) (derived94916 p h)

theorem derived123674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 5109) ∨ (p 2528) ∨ (¬ p 3755) ∨ (p 2797) ∨ (¬ p 2331) ∨ (p 3379) :=
  ElevenRUP.step123674 (p 2248) (p 2331) (p 2509) (p 2528) (p 2797) (p 3379) (p 3755) (p 5109) (derived105365 p h) (derived94937 p h)

theorem derived123684 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3755) ∨ (¬ p 5109) ∨ (p 2373) ∨ (p 2230) ∨ (p 3146) ∨ (¬ p 4117) ∨ (¬ p 2331) :=
  ElevenRUP.step123684 (p 2230) (p 2331) (p 2373) (p 2797) (p 3146) (p 3755) (p 4117) (p 4729) (p 5109) (derived105429 p h) (derived94986 p h)

theorem derived123685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3755) ∨ (p 2373) ∨ (¬ p 5568) ∨ (¬ p 2696) ∨ (p 2230) ∨ (¬ p 5123) :=
  ElevenRUP.step123685 (p 2230) (p 2373) (p 2696) (p 3506) (p 3755) (p 4729) (p 5123) (p 5568) (derived105429 p h) (derived95000 p h)

theorem derived123688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3755) ∨ (p 2553) ∨ (¬ p 2696) ∨ (¬ p 4260) ∨ (¬ p 3589) ∨ (p 2573) :=
  ElevenRUP.step123688 (p 2553) (p 2573) (p 2696) (p 3506) (p 3589) (p 3755) (p 4260) (p 4831) (p 5193) (derived105488 p h) (derived105445 p h) (derived95011 p h)

theorem derived123691 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3755) ∨ (¬ p 2696) ∨ (p 2553) ∨ (¬ p 4260) ∨ (¬ p 4203) ∨ (¬ p 2145) ∨ (p 2156) :=
  ElevenRUP.step123691 (p 2145) (p 2156) (p 2553) (p 2696) (p 3506) (p 3755) (p 4203) (p 4260) (p 4831) (derived105445 p h) (derived95018 p h)

theorem derived123693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3755) ∨ (¬ p 2737) ∨ (p 3246) ∨ (p 2427) ∨ (¬ p 4658) ∨ (¬ p 2608) ∨ (p 2230) :=
  ElevenRUP.step123693 (p 2230) (p 2427) (p 2608) (p 2737) (p 3246) (p 3755) (p 4658) (p 5193) (derived105488 p h) (derived95024 p h)

theorem derived123695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3755) ∨ (p 2685) ∨ (¬ p 5109) ∨ (¬ p 2807) ∨ (¬ p 4117) ∨ (p 2230) ∨ (p 3146) ∨ (p 2373) :=
  ElevenRUP.step123695 (p 2230) (p 2373) (p 2685) (p 2807) (p 3146) (p 3755) (p 4117) (p 4729) (p 5109) (derived105429 p h) (derived95040 p h)

theorem derived123696 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 4236) ∨ (¬ p 3755) ∨ (p 2553) ∨ (¬ p 4774) ∨ (¬ p 2352) ∨ (¬ p 2307) ∨ (p 3286) ∨ (¬ p 5016) ∨ (¬ p 3366) :=
  ElevenRUP.step123696 (p 2307) (p 2352) (p 2553) (p 3005) (p 3286) (p 3366) (p 3755) (p 4236) (p 4774) (p 4866) (p 5016) (derived106063 p h) (derived95049 p h)

theorem derived123698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 4512) ∨ (¬ p 5109) ∨ (¬ p 3204) ∨ (p 3461) ∨ (p 2630) ∨ (¬ p 3266) ∨ (¬ p 3755) ∨ (¬ p 2651) ∨ (¬ p 2753) ∨ (p 3654) :=
  ElevenRUP.step123698 (p 2630) (p 2651) (p 2753) (p 3204) (p 3266) (p 3461) (p 3654) (p 3755) (p 4117) (p 4512) (p 4877) (p 5109) (derived105451 p h) (derived95054 p h)

theorem derived123701 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5568) ∨ (¬ p 4238) ∨ (¬ p 3998) ∨ (p 2373) :=
  ElevenRUP.step123701 (p 2373) (p 3998) (p 4238) (p 4539) (p 5568) (derived105395 p h) (derived95078 p h)

theorem derived123702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (p 3051) ∨ (¬ p 4333) ∨ (p 2459) ∨ (p 2264) ∨ (p 3461) ∨ (¬ p 3362) ∨ (¬ p 3355) ∨ (¬ p 2145) :=
  ElevenRUP.step123702 (p 2145) (p 2264) (p 2459) (p 3051) (p 3276) (p 3355) (p 3362) (p 3461) (p 4330) (p 4333) (derived106329 p h) (derived95087 p h)

theorem derived123706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5197) ∨ (¬ p 2911) ∨ (p 2341) ∨ (¬ p 3741) ∨ (¬ p 2573) :=
  ElevenRUP.step123706 (p 2341) (p 2573) (p 2911) (p 3741) (p 4717) (p 5197) (derived105424 p h) (derived95097 p h)

theorem derived123715 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 3389) ∨ (p 3146) ∨ (¬ p 2663) ∨ (¬ p 2136) ∨ (p 2437) ∨ (¬ p 3083) ∨ (¬ p 2363) ∨ (¬ p 3988) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 4596) :=
  ElevenRUP.step123715 (p 2136) (p 2156) (p 2246) (p 2363) (p 2437) (p 2663) (p 2744) (p 3083) (p 3146) (p 3366) (p 3389) (p 3988) (p 4596) (derived106503 p h) (derived95124 p h)

theorem derived123719 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 4313) ∨ (¬ p 2598) ∨ (¬ p 2136) ∨ (¬ p 2619) :=
  ElevenRUP.step123719 (p 2136) (p 2220) (p 2598) (p 2619) (p 4313) (p 4752) (derived105434 p h) (derived95135 p h)

theorem derived123725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3412) ∨ (¬ p 2192) ∨ (¬ p 3773) ∨ (¬ p 3297) ∨ (¬ p 2946) ∨ (¬ p 3266) ∨ (¬ p 3125) ∨ (¬ p 3848) :=
  ElevenRUP.step123725 (p 2192) (p 2255) (p 2946) (p 3125) (p 3266) (p 3297) (p 3412) (p 3773) (p 3848) (p 4330) (derived105367 p h) (derived106329 p h) (derived51687 p h)

theorem derived123726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2156) ∨ (¬ p 2727) ∨ (¬ p 2241) ∨ (p 2274) ∨ (p 2177) :=
  ElevenRUP.step123726 (p 2156) (p 2177) (p 2241) (p 2274) (p 2727) (p 3083) (p 4420) (derived105707 p h) (derived95161 p h)

theorem derived123734 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 4436) ∨ (¬ p 2088) ∨ (p 2241) ∨ (¬ p 5242) :=
  ElevenRUP.step123734 (p 2088) (p 2241) (p 2744) (p 3073) (p 4436) (p 5242) (derived106503 p h) (derived95196 p h)

theorem derived123735 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (p 3399) ∨ (¬ p 2396) ∨ (¬ p 2156) ∨ (p 3527) ∨ (¬ p 2608) ∨ (¬ p 2274) :=
  ElevenRUP.step123735 (p 2156) (p 2274) (p 2396) (p 2608) (p 3370) (p 3399) (p 3527) (p 4377) (p 4668) (derived105414 p h) (derived106170 p h) (derived95200 p h)

theorem derived123736 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3369) ∨ (¬ p 4032) ∨ (¬ p 2972) ∨ (¬ p 2608) :=
  ElevenRUP.step123736 (p 2608) (p 2972) (p 3369) (p 4032) (p 4377) (derived106170 p h) (derived63822 p h)

theorem derived123737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (p 3379) ∨ (¬ p 4438) ∨ (¬ p 3370) ∨ (¬ p 2220) ∨ (¬ p 2509) ∨ (p 2459) ∨ (¬ p 2608) :=
  ElevenRUP.step123737 (p 2220) (p 2459) (p 2509) (p 2608) (p 3146) (p 3370) (p 3379) (p 4377) (p 4438) (derived106170 p h) (derived95201 p h)

theorem derived123739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4373) ∨ (p 5370) :=
  ElevenRUP.step123739 (p 4373) (p 4752) (p 5370) (derived105434 p h) (h 26298)

theorem derived123742 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 2685) ∨ (¬ p 2807) ∨ (¬ p 3347) ∨ (¬ p 4117) ∨ (p 2470) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (p 2528) :=
  ElevenRUP.step123742 (p 2470) (p 2528) (p 2685) (p 2753) (p 2807) (p 3005) (p 3146) (p 3347) (p 4117) (p 5063) (derived105474 p h) (derived95216 p h)

theorem derived123744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4040) ∨ (p 3286) ∨ (¬ p 2972) ∨ (¬ p 2946) :=
  ElevenRUP.step123744 (p 2946) (p 2972) (p 3286) (p 4040) (p 4960) (derived106209 p h) (derived95221 p h)

theorem derived123750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 2860) ∨ (¬ p 2509) ∨ (¬ p 2187) :=
  ElevenRUP.step123750 (p 2132) (p 2187) (p 2459) (p 2509) (p 2528) (p 2753) (p 2860) (p 4133) (derived105712 p h) (derived95242 p h)

theorem derived123751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (p 2098) ∨ (p 3609) ∨ (¬ p 2641) ∨ (¬ p 2459) ∨ (¬ p 2668) :=
  ElevenRUP.step123751 (p 2098) (p 2241) (p 2459) (p 2641) (p 2668) (p 3609) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived95243 p h)

theorem derived123752 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (p 2528) ∨ (¬ p 2459) ∨ (¬ p 3347) ∨ (¬ p 3093) ∨ (p 2608) ∨ (p 2470) :=
  ElevenRUP.step123752 (p 2459) (p 2470) (p 2528) (p 2608) (p 3063) (p 3093) (p 3347) (p 4133) (derived105712 p h) (derived95244 p h)

theorem derived123754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (¬ p 4744) ∨ (p 2860) ∨ (¬ p 5568) :=
  ElevenRUP.step123754 (p 2860) (p 4019) (p 4509) (p 4744) (p 5568) (derived105392 p h) (derived95252 p h)

theorem derived123756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2427) ∨ (¬ p 3519) ∨ (p 3005) ∨ (p 2696) ∨ (¬ p 3366) ∨ (¬ p 3950) ∨ (p 3256) ∨ (¬ p 2230) :=
  ElevenRUP.step123756 (p 2230) (p 2427) (p 2696) (p 3005) (p 3246) (p 3256) (p 3366) (p 3519) (p 3950) (p 4376) (derived106320 p h) (derived95263 p h)

theorem derived123757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3519) ∨ (p 2696) ∨ (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 3366) ∨ (p 3005) ∨ (¬ p 5600) ∨ (¬ p 5123) :=
  ElevenRUP.step123757 (p 2573) (p 2696) (p 3005) (p 3366) (p 3461) (p 3519) (p 3564) (p 4376) (p 5123) (p 5600) (derived106320 p h) (derived95265 p h)

theorem derived123761 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2584) ∨ (¬ p 3654) ∨ (p 2493) ∨ (p 3564) :=
  ElevenRUP.step123761 (p 2493) (p 2584) (p 3564) (p 3654) (p 5194) (derived105489 p h) (derived95330 p h)

theorem derived123763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 4399) ∨ (p 2563) ∨ (p 2406) :=
  ElevenRUP.step123763 (p 2156) (p 2406) (p 2563) (p 4399) (p 5194) (derived105489 p h) (derived95331 p h)

theorem derived123764 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (p 2651) ∨ (¬ p 3527) ∨ (p 3564) ∨ (¬ p 2459) ∨ (¬ p 3399) :=
  ElevenRUP.step123764 (p 2254) (p 2459) (p 2651) (p 3016) (p 3399) (p 3527) (p 3564) (p 4604) (derived105366 p h) (derived106293 p h) (derived95335 p h)

theorem derived123765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3577) ∨ (¬ p 2707) ∨ (p 2493) ∨ (p 2598) ∨ (p 3564) ∨ (¬ p 2341) ∨ (¬ p 4030) ∨ (¬ p 2459) :=
  ElevenRUP.step123765 (p 2341) (p 2459) (p 2493) (p 2598) (p 2707) (p 3564) (p 3577) (p 4030) (p 4604) (derived106293 p h) (derived95339 p h)

theorem derived123766 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (¬ p 2946) ∨ (p 2598) ∨ (¬ p 3156) ∨ (¬ p 3146) ∨ (p 3564) :=
  ElevenRUP.step123766 (p 2598) (p 2946) (p 3146) (p 3156) (p 3422) (p 3564) (p 4604) (p 4786) (derived106293 p h) (derived106425 p h) (derived95340 p h)

theorem derived123773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3346) ∨ (¬ p 4399) ∨ (p 2427) :=
  ElevenRUP.step123773 (p 2427) (p 3051) (p 3346) (p 4399) (p 4949) (derived105463 p h) (derived95369 p h)

theorem derived123774 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 2156) ∨ (¬ p 4399) ∨ (p 2563) :=
  ElevenRUP.step123774 (p 2156) (p 2470) (p 2563) (p 4399) (p 4608) (derived105540 p h) (derived95370 p h)

theorem derived123779 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2641) ∨ (¬ p 3389) ∨ (¬ p 2911) ∨ (p 3323) ∨ (¬ p 2459) :=
  ElevenRUP.step123779 (p 2241) (p 2459) (p 2641) (p 2911) (p 3323) (p 3389) (p 4604) (p 5190) (derived106293 p h) (derived105487 p h) (derived95379 p h)

theorem derived123780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 3189) ∨ (p 2241) ∨ (¬ p 3125) ∨ (¬ p 2563) ∨ (p 3256) :=
  ElevenRUP.step123780 (p 2230) (p 2241) (p 2563) (p 3125) (p 3189) (p 3256) (p 4330) (p 5190) (derived105487 p h) (derived106329 p h) (derived95384 p h)

theorem derived123781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 2573) ∨ (¬ p 4041) ∨ (p 3073) ∨ (¬ p 2553) ∨ (p 3449) ∨ (¬ p 2177) :=
  ElevenRUP.step123781 (p 2177) (p 2553) (p 2573) (p 3073) (p 3256) (p 3449) (p 4041) (p 5190) (derived105487 p h) (derived95387 p h)

theorem derived123787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2742) ∨ (p 2383) ∨ (¬ p 2598) ∨ (¬ p 4759) ∨ (¬ p 3063) :=
  ElevenRUP.step123787 (p 2383) (p 2598) (p 2742) (p 2778) (p 3063) (p 4752) (p 4759) (derived105434 p h) (derived95436 p h)

theorem derived123790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 2819) ∨ (p 2383) ∨ (¬ p 2778) ∨ (¬ p 3917) ∨ (p 2761) ∨ (¬ p 3355) ∨ (¬ p 4419) :=
  ElevenRUP.step123790 (p 2383) (p 2761) (p 2778) (p 2819) (p 3276) (p 3355) (p 3917) (p 4419) (p 4625) (derived106455 p h) (derived95448 p h)

theorem derived123791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2122) ∨ (¬ p 2778) ∨ (p 2241) ∨ (p 2307) ∨ (¬ p 2210) ∨ (¬ p 4397) ∨ (¬ p 3366) ∨ (¬ p 2972) :=
  ElevenRUP.step123791 (p 2122) (p 2210) (p 2241) (p 2307) (p 2744) (p 2778) (p 2972) (p 3366) (p 3917) (p 4397) (derived106503 p h) (derived95449 p h)

theorem derived123797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3564) ∨ (¬ p 3346) ∨ (¬ p 4440) :=
  ElevenRUP.step123797 (p 2573) (p 3346) (p 3564) (p 4330) (p 4440) (derived106329 p h) (derived64987 p h)

theorem derived123800 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2651) ∨ (¬ p 2807) ∨ (¬ p 3579) :=
  ElevenRUP.step123800 (p 2651) (p 2807) (p 3201) (p 3579) (p 4750) (derived105433 p h) (derived95490 p h)

theorem derived123802 (p : Nat → Prop) (h : Inputs p) :
    (p 3286) ∨ (¬ p 3579) ∨ (¬ p 4656) ∨ (¬ p 2396) ∨ (¬ p 2807) :=
  ElevenRUP.step123802 (p 2396) (p 2807) (p 3286) (p 3579) (p 4276) (p 4656) (derived105516 p h) (derived95499 p h)

theorem derived123806 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4331) ∨ (¬ p 3333) ∨ (p 2553) ∨ (p 3422) :=
  ElevenRUP.step123806 (p 2553) (p 3333) (p 3422) (p 4331) (p 4624) (derived105408 p h) (derived95560 p h)

theorem derived123810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (p 3422) ∨ (¬ p 2573) ∨ (¬ p 3362) ∨ (p 2807) ∨ (p 2264) ∨ (p 2459) ∨ (¬ p 4332) :=
  ElevenRUP.step123810 (p 2264) (p 2459) (p 2573) (p 2807) (p 3333) (p 3362) (p 3422) (p 4332) (p 4789) (derived105646 p h) (derived95570 p h)

theorem derived123813 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (p 3422) ∨ (¬ p 2573) ∨ (p 2946) ∨ (p 3146) ∨ (p 3156) ∨ (¬ p 3362) ∨ (¬ p 4331) :=
  ElevenRUP.step123813 (p 2573) (p 2946) (p 3146) (p 3156) (p 3333) (p 3362) (p 3422) (p 4330) (p 4331) (p 4789) (derived106329 p h) (derived105646 p h) (derived95577 p h)

theorem derived123814 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4032) ∨ (¬ p 4322) ∨ (¬ p 3333) ∨ (p 2753) ∨ (¬ p 3367) ∨ (¬ p 2761) ∨ (p 2696) ∨ (¬ p 3645) ∨ (¬ p 4243) :=
  ElevenRUP.step123814 (p 2696) (p 2753) (p 2761) (p 3333) (p 3367) (p 3645) (p 4032) (p 4243) (p 4322) (p 4638) (p 5052) (derived105473 p h) (derived105409 p h) (derived95579 p h)

theorem derived123821 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3333) ∨ (p 2264) ∨ (¬ p 2598) ∨ (p 2807) ∨ (¬ p 5558) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (¬ p 5123) :=
  ElevenRUP.step123821 (p 2252) (p 2264) (p 2598) (p 2750) (p 2753) (p 2807) (p 3276) (p 3333) (p 5123) (p 5558) (derived106345 p h) (derived95600 p h)

theorem derived123823 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 4343) ∨ (¬ p 2651) ∨ (¬ p 3333) ∨ (p 3146) ∨ (¬ p 5600) ∨ (p 3136) ∨ (¬ p 3969) ∨ (¬ p 3661) :=
  ElevenRUP.step123823 (p 2651) (p 3136) (p 3146) (p 3276) (p 3333) (p 3661) (p 3969) (p 4343) (p 4790) (p 5600) (derived106424 p h) (derived95606 p h)

theorem derived123825 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3362) ∨ (¬ p 2230) ∨ (¬ p 3333) ∨ (¬ p 4332) ∨ (p 2668) ∨ (p 2331) ∨ (p 2363) ∨ (p 2850) :=
  ElevenRUP.step123825 (p 2230) (p 2331) (p 2363) (p 2668) (p 2850) (p 3333) (p 3362) (p 4332) (p 4789) (derived105646 p h) (derived95609 p h)

theorem derived123826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (p 3201) ∨ (¬ p 3389) ∨ (¬ p 4332) ∨ (p 2668) ∨ (p 2331) ∨ (¬ p 3362) ∨ (p 2363) :=
  ElevenRUP.step123826 (p 2331) (p 2363) (p 2668) (p 3201) (p 3333) (p 3362) (p 3389) (p 4332) (p 4789) (derived105646 p h) (derived95610 p h)

theorem derived123830 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 2598) ∨ (p 2331) ∨ (¬ p 2753) ∨ (p 2668) ∨ (¬ p 5580) ∨ (¬ p 2252) ∨ (¬ p 5123) :=
  ElevenRUP.step123830 (p 2252) (p 2331) (p 2598) (p 2668) (p 2750) (p 2753) (p 3276) (p 3333) (p 5123) (p 5580) (derived106345 p h) (derived95625 p h)

theorem derived123831 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 4332) ∨ (p 2459) ∨ (p 2264) ∨ (¬ p 2230) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (p 2807) :=
  ElevenRUP.step123831 (p 2230) (p 2264) (p 2459) (p 2807) (p 2850) (p 3333) (p 3362) (p 4332) (p 4789) (derived105646 p h) (derived95627 p h)

theorem derived123835 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (p 3641) ∨ (¬ p 3905) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 4438) ∨ (¬ p 3346) ∨ (¬ p 2177) :=
  ElevenRUP.step123835 (p 2177) (p 2295) (p 2331) (p 3333) (p 3346) (p 3641) (p 3905) (p 4438) (p 4786) (derived106425 p h) (derived95643 p h)

theorem derived123837 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3425) ∨ (¬ p 2264) ∨ (¬ p 2156) ∨ (p 2563) ∨ (¬ p 2427) ∨ (¬ p 2139) :=
  ElevenRUP.step123837 (p 2139) (p 2156) (p 2264) (p 2427) (p 2563) (p 2717) (p 3425) (p 4362) (derived106173 p h) (derived95650 p h)

theorem derived123841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4984) ∨ (¬ p 2156) ∨ (p 2341) ∨ (¬ p 2881) :=
  ElevenRUP.step123841 (p 2156) (p 2341) (p 2881) (p 4555) (p 4984) (derived105542 p h) (derived95678 p h)

theorem derived123842 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 4984) ∨ (¬ p 2427) ∨ (¬ p 2881) :=
  ElevenRUP.step123842 (p 2341) (p 2427) (p 2881) (p 4533) (p 4984) (derived105394 p h) (derived95679 p h)

theorem derived123844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3575) ∨ (¬ p 4984) ∨ (¬ p 2437) ∨ (¬ p 2220) ∨ (p 3016) ∨ (¬ p 3096) :=
  ElevenRUP.step123844 (p 2220) (p 2437) (p 3016) (p 3096) (p 3575) (p 4509) (p 4984) (derived105392 p h) (derived95683 p h)

theorem derived123845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2427) ∨ (¬ p 4984) ∨ (p 3516) :=
  ElevenRUP.step123845 (p 2427) (p 3246) (p 3516) (p 4533) (p 4984) (derived105394 p h) (derived95685 p h)

theorem derived123846 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (p 3516) ∨ (¬ p 4984) ∨ (¬ p 3246) :=
  ElevenRUP.step123846 (p 2140) (p 2870) (p 3246) (p 3516) (p 4984) (derived105364 p h) (derived95686 p h)

theorem derived123847 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 4984) ∨ (¬ p 2881) ∨ (¬ p 3872) ∨ (¬ p 2563) :=
  ElevenRUP.step123847 (p 2341) (p 2563) (p 2881) (p 3872) (p 4533) (p 4984) (derived105394 p h) (derived95688 p h)

theorem derived123853 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 2156) ∨ (p 2284) ∨ (¬ p 2166) :=
  ElevenRUP.step123853 (p 2156) (p 2166) (p 2220) (p 2284) (p 4960) (derived106209 p h) (derived95772 p h)

theorem derived123854 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 4516) ∨ (p 2284) ∨ (¬ p 3093) :=
  ElevenRUP.step123854 (p 2210) (p 2284) (p 3093) (p 4516) (p 4960) (derived106209 p h) (derived95773 p h)

theorem derived123856 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 2829) ∨ (¬ p 2608) ∨ (¬ p 3590) :=
  ElevenRUP.step123856 (p 2608) (p 2829) (p 3379) (p 3590) (p 5224) (derived105494 p h) (derived95796 p h)

theorem derived123861 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (p 2996) ∨ (¬ p 4849) ∨ (p 3516) :=
  ElevenRUP.step123861 (p 2249) (p 2449) (p 2996) (p 3516) (p 4849) (derived106513 p h) (derived95818 p h)

theorem derived123862 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (p 3527) ∨ (¬ p 3037) ∨ (¬ p 3125) ∨ (p 2459) ∨ (¬ p 2951) ∨ (p 2807) ∨ (¬ p 2992) :=
  ElevenRUP.step123862 (p 2156) (p 2249) (p 2459) (p 2807) (p 2951) (p 2992) (p 3037) (p 3125) (p 3527) (p 4330) (derived106513 p h) (derived106329 p h) (derived95859 p h)

theorem derived123870 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2307) ∨ (¬ p 3987) ∨ (p 2295) :=
  ElevenRUP.step123870 (p 2295) (p 2307) (p 2651) (p 3987) (p 4975) (derived105464 p h) (derived95896 p h)

theorem derived123871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (p 2230) ∨ (¬ p 2331) ∨ (p 2440) :=
  ElevenRUP.step123871 (p 2230) (p 2331) (p 2440) (p 2655) (p 4975) (derived105464 p h) (derived95897 p h)

theorem derived123873 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (¬ p 3543) ∨ (¬ p 4404) ∨ (¬ p 4427) ∨ (p 2396) ∨ (¬ p 3083) ∨ (p 2437) :=
  ElevenRUP.step123873 (p 2396) (p 2437) (p 3083) (p 3543) (p 4279) (p 4404) (p 4427) (p 4666) (derived105658 p h) (derived95904 p h)

theorem derived123874 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2449) ∨ (p 3516) ∨ (¬ p 3580) ∨ (¬ p 4279) :=
  ElevenRUP.step123874 (p 2449) (p 2922) (p 3516) (p 3580) (p 4279) (p 4811) (derived105633 p h) (derived95914 p h)

theorem derived123878 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4984) ∨ (p 2341) ∨ (¬ p 2881) ∨ (¬ p 2901) :=
  ElevenRUP.step123878 (p 2341) (p 2881) (p 2901) (p 2954) (p 4984) (derived106494 p h) (derived95944 p h)

theorem derived123879 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 4198) ∨ (¬ p 2187) ∨ (p 2383) :=
  ElevenRUP.step123879 (p 2187) (p 2284) (p 2383) (p 2954) (p 4198) (derived106494 p h) (derived95947 p h)

theorem derived123884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 3051) ∨ (¬ p 3483) ∨ (p 2982) ∨ (¬ p 2427) ∨ (p 2696) ∨ (¬ p 3366) ∨ (¬ p 2143) ∨ (¬ p 4368) :=
  ElevenRUP.step123884 (p 2143) (p 2427) (p 2696) (p 2829) (p 2982) (p 3051) (p 3366) (p 3483) (p 4368) (p 5052) (derived105473 p h) (derived95958 p h)

theorem derived123885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4136) ∨ (p 4782) :=
  ElevenRUP.step123885 (p 4136) (p 4782) (p 5052) (derived105473 p h) (h 36450)

theorem derived123886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3083) ∨ (¬ p 4383) ∨ (¬ p 2437) :=
  ElevenRUP.step123886 (p 2341) (p 2437) (p 3083) (p 4383) (p 5203) (derived105490 p h) (derived95959 p h)

theorem derived123887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4198) ∨ (p 2850) ∨ (¬ p 2505) ∨ (¬ p 3309) ∨ (p 2307) ∨ (¬ p 4031) :=
  ElevenRUP.step123887 (p 2307) (p 2505) (p 2850) (p 3309) (p 4031) (p 4198) (p 5217) (derived105493 p h) (derived95961 p h)

theorem derived123888 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3166) ∨ (p 3266) ∨ (¬ p 2573) ∨ (p 3256) ∨ (¬ p 4236) ∨ (¬ p 2553) ∨ (¬ p 4419) :=
  ElevenRUP.step123888 (p 2553) (p 2573) (p 3166) (p 3256) (p 3266) (p 3791) (p 4236) (p 4419) (p 4826) (derived105444 p h) (derived95975 p h)

theorem derived123890 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2241) ∨ (p 2274) ∨ (¬ p 5017) ∨ (¬ p 2187) ∨ (p 3083) ∨ (p 2727) :=
  ElevenRUP.step123890 (p 2187) (p 2241) (p 2274) (p 2307) (p 2727) (p 3083) (p 4384) (p 5017) (derived106167 p h) (derived95989 p h)

theorem derived123891 (p : Nat → Prop) (h : Inputs p) :
    (p 2972) ∨ (¬ p 5016) ∨ (¬ p 2319) ∨ (¬ p 2341) ∨ (¬ p 2396) ∨ (p 2210) ∨ (¬ p 2608) ∨ (p 2177) :=
  ElevenRUP.step123891 (p 2177) (p 2210) (p 2319) (p 2341) (p 2396) (p 2608) (p 2972) (p 3951) (p 4866) (p 5016) (derived106063 p h) (derived106536 p h) (derived96019 p h)

theorem derived123893 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4636) ∨ (p 3343) ∨ (¬ p 2396) ∨ (¬ p 2437) :=
  ElevenRUP.step123893 (p 2396) (p 2437) (p 3343) (p 4276) (p 4636) (derived105516 p h) (derived96034 p h)

theorem derived123900 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 2982) ∨ (p 3707) ∨ (¬ p 4938) ∨ (¬ p 4282) :=
  ElevenRUP.step123900 (p 2982) (p 3680) (p 3707) (p 4282) (p 4702) (p 4938) (derived106079 p h) (derived96057 p h)

theorem derived123901 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2341) ∨ (¬ p 3545) ∨ (p 3527) :=
  ElevenRUP.step123901 (p 2341) (p 2608) (p 3527) (p 3545) (p 4796) (derived105439 p h) (derived96058 p h)

theorem derived123904 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5740) ∨ (p 3136) ∨ (¬ p 2363) ∨ (¬ p 5016) ∨ (¬ p 2383) ∨ (¬ p 3366) ∨ (¬ p 3266) ∨ (¬ p 5405) ∨ (p 2696) :=
  ElevenRUP.step123904 (p 2363) (p 2383) (p 2696) (p 3136) (p 3266) (p 3366) (p 4866) (p 5016) (p 5405) (p 5740) (derived106063 p h) (derived96085 p h)

theorem derived123914 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3550) ∨ (p 4998) :=
  ElevenRUP.step123914 (p 3550) (p 4998) (p 5309) (derived105497 p h) (h 23396)

theorem derived123915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (p 2696) ∨ (p 3323) ∨ (¬ p 2341) ∨ (p 2797) ∨ (¬ p 5257) :=
  ElevenRUP.step123915 (p 2341) (p 2696) (p 2797) (p 2881) (p 3246) (p 3323) (p 4625) (p 5257) (derived106455 p h) (derived96606 p h)

theorem derived123918 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 3367) ∨ (p 3399) ∨ (¬ p 3589) :=
  ElevenRUP.step123918 (p 2598) (p 3367) (p 3399) (p 3589) (p 4793) (derived105438 p h) (derived96673 p h)

theorem derived123920 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 2651) ∨ (¬ p 2253) ∨ (¬ p 2741) ∨ (p 2727) :=
  ElevenRUP.step123920 (p 2253) (p 2651) (p 2727) (p 2741) (p 3399) (p 4793) (derived105438 p h) (derived96675 p h)

theorem derived123921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 2156) ∨ (¬ p 2753) ∨ (¬ p 3343) ∨ (¬ p 3645) ∨ (p 2274) ∨ (p 2396) ∨ (¬ p 2630) :=
  ElevenRUP.step123921 (p 2156) (p 2274) (p 2396) (p 2630) (p 2696) (p 2753) (p 3343) (p 3645) (p 4638) (p 4877) (derived105451 p h) (derived105409 p h) (derived96680 p h)

theorem derived123922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (p 3083) ∨ (¬ p 2663) ∨ (p 2396) ∨ (p 2774) ∨ (p 2122) ∨ (¬ p 3343) :=
  ElevenRUP.step123922 (p 2122) (p 2396) (p 2470) (p 2663) (p 2774) (p 3083) (p 3343) (p 4638) (p 4786) (derived106425 p h) (derived105409 p h) (derived96681 p h)

theorem derived123924 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3914) ∨ (p 3201) ∨ (¬ p 4512) ∨ (¬ p 4375) ∨ (¬ p 4435) ∨ (¬ p 4210) :=
  ElevenRUP.step123924 (p 3201) (p 3914) (p 4210) (p 4375) (p 4435) (p 4512) (p 4644) (derived105411 p h) (derived96708 p h)

theorem derived123938 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2373) ∨ (¬ p 3379) ∨ (¬ p 2406) ∨ (¬ p 3425) ∨ (¬ p 2177) ∨ (¬ p 4119) :=
  ElevenRUP.step123938 (p 2177) (p 2373) (p 2406) (p 2717) (p 3379) (p 3425) (p 4119) (p 4556) (p 4736) (derived105431 p h) (derived105399 p h) (derived97027 p h)

theorem derived123939 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3425) ∨ (¬ p 3125) ∨ (p 2459) ∨ (¬ p 2210) ∨ (¬ p 2192) :=
  ElevenRUP.step123939 (p 2192) (p 2210) (p 2459) (p 2717) (p 3125) (p 3425) (p 4330) (p 4736) (derived105431 p h) (derived106329 p h) (derived97028 p h)

theorem derived123940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2192) ∨ (p 2717) ∨ (¬ p 3425) ∨ (¬ p 2156) ∨ (¬ p 2911) ∨ (¬ p 4172) :=
  ElevenRUP.step123940 (p 2156) (p 2192) (p 2717) (p 2891) (p 2911) (p 3425) (p 4172) (p 4647) (p 4736) (derived105431 p h) (derived105412 p h) (derived97030 p h)

theorem derived123942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 2518) ∨ (¬ p 3379) ∨ (p 2459) ∨ (¬ p 3425) ∨ (p 2717) :=
  ElevenRUP.step123942 (p 2459) (p 2518) (p 2717) (p 3379) (p 3425) (p 4149) (p 4736) (p 5122) (derived105431 p h) (derived105483 p h) (derived97036 p h)

theorem derived123946 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2331) ∨ (¬ p 5558) ∨ (¬ p 3461) ∨ (¬ p 3323) ∨ (¬ p 3425) ∨ (¬ p 5123) :=
  ElevenRUP.step123946 (p 2331) (p 2717) (p 3323) (p 3425) (p 3461) (p 4786) (p 5123) (p 5558) (derived106425 p h) (derived97050 p h)

theorem derived123947 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (¬ p 5083) ∨ (¬ p 3399) ∨ (p 2717) ∨ (p 2440) ∨ (¬ p 3527) ∨ (p 2437) :=
  ElevenRUP.step123947 (p 2230) (p 2437) (p 2440) (p 2717) (p 3399) (p 3527) (p 5083) (p 5193) (derived105488 p h) (derived97051 p h)

theorem derived123950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (p 2717) ∨ (¬ p 4042) ∨ (¬ p 3425) ∨ (¬ p 5123) ∨ (¬ p 3366) ∨ (¬ p 3830) ∨ (¬ p 5568) ∨ (p 3379) :=
  ElevenRUP.step123950 (p 2717) (p 3366) (p 3379) (p 3425) (p 3707) (p 3830) (p 4042) (p 4376) (p 5123) (p 5568) (derived106320 p h) (derived97061 p h)

theorem derived123953 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 2727) ∨ (¬ p 2437) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 2241) :=
  ElevenRUP.step123953 (p 2177) (p 2241) (p 2437) (p 2717) (p 2727) (p 3425) (p 4276) (p 4736) (derived105431 p h) (derived105516 p h) (derived97072 p h)

theorem derived123955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 2717) ∨ (¬ p 5123) ∨ (¬ p 2982) ∨ (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 5558) ∨ (¬ p 2230) :=
  ElevenRUP.step123955 (p 2230) (p 2717) (p 2982) (p 3366) (p 3425) (p 3519) (p 3680) (p 4376) (p 5123) (p 5558) (derived106320 p h) (derived97077 p h)

theorem derived123958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4431) ∨ (p 2717) ∨ (¬ p 3527) ∨ (¬ p 4344) ∨ (p 2192) :=
  ElevenRUP.step123958 (p 2192) (p 2717) (p 3527) (p 4344) (p 4431) (p 4558) (derived105400 p h) (derived97094 p h)

theorem derived123960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (p 2098) ∨ (¬ p 3379) ∨ (¬ p 2459) ∨ (¬ p 2352) ∨ (p 3609) :=
  ElevenRUP.step123960 (p 2098) (p 2352) (p 2459) (p 2493) (p 3379) (p 3609) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived97103 p h)

theorem derived123962 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2098) ∨ (¬ p 2891) ∨ (¬ p 2881) ∨ (¬ p 2210) ∨ (¬ p 2363) :=
  ElevenRUP.step123962 (p 2098) (p 2210) (p 2363) (p 2881) (p 2891) (p 3609) (p 4503) (p 4736) (derived105431 p h) (derived106530 p h) (derived97109 p h)

theorem derived123965 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2098) ∨ (¬ p 2264) ∨ (¬ p 2241) ∨ (p 2996) ∨ (¬ p 2363) :=
  ElevenRUP.step123965 (p 2098) (p 2241) (p 2264) (p 2363) (p 2996) (p 3609) (p 4503) (p 4736) (derived105431 p h) (derived106530 p h) (derived97120 p h)

theorem derived123968 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 2459) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (p 3609) ∨ (¬ p 2742) ∨ (¬ p 2641) :=
  ElevenRUP.step123968 (p 2459) (p 2641) (p 2668) (p 2696) (p 2742) (p 3537) (p 3609) (p 4133) (derived105712 p h) (derived97129 p h)

theorem derived123969 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2098) ∨ (¬ p 2459) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (¬ p 2352) :=
  ElevenRUP.step123969 (p 2098) (p 2352) (p 2459) (p 2651) (p 3016) (p 3609) (p 4133) (p 4786) (derived105712 p h) (derived106425 p h) (derived97131 p h)

theorem derived123973 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 3609) ∨ (¬ p 3322) ∨ (p 2098) ∨ (¬ p 2459) ∨ (¬ p 2563) ∨ (¬ p 3125) ∨ (¬ p 4419) :=
  ElevenRUP.step123973 (p 2098) (p 2230) (p 2459) (p 2563) (p 3125) (p 3322) (p 3609) (p 4133) (p 4419) (derived105712 p h) (derived97139 p h)

theorem derived123976 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3609) ∨ (¬ p 3366) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 4041) ∨ (¬ p 3519) ∨ (¬ p 2230) ∨ (¬ p 3256) :=
  ElevenRUP.step123976 (p 2098) (p 2230) (p 2427) (p 2881) (p 3256) (p 3366) (p 3519) (p 3609) (p 4041) (p 4376) (derived106320 p h) (derived97144 p h)

theorem derived123977 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2230) ∨ (p 3609) ∨ (¬ p 2363) ∨ (¬ p 2427) ∨ (¬ p 3519) ∨ (¬ p 3366) ∨ (¬ p 2881) :=
  ElevenRUP.step123977 (p 2098) (p 2230) (p 2363) (p 2427) (p 2881) (p 3366) (p 3519) (p 3609) (p 4376) (p 4503) (derived106530 p h) (derived106320 p h) (derived97145 p h)

theorem derived123979 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2098) ∨ (¬ p 3379) ∨ (¬ p 2911) ∨ (¬ p 2363) ∨ (¬ p 2922) :=
  ElevenRUP.step123979 (p 2098) (p 2363) (p 2911) (p 2922) (p 3379) (p 3609) (p 4503) (p 4736) (derived105431 p h) (derived106530 p h) (derived97147 p h)

theorem derived123980 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (p 2608) ∨ (¬ p 2651) ∨ (¬ p 3564) ∨ (¬ p 3016) ∨ (p 3609) :=
  ElevenRUP.step123980 (p 2248) (p 2608) (p 2651) (p 3016) (p 3537) (p 3564) (p 3609) (p 4330) (derived105365 p h) (derived106329 p h) (derived97151 p h)

theorem derived123981 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3399) ∨ (p 3609) ∨ (p 3379) ∨ (¬ p 2363) ∨ (p 2098) ∨ (¬ p 3366) :=
  ElevenRUP.step123981 (p 2098) (p 2363) (p 3366) (p 3379) (p 3399) (p 3527) (p 3609) (p 4376) (p 4503) (derived106530 p h) (derived106320 p h) (derived97166 p h)

theorem derived123984 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3609) ∨ (¬ p 2363) ∨ (¬ p 2901) ∨ (¬ p 3873) ∨ (¬ p 2946) ∨ (¬ p 2881) :=
  ElevenRUP.step123984 (p 2098) (p 2248) (p 2363) (p 2881) (p 2901) (p 2946) (p 3609) (p 3873) (p 4503) (derived105365 p h) (derived106530 p h) (derived97179 p h)

theorem derived123985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3537) ∨ (p 3609) ∨ (¬ p 3246) ∨ (¬ p 2946) ∨ (p 2608) ∨ (¬ p 3950) :=
  ElevenRUP.step123985 (p 2248) (p 2608) (p 2901) (p 2946) (p 3246) (p 3537) (p 3609) (p 3950) (derived105365 p h) (derived97180 p h)

theorem derived123987 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3609) ∨ (¬ p 4774) ∨ (¬ p 2187) ∨ (¬ p 3873) ∨ (¬ p 2563) ∨ (¬ p 3256) ∨ (¬ p 2230) :=
  ElevenRUP.step123987 (p 2098) (p 2187) (p 2230) (p 2563) (p 3256) (p 3609) (p 3873) (p 4774) (p 5190) (derived105487 p h) (derived97192 p h)

theorem derived123988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2427) ∨ (p 3609) ∨ (p 3537) ∨ (¬ p 3950) ∨ (¬ p 2230) ∨ (p 2608) :=
  ElevenRUP.step123988 (p 2230) (p 2427) (p 2608) (p 3246) (p 3537) (p 3609) (p 3950) (p 5190) (derived105487 p h) (derived97194 p h)

theorem derived123989 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (p 3537) ∨ (¬ p 2651) ∨ (p 3609) ∨ (¬ p 3950) :=
  ElevenRUP.step123989 (p 2248) (p 2417) (p 2437) (p 2608) (p 2651) (p 3537) (p 3609) (p 3950) (derived105365 p h) (derived97197 p h)

theorem derived123990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 2098) ∨ (p 3266) ∨ (p 3609) ∨ (¬ p 2437) ∨ (¬ p 2651) :=
  ElevenRUP.step123990 (p 2098) (p 2437) (p 2651) (p 3266) (p 3609) (p 3868) (p 4786) (p 4826) (derived106425 p h) (derived105444 p h) (derived97199 p h)

theorem derived123992 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (p 2608) ∨ (¬ p 3950) ∨ (p 3609) ∨ (¬ p 2553) ∨ (¬ p 2396) ∨ (¬ p 2573) :=
  ElevenRUP.step123992 (p 2396) (p 2553) (p 2573) (p 2608) (p 3537) (p 3609) (p 3950) (p 5190) (derived105487 p h) (derived97204 p h)

theorem derived123993 (p : Nat → Prop) (h : Inputs p) :
    (p 3609) ∨ (p 2608) ∨ (¬ p 3125) ∨ (p 3537) ∨ (¬ p 2284) ∨ (¬ p 2946) :=
  ElevenRUP.step123993 (p 2248) (p 2284) (p 2608) (p 2946) (p 3125) (p 3537) (p 3609) (p 4330) (derived105365 p h) (derived106329 p h) (derived97206 p h)

theorem derived123995 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 2396) ∨ (¬ p 3950) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (p 3609) ∨ (p 2608) :=
  ElevenRUP.step123995 (p 2248) (p 2295) (p 2331) (p 2396) (p 2608) (p 3537) (p 3609) (p 3950) (derived105365 p h) (derived97209 p h)

theorem derived124000 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 3917) ∨ (p 3461) ∨ (p 2774) ∨ (¬ p 2651) ∨ (¬ p 2437) :=
  ElevenRUP.step124000 (p 2437) (p 2651) (p 2774) (p 3461) (p 3868) (p 3917) (p 4786) (p 4826) (derived106425 p h) (derived105444 p h) (derived97232 p h)

theorem derived124002 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4253) ∨ (¬ p 2707) ∨ (p 3323) ∨ (p 3461) ∨ (¬ p 2608) ∨ (p 2331) :=
  ElevenRUP.step124002 (p 2254) (p 2331) (p 2608) (p 2707) (p 3323) (p 3461) (p 4253) (p 4826) (derived105366 p h) (derived105444 p h) (derived97236 p h)

theorem derived124004 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 2459) ∨ (¬ p 2363) ∨ (¬ p 3564) :=
  ElevenRUP.step124004 (p 2363) (p 2459) (p 3256) (p 3564) (p 4503) (derived106530 p h) (derived97245 p h)

theorem derived124008 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (p 2598) ∨ (¬ p 3323) ∨ (¬ p 2641) ∨ (p 2528) ∨ (¬ p 2241) :=
  ElevenRUP.step124008 (p 2241) (p 2528) (p 2598) (p 2641) (p 3323) (p 3641) (p 4330) (p 4736) (derived105431 p h) (derived106329 p h) (derived97291 p h)

theorem derived124010 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 2246) ∨ (p 2598) ∨ (¬ p 2284) ∨ (¬ p 3125) ∨ (p 2528) ∨ (¬ p 2946) ∨ (¬ p 3366) :=
  ElevenRUP.step124010 (p 2246) (p 2284) (p 2528) (p 2598) (p 2744) (p 2946) (p 3125) (p 3366) (p 3641) (p 4330) (derived106503 p h) (derived106329 p h) (derived97297 p h)

theorem derived124012 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 3641) ∨ (p 2598) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (p 2528) ∨ (¬ p 2210) :=
  ElevenRUP.step124012 (p 2210) (p 2528) (p 2598) (p 2891) (p 3246) (p 3641) (p 3950) (p 4736) (derived105431 p h) (derived97303 p h)

theorem derived124015 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3422) ∨ (¬ p 2139) ∨ (p 2573) ∨ (¬ p 3156) ∨ (¬ p 3051) ∨ (¬ p 3905) ∨ (p 2901) :=
  ElevenRUP.step124015 (p 2139) (p 2573) (p 2901) (p 3051) (p 3156) (p 3422) (p 3641) (p 3905) (p 4434) (derived106144 p h) (derived97309 p h)

theorem derived124016 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3422) ∨ (¬ p 2187) ∨ (¬ p 4432) :=
  ElevenRUP.step124016 (p 2187) (p 3422) (p 3641) (p 3958) (p 4432) (derived105378 p h) (derived97311 p h)

theorem derived124017 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3759) ∨ (¬ p 2187) ∨ (¬ p 4432) ∨ (¬ p 2573) :=
  ElevenRUP.step124017 (p 2187) (p 2573) (p 3641) (p 3759) (p 3958) (p 4432) (derived105378 p h) (derived97313 p h)

theorem derived124022 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 2901) ∨ (¬ p 2922) ∨ (p 3246) ∨ (¬ p 3379) ∨ (¬ p 2911) :=
  ElevenRUP.step124022 (p 2254) (p 2901) (p 2911) (p 2922) (p 2946) (p 3246) (p 3379) (p 4666) (derived105366 p h) (derived105658 p h) (derived97331 p h)

theorem derived124025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4442) ∨ (¬ p 2774) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 2177) ∨ (¬ p 2122) ∨ (p 3399) :=
  ElevenRUP.step124025 (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 3399) (p 4442) (p 5559) (derived106189 p h) (derived97336 p h)

theorem derived124027 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 3367) ∨ (¬ p 2608) :=
  ElevenRUP.step124027 (p 2241) (p 2608) (p 3367) (p 4752) (derived105434 p h) (derived97347 p h)

theorem derived124029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 3156) ∨ (p 2946) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (p 3146) ∨ (¬ p 3950) :=
  ElevenRUP.step124029 (p 2254) (p 2608) (p 2707) (p 2946) (p 3146) (p 3156) (p 3434) (p 3950) (derived105366 p h) (derived97349 p h)

theorem derived124030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 2881) ∨ (¬ p 2608) ∨ (p 2264) ∨ (p 2807) ∨ (¬ p 2122) :=
  ElevenRUP.step124030 (p 2122) (p 2254) (p 2264) (p 2608) (p 2807) (p 2829) (p 2881) (p 4559) (derived105366 p h) (derived105701 p h) (derived97352 p h)

theorem derived124038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 2608) ∨ (¬ p 2493) ∨ (¬ p 2352) ∨ (p 3707) ∨ (p 3830) ∨ (¬ p 5119) :=
  ElevenRUP.step124038 (p 2352) (p 2493) (p 2608) (p 3707) (p 3830) (p 3979) (p 4376) (p 5119) (derived106320 p h) (derived97368 p h)

theorem derived124040 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2946) ∨ (¬ p 2246) ∨ (¬ p 2284) ∨ (p 3527) ∨ (¬ p 2187) ∨ (p 3399) :=
  ElevenRUP.step124040 (p 2187) (p 2246) (p 2284) (p 2608) (p 2744) (p 2946) (p 3399) (p 3527) (p 4133) (derived106503 p h) (derived105712 p h) (derived97371 p h)

theorem derived124044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3156) ∨ (p 3319) ∨ (¬ p 2246) ∨ (¬ p 2608) ∨ (p 3093) ∨ (¬ p 3146) :=
  ElevenRUP.step124044 (p 2246) (p 2608) (p 2744) (p 2946) (p 3093) (p 3146) (p 3156) (p 3319) (p 4604) (derived106503 p h) (derived106293 p h) (derived97381 p h)

theorem derived124050 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 2608) ∨ (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 3923) ∨ (¬ p 2881) ∨ (¬ p 3519) :=
  ElevenRUP.step124050 (p 2230) (p 2427) (p 2608) (p 2881) (p 3093) (p 3519) (p 3923) (p 4376) (p 4503) (derived106530 p h) (derived106320 p h) (derived97391 p h)

theorem derived124054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (p 2230) ∨ (p 2563) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (p 2187) :=
  ElevenRUP.step124054 (p 2187) (p 2230) (p 2563) (p 2608) (p 2707) (p 2717) (p 4503) (p 5193) (derived106530 p h) (derived105488 p h) (derived97399 p h)

theorem derived124056 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (p 2156) ∨ (¬ p 2192) ∨ (¬ p 2608) :=
  ElevenRUP.step124056 (p 2156) (p 2192) (p 2608) (p 3093) (p 4377) (derived106170 p h) (derived97400 p h)

theorem derived124057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3369) ∨ (p 2156) ∨ (¬ p 2608) ∨ (¬ p 2192) :=
  ElevenRUP.step124057 (p 2156) (p 2192) (p 2608) (p 3369) (p 4377) (derived106170 p h) (derived97401 p h)

theorem derived124058 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 2295) ∨ (p 3073) ∨ (¬ p 2246) ∨ (¬ p 2396) ∨ (¬ p 2331) ∨ (¬ p 2608) ∨ (¬ p 3950) :=
  ElevenRUP.step124058 (p 2246) (p 2295) (p 2331) (p 2396) (p 2608) (p 2744) (p 3073) (p 3449) (p 3950) (derived106503 p h) (derived97402 p h)

theorem derived124061 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3369) ∨ (¬ p 2166) ∨ (¬ p 2608) :=
  ElevenRUP.step124061 (p 2166) (p 2220) (p 2608) (p 3369) (p 4377) (derived106170 p h) (derived97405 p h)

theorem derived124063 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2891) ∨ (¬ p 2608) :=
  ElevenRUP.step124063 (p 2608) (p 2891) (p 3051) (p 4377) (derived106170 p h) (derived97408 p h)

theorem derived124065 (p : Nat → Prop) (h : Inputs p) :
    (p 3755) ∨ (¬ p 2749) ∨ (¬ p 2685) ∨ (¬ p 2608) ∨ (p 2563) ∨ (p 2187) ∨ (¬ p 3842) ∨ (p 2230) :=
  ElevenRUP.step124065 (p 2187) (p 2230) (p 2563) (p 2608) (p 2685) (p 2749) (p 3755) (p 3842) (p 5193) (derived105488 p h) (derived97412 p h)

theorem derived124071 (p : Nat → Prop) (h : Inputs p) :
    (p 3641) ∨ (¬ p 3422) ∨ (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 3366) ∨ (p 2573) ∨ (p 2241) ∨ (¬ p 3905) :=
  ElevenRUP.step124071 (p 2166) (p 2210) (p 2241) (p 2573) (p 2744) (p 3366) (p 3422) (p 3641) (p 3905) (p 4434) (derived106503 p h) (derived106144 p h) (derived97435 p h)

theorem derived124072 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (p 2437) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (p 2651) :=
  ElevenRUP.step124072 (p 2210) (p 2254) (p 2437) (p 2651) (p 2891) (p 2911) (p 3246) (p 4668) (derived105366 p h) (derived105414 p h) (derived97436 p h)

theorem derived124073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4390) ∨ (¬ p 2166) ∨ (p 2241) ∨ (¬ p 2210) ∨ (p 2122) ∨ (p 2573) ∨ (¬ p 3905) ∨ (¬ p 3366) ∨ (p 2177) :=
  ElevenRUP.step124073 (p 2122) (p 2166) (p 2177) (p 2210) (p 2241) (p 2573) (p 2744) (p 3366) (p 3905) (p 4390) (p 4902) (derived106503 p h) (derived105456 p h) (derived97437 p h)

theorem derived124074 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 2363) ∨ (p 2470) ∨ (¬ p 2210) :=
  ElevenRUP.step124074 (p 2210) (p 2363) (p 2470) (p 2528) (p 2881) (p 2891) (p 4503) (p 5193) (derived106530 p h) (derived105488 p h) (derived97444 p h)

theorem derived124075 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2210) ∨ (p 2608) :=
  ElevenRUP.step124075 (p 2210) (p 2608) (p 2839) (p 4875) (derived106227 p h) (derived97446 p h)

theorem derived124078 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (p 2122) ∨ (¬ p 3366) ∨ (p 2774) ∨ (p 2396) ∨ (¬ p 2972) ∨ (p 2241) ∨ (¬ p 4395) :=
  ElevenRUP.step124078 (p 2122) (p 2210) (p 2241) (p 2396) (p 2744) (p 2774) (p 2972) (p 3366) (p 4395) (derived106503 p h) (derived97451 p h)

theorem derived124081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2774) ∨ (¬ p 2210) ∨ (p 2819) ∨ (¬ p 3246) ∨ (p 2363) ∨ (¬ p 3950) :=
  ElevenRUP.step124081 (p 2210) (p 2363) (p 2774) (p 2819) (p 2891) (p 3246) (p 3950) (p 4736) (derived105431 p h) (derived97462 p h)

theorem derived124082 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2819) ∨ (¬ p 2881) ∨ (¬ p 2210) ∨ (¬ p 2352) ∨ (¬ p 2891) ∨ (p 2553) :=
  ElevenRUP.step124082 (p 2210) (p 2352) (p 2553) (p 2774) (p 2819) (p 2881) (p 2891) (p 4736) (derived105431 p h) (derived97469 p h)

theorem derived124088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (p 2651) ∨ (¬ p 3146) ∨ (p 3564) ∨ (¬ p 2210) ∨ (p 3016) :=
  ElevenRUP.step124088 (p 2166) (p 2210) (p 2254) (p 2651) (p 3016) (p 3146) (p 3564) (p 4604) (derived105366 p h) (derived106293 p h) (derived97481 p h)

theorem derived124090 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 3564) ∨ (¬ p 2210) ∨ (¬ p 3146) ∨ (¬ p 2166) ∨ (p 2598) :=
  ElevenRUP.step124090 (p 2166) (p 2210) (p 2598) (p 3146) (p 3422) (p 3564) (p 4604) (p 4736) (derived105431 p h) (derived106293 p h) (derived97484 p h)

theorem derived124095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (p 2573) ∨ (¬ p 2807) ∨ (p 3201) ∨ (¬ p 2264) ∨ (p 2881) ∨ (¬ p 3905) :=
  ElevenRUP.step124095 (p 2264) (p 2573) (p 2807) (p 2881) (p 3201) (p 3422) (p 3905) (p 4647) (p 4786) (derived105412 p h) (derived106425 p h) (derived97498 p h)

theorem derived124097 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2651) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (p 3201) ∨ (p 2911) ∨ (¬ p 3366) ∨ (¬ p 4236) ∨ (¬ p 3683) :=
  ElevenRUP.step124097 (p 2210) (p 2651) (p 2911) (p 3201) (p 3366) (p 3399) (p 3631) (p 3683) (p 4236) (p 4377) (p 4668) (derived105414 p h) (derived106170 p h) (derived97501 p h)

theorem derived124098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4066) ∨ (p 3201) ∨ (¬ p 4279) ∨ (p 2727) ∨ (p 2996) :=
  ElevenRUP.step124098 (p 2727) (p 2996) (p 3201) (p 4066) (p 4279) (p 4750) (derived105433 p h) (derived97503 p h)

theorem derived124100 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3399) ∨ (p 3201) ∨ (p 2210) ∨ (p 2417) ∨ (¬ p 3366) ∨ (p 2598) :=
  ElevenRUP.step124100 (p 2210) (p 2417) (p 2598) (p 3201) (p 3366) (p 3399) (p 3527) (p 4377) (p 4666) (derived105658 p h) (derived106170 p h) (derived97505 p h)

theorem derived124103 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2210) ∨ (¬ p 2192) ∨ (p 2598) ∨ (p 2911) ∨ (¬ p 2187) :=
  ElevenRUP.step124103 (p 2187) (p 2192) (p 2210) (p 2598) (p 2911) (p 3201) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived97510 p h)

theorem derived124104 (p : Nat → Prop) (h : Inputs p) :
    (p 2996) ∨ (¬ p 2449) ∨ (p 3201) ∨ (p 2911) ∨ (p 2598) ∨ (¬ p 2241) :=
  ElevenRUP.step124104 (p 2241) (p 2449) (p 2598) (p 2911) (p 2996) (p 3201) (p 4668) (p 4736) (derived105431 p h) (derived105414 p h) (derived97514 p h)

theorem derived124105 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2417) ∨ (p 2598) ∨ (¬ p 2241) ∨ (¬ p 3323) ∨ (¬ p 2641) :=
  ElevenRUP.step124105 (p 2241) (p 2417) (p 2598) (p 2641) (p 3201) (p 3323) (p 4621) (p 4736) (derived105431 p h) (derived105407 p h) (derived97517 p h)

theorem derived124107 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2449) ∨ (p 2417) ∨ (¬ p 3580) :=
  ElevenRUP.step124107 (p 2417) (p 2449) (p 3201) (p 3580) (p 4750) (derived105433 p h) (derived97521 p h)

theorem derived124109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3399) ∨ (¬ p 3571) ∨ (¬ p 3246) ∨ (p 3379) ∨ (p 2774) ∨ (p 2122) ∨ (¬ p 3366) ∨ (p 2177) :=
  ElevenRUP.step124109 (p 2122) (p 2177) (p 2774) (p 3246) (p 3366) (p 3379) (p 3399) (p 3571) (p 4376) (p 4668) (derived105414 p h) (derived106320 p h) (derived97541 p h)

theorem derived124112 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 3399) ∨ (¬ p 3037) ∨ (p 2241) :=
  ElevenRUP.step124112 (p 2241) (p 2685) (p 2751) (p 3037) (p 3399) (derived106343 p h) (derived97546 p h)

theorem derived124115 (p : Nat → Prop) (h : Inputs p) :
    (p 2563) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2274) ∨ (p 2230) ∨ (p 2264) :=
  ElevenRUP.step124115 (p 2230) (p 2264) (p 2274) (p 2563) (p 3399) (p 3527) (p 5193) (derived105488 p h) (derived97564 p h)

theorem derived124119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (p 2241) ∨ (¬ p 3905) ∨ (p 2573) ∨ (p 2363) ∨ (¬ p 3366) ∨ (¬ p 3950) ∨ (p 2352) :=
  ElevenRUP.step124119 (p 2241) (p 2352) (p 2363) (p 2573) (p 2744) (p 3366) (p 3399) (p 3631) (p 3905) (p 3950) (derived106503 p h) (derived97573 p h)

theorem derived124121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5160) ∨ (¬ p 3527) ∨ (¬ p 3941) ∨ (p 2598) ∨ (¬ p 3399) ∨ (p 3276) ∨ (¬ p 5119) :=
  ElevenRUP.step124121 (p 2598) (p 3276) (p 3399) (p 3527) (p 3941) (p 4736) (p 5119) (p 5160) (derived105431 p h) (derived97581 p h)

theorem derived124125 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 3527) ∨ (p 2982) ∨ (¬ p 3399) ∨ (p 2598) ∨ (¬ p 5059) ∨ (¬ p 2459) :=
  ElevenRUP.step124125 (p 2459) (p 2598) (p 2850) (p 2982) (p 3399) (p 3527) (p 4736) (p 5059) (derived105431 p h) (derived97587 p h)

theorem derived124126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (¬ p 3399) ∨ (p 2598) ∨ (p 3564) ∨ (¬ p 2459) ∨ (p 3422) :=
  ElevenRUP.step124126 (p 2459) (p 2598) (p 3399) (p 3422) (p 3527) (p 3564) (p 4604) (p 4736) (derived105431 p h) (derived106293 p h) (derived97590 p h)

theorem derived124128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (p 2608) ∨ (¬ p 2187) ∨ (p 3125) ∨ (¬ p 3923) ∨ (¬ p 4870) :=
  ElevenRUP.step124128 (p 2187) (p 2608) (p 3125) (p 3399) (p 3631) (p 3923) (p 4625) (p 4870) (derived106455 p h) (derived97594 p h)

theorem derived124132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (p 2220) ∨ (¬ p 2241) ∨ (p 3266) ∨ (p 3146) ∨ (p 2996) :=
  ElevenRUP.step124132 (p 2220) (p 2241) (p 2996) (p 3146) (p 3266) (p 3931) (p 4826) (derived105444 p h) (derived97616 p h)

theorem derived124134 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 2753) ∨ (¬ p 2132) ∨ (¬ p 3125) ∨ (p 3073) ∨ (¬ p 2860) ∨ (¬ p 2241) :=
  ElevenRUP.step124134 (p 2132) (p 2241) (p 2750) (p 2753) (p 2860) (p 3073) (p 3125) (p 3449) (p 4330) (derived106345 p h) (derived106329 p h) (derived97624 p h)

theorem derived124136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3369) ∨ (¬ p 3371) ∨ (p 2156) ∨ (¬ p 2192) ∨ (¬ p 2241) :=
  ElevenRUP.step124136 (p 2156) (p 2192) (p 2241) (p 2750) (p 3369) (p 3371) (derived106345 p h) (derived97631 p h)

theorem derived124137 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 3564) ∨ (p 2598) ∨ (¬ p 3189) ∨ (¬ p 2241) ∨ (¬ p 3256) :=
  ElevenRUP.step124137 (p 2241) (p 2598) (p 3189) (p 3256) (p 3422) (p 3564) (p 4604) (p 4736) (derived105431 p h) (derived106293 p h) (derived97634 p h)

theorem derived124138 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (p 3422) ∨ (¬ p 2641) ∨ (¬ p 2241) ∨ (p 2352) ∨ (¬ p 2295) :=
  ElevenRUP.step124138 (p 2241) (p 2295) (p 2352) (p 2598) (p 2641) (p 3422) (p 4736) (derived105431 p h) (derived97636 p h)

theorem derived124141 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2996) ∨ (¬ p 2241) ∨ (p 2598) ∨ (¬ p 2449) ∨ (p 2982) :=
  ElevenRUP.step124141 (p 2241) (p 2449) (p 2598) (p 2850) (p 2982) (p 2996) (p 3951) (p 4736) (derived105431 p h) (derived106536 p h) (derived97640 p h)

theorem derived124145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5160) ∨ (¬ p 2166) ∨ (¬ p 2210) ∨ (p 2598) ∨ (p 3276) ∨ (¬ p 5119) :=
  ElevenRUP.step124145 (p 2166) (p 2210) (p 2598) (p 3276) (p 3969) (p 4736) (p 5119) (p 5160) (derived105431 p h) (derived97655 p h)

theorem derived124146 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 2166) ∨ (¬ p 4365) ∨ (p 3156) :=
  ElevenRUP.step124146 (p 2166) (p 2751) (p 3136) (p 3156) (p 4365) (derived106343 p h) (derived97657 p h)

theorem derived124148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 3412) ∨ (p 2641) ∨ (p 3461) ∨ (p 3654) ∨ (¬ p 2667) ∨ (¬ p 2166) ∨ (¬ p 2946) ∨ (¬ p 5119) :=
  ElevenRUP.step124148 (p 2166) (p 2255) (p 2641) (p 2667) (p 2946) (p 3412) (p 3461) (p 3654) (p 3969) (p 5119) (derived105367 p h) (derived97667 p h)

theorem derived124149 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2437) ∨ (¬ p 3146) ∨ (p 3343) ∨ (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 4697) :=
  ElevenRUP.step124149 (p 2166) (p 2210) (p 2437) (p 3146) (p 3343) (p 3389) (p 4697) (p 5193) (derived105488 p h) (derived97670 p h)

theorem derived124153 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (¬ p 3582) ∨ (p 2982) ∨ (¬ p 3105) :=
  ElevenRUP.step124153 (p 2406) (p 2982) (p 3105) (p 3582) (p 5214) (derived105492 p h) (derived97703 p h)

theorem derived124154 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (¬ p 2230) ∨ (p 2241) ∨ (¬ p 4257) ∨ (¬ p 4079) :=
  ElevenRUP.step124154 (p 2230) (p 2241) (p 2406) (p 2744) (p 4079) (p 4257) (derived106503 p h) (derived97707 p h)

theorem derived124155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2829) ∨ (¬ p 3759) ∨ (¬ p 4257) ∨ (p 2406) :=
  ElevenRUP.step124155 (p 2230) (p 2406) (p 2829) (p 3759) (p 4257) (p 5224) (derived105494 p h) (derived97708 p h)

theorem derived124156 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 3399) ∨ (¬ p 2230) ∨ (¬ p 4079) ∨ (¬ p 4257) :=
  ElevenRUP.step124156 (p 2230) (p 2406) (p 3399) (p 4079) (p 4257) (p 4793) (derived105438 p h) (derived97709 p h)

theorem derived124158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 2972) ∨ (¬ p 2696) ∨ (¬ p 3425) ∨ (¬ p 3948) ∨ (p 3434) ∨ (¬ p 3590) ∨ (p 3461) :=
  ElevenRUP.step124158 (p 2696) (p 2972) (p 3425) (p 3434) (p 3461) (p 3590) (p 3680) (p 3948) (p 4621) (p 4749) (derived105432 p h) (derived105407 p h) (derived97722 p h)

theorem derived124159 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 3680) ∨ (¬ p 2210) ∨ (p 2331) ∨ (p 2295) ∨ (¬ p 2972) :=
  ElevenRUP.step124159 (p 2210) (p 2254) (p 2295) (p 2331) (p 2972) (p 3680) (p 4260) (p 4831) (derived105366 p h) (derived105445 p h) (derived97726 p h)

theorem derived124166 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 2972) ∨ (p 3115) ∨ (¬ p 4365) :=
  ElevenRUP.step124166 (p 2751) (p 2972) (p 3115) (p 3136) (p 4365) (derived106343 p h) (derived97752 p h)

theorem derived124167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 3146) ∨ (¬ p 3032) ∨ (p 2264) ∨ (¬ p 4443) :=
  ElevenRUP.step124167 (p 2264) (p 3032) (p 3146) (p 3631) (p 4443) (p 4902) (derived105456 p h) (derived97766 p h)

theorem derived124169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2927) ∨ (p 4914) :=
  ElevenRUP.step124169 (p 2927) (p 4647) (p 4914) (derived105412 p h) (h 24424)

theorem derived124175 (p : Nat → Prop) (h : Inputs p) :
    (p 3537) ∨ (¬ p 3156) ∨ (¬ p 2992) ∨ (p 3609) ∨ (¬ p 2459) ∨ (¬ p 3367) ∨ (¬ p 2241) :=
  ElevenRUP.step124175 (p 2241) (p 2459) (p 2992) (p 3156) (p 3367) (p 3537) (p 3609) (p 4902) (derived105456 p h) (derived97787 p h)

theorem derived124178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3953) ∨ (¬ p 3483) ∨ (¬ p 3367) ∨ (¬ p 4426) ∨ (p 3319) :=
  ElevenRUP.step124178 (p 3319) (p 3367) (p 3483) (p 3953) (p 4426) (p 4752) (derived105434 p h) (derived97798 p h)

theorem derived124179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (p 2241) ∨ (p 2396) ∨ (p 2774) ∨ (p 2122) ∨ (¬ p 3073) ∨ (¬ p 3366) :=
  ElevenRUP.step124179 (p 2122) (p 2241) (p 2396) (p 2744) (p 2774) (p 3073) (p 3366) (p 3449) (p 4669) (derived106503 p h) (derived105415 p h) (derived97821 p h)

theorem derived124181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 2786) ∨ (¬ p 2307) ∨ (p 2946) ∨ (p 2122) ∨ (p 3146) ∨ (p 3156) :=
  ElevenRUP.step124181 (p 2122) (p 2307) (p 2786) (p 2946) (p 3146) (p 3156) (p 3483) (p 4330) (p 4789) (derived106329 p h) (derived105646 p h) (derived97826 p h)

theorem derived124183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2319) ∨ (¬ p 2341) ∨ (p 2122) ∨ (p 2177) :=
  ElevenRUP.step124183 (p 2122) (p 2177) (p 2319) (p 2341) (p 2788) (derived105375 p h) (derived97835 p h)

theorem derived124184 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2819) ∨ (¬ p 2295) ∨ (p 2383) :=
  ElevenRUP.step124184 (p 2122) (p 2295) (p 2383) (p 2819) (p 4581) (derived105405 p h) (derived97839 p h)

theorem derived124185 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2341) ∨ (p 2122) ∨ (¬ p 3550) :=
  ElevenRUP.step124185 (p 2122) (p 2315) (p 2341) (p 2819) (p 3550) (derived105368 p h) (derived97845 p h)

theorem derived124188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 2992) ∨ (p 2122) ∨ (¬ p 2241) ∨ (p 2396) ∨ (p 2774) ∨ (¬ p 4395) :=
  ElevenRUP.step124188 (p 2122) (p 2241) (p 2396) (p 2774) (p 2992) (p 3115) (p 4395) (p 4736) (derived105431 p h) (derived97851 p h)

theorem derived124189 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (p 2406) ∨ (p 2774) ∨ (¬ p 2230) ∨ (p 2177) ∨ (¬ p 4079) ∨ (p 2122) :=
  ElevenRUP.step124189 (p 2122) (p 2177) (p 2230) (p 2406) (p 2518) (p 2774) (p 4079) (p 4420) (p 4736) (derived105431 p h) (derived105707 p h) (derived97852 p h)

theorem derived124193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 4260) ∨ (p 2122) ∨ (¬ p 2946) ∨ (p 2774) ∨ (¬ p 3115) :=
  ElevenRUP.step124193 (p 2122) (p 2774) (p 2946) (p 3115) (p 3680) (p 4260) (p 4786) (p 4831) (derived106425 p h) (derived105445 p h) (derived97863 p h)

theorem derived124195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 2651) ∨ (p 2122) ∨ (¬ p 2440) ∨ (¬ p 2786) ∨ (p 2373) ∨ (¬ p 2307) :=
  ElevenRUP.step124195 (p 2122) (p 2307) (p 2373) (p 2440) (p 2651) (p 2786) (p 2819) (p 4134) (p 4789) (derived105379 p h) (derived105646 p h) (derived97867 p h)

theorem derived124196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3366) ∨ (¬ p 2246) ∨ (p 2396) ∨ (¬ p 3083) ∨ (p 2774) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (p 2122) :=
  ElevenRUP.step124196 (p 2122) (p 2246) (p 2396) (p 2528) (p 2651) (p 2744) (p 2774) (p 3083) (p 3366) (p 4669) (derived106503 p h) (derived105415 p h) (derived97868 p h)

theorem derived124198 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 3680) ∨ (p 2774) ∨ (¬ p 4260) ∨ (¬ p 4419) :=
  ElevenRUP.step124198 (p 2122) (p 2230) (p 2774) (p 2982) (p 3680) (p 4260) (p 4419) (p 4831) (derived105445 p h) (derived97877 p h)

theorem derived124200 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2122) ∨ (¬ p 2881) ∨ (p 2396) ∨ (¬ p 2946) ∨ (¬ p 2901) :=
  ElevenRUP.step124200 (p 2122) (p 2396) (p 2774) (p 2881) (p 2901) (p 2946) (p 4666) (p 4786) (derived105658 p h) (derived106425 p h) (derived97879 p h)

theorem derived124201 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3367) ∨ (p 2396) ∨ (p 2122) ∨ (¬ p 3759) ∨ (¬ p 2528) ∨ (¬ p 2470) :=
  ElevenRUP.step124201 (p 2122) (p 2396) (p 2470) (p 2528) (p 2774) (p 3367) (p 3759) (p 4669) (derived105415 p h) (derived97880 p h)

theorem derived124203 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 2166) ∨ (¬ p 3146) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 2210) :=
  ElevenRUP.step124203 (p 2122) (p 2166) (p 2210) (p 2396) (p 2774) (p 3146) (p 4669) (p 4736) (derived105431 p h) (derived105415 p h) (derived97883 p h)

theorem derived124204 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (p 2122) ∨ (p 2396) ∨ (¬ p 2891) ∨ (¬ p 2881) ∨ (¬ p 2210) :=
  ElevenRUP.step124204 (p 2122) (p 2210) (p 2396) (p 2774) (p 2881) (p 2891) (p 4666) (p 4736) (derived105431 p h) (derived105658 p h) (derived97884 p h)

theorem derived124205 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3189) ∨ (p 2122) ∨ (¬ p 2241) ∨ (p 2396) ∨ (¬ p 3256) :=
  ElevenRUP.step124205 (p 2122) (p 2241) (p 2396) (p 2774) (p 3189) (p 3256) (p 4669) (p 4736) (derived105431 p h) (derived105415 p h) (derived97885 p h)

theorem derived124207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (¬ p 3367) ∨ (¬ p 2946) ∨ (p 2177) ∨ (¬ p 3759) ∨ (¬ p 3156) ∨ (p 2122) ∨ (p 2774) :=
  ElevenRUP.step124207 (p 2122) (p 2177) (p 2655) (p 2774) (p 2946) (p 3156) (p 3367) (p 3759) (p 4902) (derived105456 p h) (derived97893 p h)

theorem derived124209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2482) ∨ (p 2331) ∨ (¬ p 2088) ∨ (¬ p 2656) ∨ (p 2528) ∨ (p 2177) ∨ (p 2122) ∨ (¬ p 4328) ∨ (¬ p 2630) :=
  ElevenRUP.step124209 (p 2088) (p 2122) (p 2177) (p 2331) (p 2482) (p 2528) (p 2630) (p 2656) (p 4328) (p 4420) (derived105707 p h) (derived97896 p h)

theorem derived124210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3920) ∨ (p 2396) ∨ (p 2122) :=
  ElevenRUP.step124210 (p 2122) (p 2396) (p 2417) (p 3920) (p 5222) (derived105793 p h) (derived97900 p h)

theorem derived124215 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2220) ∨ (¬ p 4390) ∨ (¬ p 3115) ∨ (p 2122) ∨ (¬ p 3370) ∨ (¬ p 3905) ∨ (¬ p 3366) ∨ (p 3156) ∨ (p 2396) ∨ (¬ p 4395) :=
  ElevenRUP.step124215 (p 2122) (p 2220) (p 2396) (p 2573) (p 3115) (p 3156) (p 3366) (p 3370) (p 3905) (p 4377) (p 4390) (p 4395) (derived106170 p h) (derived97909 p h)

theorem derived124217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 2284) ∨ (p 3051) ∨ (¬ p 2860) :=
  ElevenRUP.step124217 (p 2140) (p 2284) (p 2860) (p 2901) (p 3051) (derived105364 p h) (derived97934 p h)

theorem derived124218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (p 2528) ∨ (¬ p 2881) ∨ (¬ p 2363) ∨ (¬ p 2901) ∨ (p 2470) ∨ (¬ p 3905) :=
  ElevenRUP.step124218 (p 2363) (p 2470) (p 2528) (p 2881) (p 2901) (p 2946) (p 3905) (p 4503) (p 4786) (derived106530 p h) (derived106425 p h) (derived97937 p h)

theorem derived124220 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2946) ∨ (¬ p 2901) ∨ (¬ p 3745) :=
  ElevenRUP.step124220 (p 2331) (p 2901) (p 2946) (p 3745) (p 4558) (derived105400 p h) (derived97943 p h)

theorem derived124221 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3873) ∨ (¬ p 2901) ∨ (p 2284) ∨ (p 2598) ∨ (¬ p 2156) ∨ (¬ p 3367) ∨ (¬ p 4521) :=
  ElevenRUP.step124221 (p 2156) (p 2284) (p 2598) (p 2707) (p 2901) (p 3367) (p 3873) (p 4521) (p 4898) (derived105455 p h) (derived97951 p h)

theorem derived124223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 4153) ∨ (p 3323) ∨ (¬ p 3125) :=
  ElevenRUP.step124223 (p 2901) (p 3125) (p 3323) (p 4153) (p 4558) (derived105400 p h) (derived97962 p h)

theorem derived124224 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4153) ∨ (¬ p 3743) ∨ (¬ p 2383) ∨ (p 2668) ∨ (¬ p 2901) :=
  ElevenRUP.step124224 (p 2383) (p 2668) (p 2901) (p 3743) (p 4153) (p 4558) (derived105400 p h) (derived97963 p h)

theorem derived124226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 4386) ∨ (p 2449) :=
  ElevenRUP.step124226 (p 2427) (p 2449) (p 3246) (p 4386) (p 4702) (derived106079 p h) (derived97972 p h)

theorem derived124227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3699) ∨ (p 2807) ∨ (¬ p 2427) :=
  ElevenRUP.step124227 (p 2427) (p 2807) (p 2946) (p 3699) (p 4702) (derived106079 p h) (derived97974 p h)

theorem derived124228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 2563) ∨ (p 2295) ∨ (¬ p 4140) :=
  ElevenRUP.step124228 (p 2295) (p 2427) (p 2563) (p 4140) (p 4564) (derived105401 p h) (derived97976 p h)

theorem derived124232 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3399) ∨ (¬ p 2427) ∨ (¬ p 2264) ∨ (¬ p 2156) ∨ (p 2563) ∨ (¬ p 4521) :=
  ElevenRUP.step124232 (p 2156) (p 2264) (p 2427) (p 2563) (p 3399) (p 3527) (p 4362) (p 4521) (derived106173 p h) (derived97991 p h)

theorem derived124233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (p 2241) ∨ (p 2449) ∨ (¬ p 2881) ∨ (¬ p 2230) ∨ (¬ p 2427) :=
  ElevenRUP.step124233 (p 2230) (p 2241) (p 2427) (p 2449) (p 2881) (p 2996) (p 4666) (p 5190) (derived105658 p h) (derived105487 p h) (derived97999 p h)

theorem derived124235 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 2437) ∨ (¬ p 2264) ∨ (p 2177) ∨ (¬ p 2440) :=
  ElevenRUP.step124235 (p 2177) (p 2264) (p 2437) (p 2440) (p 3016) (p 4711) (derived105655 p h) (derived98009 p h)

theorem derived124236 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2437) ∨ (¬ p 2727) :=
  ElevenRUP.step124236 (p 2249) (p 2437) (p 2727) (p 3389) (derived106513 p h) (derived98011 p h)

theorem derived124238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 4194) ∨ (¬ p 3660) ∨ (¬ p 3564) ∨ (p 3323) :=
  ElevenRUP.step124238 (p 2437) (p 3323) (p 3564) (p 3660) (p 4194) (p 4646) (derived105534 p h) (derived98017 p h)

theorem derived124239 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 2753) ∨ (p 2187) ∨ (¬ p 3950) ∨ (p 2363) ∨ (¬ p 2651) ∨ (¬ p 2437) ∨ (¬ p 3645) ∨ (¬ p 2417) ∨ (p 2156) :=
  ElevenRUP.step124239 (p 2156) (p 2187) (p 2363) (p 2417) (p 2437) (p 2651) (p 2753) (p 3645) (p 3950) (p 4117) (p 4877) (derived105451 p h) (derived98018 p h)

theorem derived124240 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 3389) ∨ (¬ p 2230) ∨ (¬ p 2437) :=
  ElevenRUP.step124240 (p 2230) (p 2437) (p 2850) (p 3389) (p 4750) (derived105433 p h) (derived98022 p h)

theorem derived124241 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2230) ∨ (p 2406) ∨ (¬ p 2437) :=
  ElevenRUP.step124241 (p 2230) (p 2406) (p 2437) (p 3389) (p 4811) (derived105633 p h) (derived98026 p h)

theorem derived124243 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3879) ∨ (¬ p 2437) ∨ (¬ p 2651) :=
  ElevenRUP.step124243 (p 2437) (p 2651) (p 2946) (p 3879) (p 4646) (derived105534 p h) (derived98032 p h)

theorem derived124244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 3575) ∨ (¬ p 4383) ∨ (p 3083) ∨ (¬ p 2437) :=
  ElevenRUP.step124244 (p 2437) (p 3083) (p 3516) (p 3575) (p 4383) (p 4668) (derived105414 p h) (derived98034 p h)

theorem derived124245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 2437) ∨ (p 2608) ∨ (p 3389) ∨ (¬ p 3093) ∨ (¬ p 3461) ∨ (p 3083) ∨ (¬ p 2655) ∨ (¬ p 2252) :=
  ElevenRUP.step124245 (p 2252) (p 2437) (p 2608) (p 2655) (p 2750) (p 3083) (p 3093) (p 3319) (p 3389) (p 3461) (derived106345 p h) (derived98036 p h)

theorem derived124246 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2655) ∨ (¬ p 2331) ∨ (¬ p 2437) :=
  ElevenRUP.step124246 (p 2331) (p 2437) (p 2655) (p 3389) (p 4975) (derived105464 p h) (derived98041 p h)

theorem derived124248 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3434) ∨ (p 2608) ∨ (¬ p 2911) ∨ (¬ p 2437) ∨ (¬ p 2651) :=
  ElevenRUP.step124248 (p 2248) (p 2437) (p 2608) (p 2651) (p 2707) (p 2911) (p 3434) (p 4666) (derived105365 p h) (derived105658 p h) (derived98051 p h)

theorem derived124251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2578) ∨ (¬ p 2383) ∨ (¬ p 2437) ∨ (p 2668) ∨ (¬ p 4194) :=
  ElevenRUP.step124251 (p 2383) (p 2437) (p 2578) (p 2668) (p 4194) (p 4711) (derived105655 p h) (derived98063 p h)

theorem derived124254 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 3879) ∨ (¬ p 2437) ∨ (¬ p 2727) :=
  ElevenRUP.step124254 (p 2437) (p 2727) (p 2992) (p 3879) (p 4646) (derived105534 p h) (derived98069 p h)

theorem derived124257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2926) ∨ (p 3527) ∨ (¬ p 2911) ∨ (¬ p 2437) :=
  ElevenRUP.step124257 (p 2437) (p 2911) (p 2926) (p 3527) (p 4811) (derived105633 p h) (derived98075 p h)

theorem derived124258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 2417) ∨ (¬ p 3917) ∨ (¬ p 2246) ∨ (¬ p 2778) ∨ (¬ p 2437) ∨ (p 2383) ∨ (¬ p 2651) ∨ (¬ p 3366) :=
  ElevenRUP.step124258 (p 2246) (p 2383) (p 2417) (p 2437) (p 2651) (p 2744) (p 2778) (p 2819) (p 3366) (p 3917) (p 4625) (derived106503 p h) (derived106455 p h) (derived98076 p h)

theorem derived124261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2926) ∨ (¬ p 2417) ∨ (p 3631) ∨ (¬ p 2437) :=
  ElevenRUP.step124261 (p 2417) (p 2437) (p 2926) (p 3631) (p 4811) (derived105633 p h) (derived98079 p h)

theorem derived124263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 2187) ∨ (¬ p 4198) ∨ (p 3125) ∨ (¬ p 2417) ∨ (p 2383) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 2145) :=
  ElevenRUP.step124263 (p 2145) (p 2187) (p 2383) (p 2417) (p 2437) (p 2651) (p 3125) (p 4117) (p 4198) (p 4625) (derived106455 p h) (derived98083 p h)

theorem derived124266 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2440) ∨ (¬ p 2331) :=
  ElevenRUP.step124266 (p 2331) (p 2440) (p 2651) (p 4717) (derived105424 p h) (derived98102 p h)

theorem derived124268 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (p 2651) ∨ (¬ p 2807) ∨ (¬ p 2727) :=
  ElevenRUP.step124268 (p 2651) (p 2685) (p 2727) (p 2751) (p 2807) (derived106343 p h) (derived98111 p h)

theorem derived124269 (p : Nat → Prop) (h : Inputs p) :
    (p 2312) ∨ (p 2651) ∨ (p 2295) :=
  ElevenRUP.step124269 (p 2295) (p 2312) (p 2651) (p 4975) (derived105464 p h) (derived98112 p h)

theorem derived124271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2685) ∨ (¬ p 4236) ∨ (¬ p 2881) ∨ (p 2177) ∨ (¬ p 3051) ∨ (p 2651) ∨ (¬ p 2139) :=
  ElevenRUP.step124271 (p 2139) (p 2177) (p 2630) (p 2651) (p 2685) (p 2881) (p 3051) (p 4236) (p 4361) (derived105382 p h) (derived98114 p h)

theorem derived124272 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2651) ∨ (¬ p 4104) ∨ (¬ p 4067) ∨ (p 2264) :=
  ElevenRUP.step124272 (p 2264) (p 2341) (p 2651) (p 4067) (p 4104) (p 4975) (derived105464 p h) (derived98115 p h)

theorem derived124274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 3599) ∨ (p 2761) ∨ (p 2528) ∨ (p 2651) ∨ (p 3083) ∨ (¬ p 2252) ∨ (¬ p 3950) :=
  ElevenRUP.step124274 (p 2252) (p 2528) (p 2651) (p 2750) (p 2761) (p 3083) (p 3599) (p 3670) (p 3950) (derived106345 p h) (derived98121 p h)

theorem derived124275 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2651) ∨ (¬ p 3125) ∨ (¬ p 2210) ∨ (p 2528) ∨ (¬ p 2192) :=
  ElevenRUP.step124275 (p 2192) (p 2210) (p 2254) (p 2528) (p 2651) (p 3083) (p 3125) (p 4330) (derived105366 p h) (derived106329 p h) (derived98122 p h)

theorem derived124276 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2210) ∨ (¬ p 4236) ∨ (¬ p 3399) ∨ (¬ p 3950) ∨ (p 2528) ∨ (p 3083) ∨ (¬ p 3631) ∨ (¬ p 3366) :=
  ElevenRUP.step124276 (p 2210) (p 2528) (p 2651) (p 3083) (p 3366) (p 3399) (p 3631) (p 3950) (p 4236) (p 4377) (derived106170 p h) (derived98123 p h)

theorem derived124278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3366) ∨ (p 2651) ∨ (¬ p 3683) ∨ (p 2881) ∨ (p 3564) ∨ (¬ p 2341) ∨ (¬ p 4988) ∨ (p 3422) ∨ (¬ p 3370) ∨ (¬ p 3246) ∨ (¬ p 4236) :=
  ElevenRUP.step124278 (p 2341) (p 2651) (p 2881) (p 3246) (p 3366) (p 3370) (p 3422) (p 3564) (p 3683) (p 4236) (p 4377) (p 4625) (p 4988) (derived106170 p h) (derived106455 p h) (derived98138 p h)

theorem derived124282 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2210) ∨ (¬ p 3399) ∨ (¬ p 3571) ∨ (p 2417) ∨ (¬ p 2881) ∨ (p 2437) ∨ (¬ p 4448) ∨ (¬ p 2252) :=
  ElevenRUP.step124282 (p 2210) (p 2252) (p 2417) (p 2437) (p 2651) (p 2881) (p 3399) (p 3571) (p 4448) (p 4666) (derived105658 p h) (derived98152 p h)

theorem derived124283 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2437) ∨ (¬ p 2891) ∨ (¬ p 2210) ∨ (¬ p 2881) ∨ (p 2417) :=
  ElevenRUP.step124283 (p 2210) (p 2254) (p 2417) (p 2437) (p 2651) (p 2881) (p 2891) (p 4666) (derived105366 p h) (derived105658 p h) (derived98153 p h)

theorem derived124284 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2493) ∨ (¬ p 2331) ∨ (¬ p 3984) :=
  ElevenRUP.step124284 (p 2331) (p 2493) (p 2651) (p 3984) (p 4811) (derived105633 p h) (derived98155 p h)

theorem derived124286 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 3516) ∨ (p 2449) ∨ (¬ p 4104) ∨ (¬ p 4067) :=
  ElevenRUP.step124286 (p 2449) (p 2651) (p 3516) (p 4067) (p 4104) (p 4975) (derived105464 p h) (derived98171 p h)

theorem derived124289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 2166) ∨ (p 2651) ∨ (¬ p 5119) ∨ (p 3343) ∨ (p 3276) ∨ (¬ p 2210) :=
  ElevenRUP.step124289 (p 2166) (p 2210) (p 2254) (p 2651) (p 3276) (p 3343) (p 3969) (p 5119) (derived105366 p h) (derived98186 p h)

theorem derived124294 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (¬ p 3366) ∨ (¬ p 2156) ∨ (¬ p 3343) ∨ (¬ p 3370) ∨ (¬ p 2363) ∨ (p 3016) ∨ (¬ p 2187) ∨ (¬ p 5160) :=
  ElevenRUP.step124294 (p 2156) (p 2187) (p 2363) (p 2598) (p 3016) (p 3343) (p 3366) (p 3370) (p 4377) (p 5160) (derived106170 p h) (derived98210 p h)

theorem derived124295 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 4153) ∨ (¬ p 3125) ∨ (p 3323) :=
  ElevenRUP.step124295 (p 2156) (p 2960) (p 3125) (p 3323) (p 4153) (derived105377 p h) (derived98211 p h)

theorem derived124298 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2951) ∨ (¬ p 2881) ∨ (p 2396) ∨ (¬ p 3051) ∨ (¬ p 2992) ∨ (p 3309) ∨ (¬ p 3922) :=
  ElevenRUP.step124298 (p 2249) (p 2331) (p 2396) (p 2881) (p 2951) (p 2992) (p 3051) (p 3309) (p 3922) (p 4666) (derived105658 p h) (derived106513 p h) (derived98216 p h)

theorem derived124302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3051) ∨ (p 2264) :=
  ElevenRUP.step124302 (p 2264) (p 2881) (p 2960) (p 3051) (derived105377 p h) (derived98222 p h)

theorem derived124304 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 3519) ∨ (¬ p 3051) ∨ (¬ p 4399) ∨ (p 2363) ∨ (¬ p 4450) ∨ (¬ p 3366) ∨ (¬ p 2982) ∨ (p 2427) ∨ (¬ p 4236) ∨ (p 2668) :=
  ElevenRUP.step124304 (p 2331) (p 2363) (p 2427) (p 2668) (p 2982) (p 3051) (p 3366) (p 3519) (p 4236) (p 4376) (p 4399) (p 4450) (derived106320 p h) (derived98225 p h)

theorem derived124306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4386) ∨ (p 2449) ∨ (¬ p 3246) :=
  ElevenRUP.step124306 (p 2449) (p 2960) (p 3051) (p 3246) (p 4386) (derived105377 p h) (derived98237 p h)

theorem derived124308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (¬ p 4140) ∨ (p 2295) :=
  ElevenRUP.step124308 (p 2156) (p 2295) (p 3051) (p 4140) (p 4564) (derived105401 p h) (derived98248 p h)

theorem derived124309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2553) ∨ (¬ p 2274) ∨ (¬ p 2590) :=
  ElevenRUP.step124309 (p 2274) (p 2284) (p 2553) (p 2590) (p 4705) (derived106238 p h) (derived98283 p h)

theorem derived124310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 3550) ∨ (p 2881) ∨ (p 2553) :=
  ElevenRUP.step124310 (p 2352) (p 2553) (p 2881) (p 3550) (p 4556) (derived105399 p h) (derived98287 p h)

theorem derived124311 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) ∨ (¬ p 2352) ∨ (¬ p 3550) ∨ (p 2396) :=
  ElevenRUP.step124311 (p 2352) (p 2396) (p 2553) (p 3550) (p 4666) (derived105658 p h) (derived98288 p h)

theorem derived124315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4157) ∨ (¬ p 3083) ∨ (p 2307) ∨ (p 3016) ∨ (¬ p 2386) :=
  ElevenRUP.step124315 (p 2307) (p 2386) (p 3016) (p 3083) (p 4157) (p 4405) (derived105512 p h) (derived98314 p h)

theorem derived124317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 2598) ∨ (p 2307) ∨ (¬ p 2518) ∨ (p 2396) ∨ (¬ p 2528) ∨ (¬ p 3590) ∨ (p 2829) :=
  ElevenRUP.step124317 (p 2307) (p 2396) (p 2518) (p 2528) (p 2598) (p 2785) (p 2829) (p 3590) (p 4669) (derived105415 p h) (derived98331 p h)

theorem derived124319 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4198) ∨ (¬ p 2860) ∨ (p 2307) ∨ (¬ p 2274) :=
  ElevenRUP.step124319 (p 2140) (p 2274) (p 2307) (p 2860) (p 4198) (derived105364 p h) (derived98333 p h)

theorem derived124320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3920) ∨ (p 2307) ∨ (p 2396) :=
  ElevenRUP.step124320 (p 2307) (p 2396) (p 2417) (p 2581) (p 3920) (derived105371 p h) (derived98336 p h)

theorem derived124321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3917) ∨ (p 3146) ∨ (p 2307) ∨ (¬ p 3990) ∨ (¬ p 3256) ∨ (¬ p 2778) ∨ (¬ p 3166) :=
  ElevenRUP.step124321 (p 2122) (p 2307) (p 2778) (p 3146) (p 3166) (p 3256) (p 3917) (p 3990) (p 4433) (p 4786) (derived106150 p h) (derived106425 p h) (derived98340 p h)

theorem derived124323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2307) ∨ (p 2396) ∨ (¬ p 3550) :=
  ElevenRUP.step124323 (p 2307) (p 2383) (p 2396) (p 3550) (p 4666) (derived105658 p h) (derived98348 p h)

theorem derived124325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 2241) ∨ (¬ p 4771) ∨ (¬ p 4198) ∨ (p 2307) ∨ (¬ p 3645) ∨ (p 2187) ∨ (¬ p 2274) ∨ (p 2608) :=
  ElevenRUP.step124325 (p 2187) (p 2241) (p 2274) (p 2307) (p 2608) (p 3189) (p 3645) (p 4198) (p 4771) (p 4877) (derived105451 p h) (derived98351 p h)

theorem derived124327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2274) ∨ (p 2668) ∨ (p 2307) :=
  ElevenRUP.step124327 (p 2274) (p 2307) (p 2383) (p 2668) (p 4564) (derived105401 p h) (derived98359 p h)

theorem derived124333 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2352) ∨ (¬ p 4356) ∨ (¬ p 3660) ∨ (p 2427) :=
  ElevenRUP.step124333 (p 2352) (p 2383) (p 2427) (p 3660) (p 4356) (p 4555) (derived105542 p h) (derived98387 p h)

theorem derived124334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 5580) ∨ (¬ p 5123) ∨ (p 2383) ∨ (¬ p 3412) ∨ (p 2641) ∨ (¬ p 2667) ∨ (¬ p 2972) ∨ (¬ p 2946) :=
  ElevenRUP.step124334 (p 2255) (p 2383) (p 2641) (p 2667) (p 2946) (p 2972) (p 3412) (p 3680) (p 5123) (p 5580) (derived105367 p h) (derived98392 p h)

theorem derived124335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2187) ∨ (¬ p 4198) ∨ (p 2383) :=
  ElevenRUP.step124335 (p 2140) (p 2187) (p 2383) (p 2860) (p 4198) (derived105364 p h) (derived98394 p h)

theorem derived124336 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2187) ∨ (¬ p 2870) ∨ (¬ p 4198) ∨ (¬ p 2143) :=
  ElevenRUP.step124336 (p 2143) (p 2187) (p 2383) (p 2870) (p 4198) (p 4558) (derived105400 p h) (derived98395 p h)

theorem derived124339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3170) ∨ (p 2088) ∨ (¬ p 2651) ∨ (¬ p 3256) :=
  ElevenRUP.step124339 (p 2088) (p 2651) (p 3170) (p 3256) (p 5008) (derived105469 p h) (derived98423 p h)

theorem derived124344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4121) ∨ (¬ p 3170) ∨ (p 2088) ∨ (¬ p 3256) ∨ (¬ p 2331) :=
  ElevenRUP.step124344 (p 2088) (p 2331) (p 3170) (p 3256) (p 4121) (p 4975) (derived105464 p h) (derived98446 p h)

theorem derived124347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 2383) ∨ (¬ p 2578) ∨ (¬ p 2497) ∨ (¬ p 3923) :=
  ElevenRUP.step124347 (p 2383) (p 2497) (p 2578) (p 3422) (p 3923) (p 5214) (derived105492 p h) (derived57891 p h)

theorem derived124351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2352) ∨ (p 2274) ∨ (p 2946) ∨ (¬ p 3379) ∨ (p 2284) :=
  ElevenRUP.step124351 (p 2254) (p 2274) (p 2284) (p 2352) (p 2493) (p 2946) (p 3379) (p 4405) (derived105512 p h) (derived105366 p h) (derived98505 p h)

theorem derived124353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2528) ∨ (p 2274) ∨ (¬ p 3955) ∨ (p 3146) :=
  ElevenRUP.step124353 (p 2274) (p 2352) (p 2528) (p 3146) (p 3955) (p 4718) (derived105425 p h) (derived98515 p h)

theorem derived124355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 5580) ∨ (¬ p 3955) ∨ (¬ p 2881) :=
  ElevenRUP.step124355 (p 2881) (p 3941) (p 3955) (p 4559) (p 5580) (derived105701 p h) (derived41328 p h)

theorem derived124356 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2264) ∨ (¬ p 3955) ∨ (¬ p 2459) :=
  ElevenRUP.step124356 (p 2264) (p 2363) (p 2459) (p 3955) (p 4361) (derived105382 p h) (derived98518 p h)

theorem derived124361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2641) ∨ (¬ p 3987) ∨ (p 2668) :=
  ElevenRUP.step124361 (p 2255) (p 2383) (p 2641) (p 2668) (p 3987) (derived105367 p h) (derived98544 p h)

theorem derived124362 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2187) ∨ (p 2668) :=
  ElevenRUP.step124362 (p 2187) (p 2373) (p 2668) (p 4702) (derived106079 p h) (derived98552 p h)

theorem derived124363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 3537) ∨ (¬ p 5580) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 3366) ∨ (p 2668) ∨ (p 2331) ∨ (p 2598) :=
  ElevenRUP.step124363 (p 2252) (p 2331) (p 2598) (p 2668) (p 2748) (p 3366) (p 3537) (p 3609) (p 4749) (p 5118) (p 5580) (derived105432 p h) (derived105482 p h) (derived98555 p h)

theorem derived124364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 5580) ∨ (¬ p 2972) ∨ (p 2668) ∨ (¬ p 2210) ∨ (p 2331) ∨ (¬ p 5123) :=
  ElevenRUP.step124364 (p 2210) (p 2254) (p 2331) (p 2668) (p 2972) (p 3680) (p 5123) (p 5580) (derived105366 p h) (derived98565 p h)

theorem derived124365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2331) ∨ (¬ p 3246) ∨ (p 2668) ∨ (¬ p 3950) ∨ (¬ p 2210) ∨ (p 2363) :=
  ElevenRUP.step124365 (p 2210) (p 2254) (p 2331) (p 2363) (p 2668) (p 2891) (p 3246) (p 3950) (derived105366 p h) (derived98567 p h)

theorem derived124366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4153) ∨ (¬ p 2187) ∨ (p 2668) ∨ (¬ p 2563) :=
  ElevenRUP.step124366 (p 2187) (p 2563) (p 2668) (p 4153) (p 4702) (derived106079 p h) (derived98572 p h)

theorem derived124367 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 4804) ∨ (p 2668) ∨ (¬ p 2098) ∨ (¬ p 4236) :=
  ElevenRUP.step124367 (p 2098) (p 2331) (p 2668) (p 4236) (p 4503) (p 4804) (derived106530 p h) (derived98577 p h)

theorem derived124368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2797) ∨ (¬ p 2139) ∨ (p 2668) ∨ (p 2427) ∨ (¬ p 2373) ∨ (p 2696) :=
  ElevenRUP.step124368 (p 2139) (p 2373) (p 2427) (p 2668) (p 2696) (p 2797) (p 3051) (p 4433) (derived106150 p h) (derived98578 p h)

theorem derived124369 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 2331) ∨ (p 2363) ∨ (¬ p 3449) ∨ (p 3379) ∨ (¬ p 3366) ∨ (p 2668) ∨ (¬ p 4236) :=
  ElevenRUP.step124369 (p 2331) (p 2363) (p 2668) (p 3366) (p 3379) (p 3449) (p 4181) (p 4236) (p 4376) (p 5122) (derived106320 p h) (derived105483 p h) (derived98582 p h)

theorem derived124375 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3872) ∨ (p 2177) ∨ (¬ p 2881) ∨ (p 2295) :=
  ElevenRUP.step124375 (p 2177) (p 2295) (p 2881) (p 3872) (p 4564) (derived105401 p h) (derived98614 p h)

theorem derived124376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2396) ∨ (p 2295) ∨ (¬ p 3872) :=
  ElevenRUP.step124376 (p 2295) (p 2396) (p 3246) (p 3872) (p 4564) (derived105401 p h) (derived98617 p h)

theorem derived124377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 4153) ∨ (p 2295) ∨ (¬ p 2274) :=
  ElevenRUP.step124377 (p 2274) (p 2295) (p 3156) (p 4153) (p 4509) (derived105392 p h) (derived98630 p h)

theorem derived124378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4153) ∨ (¬ p 2274) ∨ (¬ p 2563) ∨ (p 2295) :=
  ElevenRUP.step124378 (p 2274) (p 2295) (p 2563) (p 4153) (p 4702) (derived106079 p h) (derived98631 p h)

theorem derived124381 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3083) ∨ (¬ p 2241) ∨ (p 3146) ∨ (¬ p 2459) ∨ (¬ p 2727) :=
  ElevenRUP.step124381 (p 2220) (p 2241) (p 2459) (p 2727) (p 3083) (p 3146) (p 4420) (derived105707 p h) (derived98669 p h)

theorem derived124383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4355) ∨ (p 3156) ∨ (¬ p 2528) ∨ (p 3146) :=
  ElevenRUP.step124383 (p 2528) (p 3146) (p 3156) (p 4355) (p 4702) (derived106079 p h) (derived98673 p h)

theorem derived124388 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (p 3156) ∨ (p 3146) ∨ (p 2946) ∨ (p 2608) ∨ (¬ p 2252) ∨ (¬ p 3449) :=
  ElevenRUP.step124388 (p 2252) (p 2608) (p 2750) (p 2946) (p 3146) (p 3156) (p 3449) (p 4181) (p 5122) (derived106345 p h) (derived105483 p h) (derived98681 p h)

theorem derived124389 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (p 3156) ∨ (¬ p 2829) ∨ (p 3146) ∨ (¬ p 3483) ∨ (¬ p 2608) :=
  ElevenRUP.step124389 (p 2254) (p 2608) (p 2829) (p 2946) (p 3146) (p 3156) (p 3483) (p 4330) (derived105366 p h) (derived106329 p h) (derived98682 p h)

theorem derived124390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2284) ∨ (p 3609) ∨ (¬ p 2958) ∨ (¬ p 2156) ∨ (¬ p 2459) ∨ (p 2098) :=
  ElevenRUP.step124390 (p 2098) (p 2156) (p 2284) (p 2459) (p 2958) (p 3156) (p 3609) (p 4786) (p 4902) (derived105456 p h) (derived106425 p h) (derived98695 p h)

theorem derived124391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3873) ∨ (p 2396) ∨ (p 2122) ∨ (¬ p 2946) ∨ (p 2774) ∨ (¬ p 3146) :=
  ElevenRUP.step124391 (p 2122) (p 2248) (p 2396) (p 2774) (p 2946) (p 3146) (p 3156) (p 3873) (p 4669) (derived105365 p h) (derived105415 p h) (derived98697 p h)

theorem derived124393 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3745) ∨ (¬ p 2946) ∨ (¬ p 2811) ∨ (¬ p 3156) :=
  ElevenRUP.step124393 (p 2797) (p 2811) (p 2946) (p 3156) (p 3745) (p 4509) (derived105392 p h) (derived98702 p h)

theorem derived124394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4119) ∨ (¬ p 3156) ∨ (¬ p 4140) ∨ (p 2553) ∨ (p 2284) :=
  ElevenRUP.step124394 (p 2284) (p 2553) (p 3156) (p 3958) (p 4119) (p 4140) (derived105378 p h) (derived98705 p h)

theorem derived124395 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 3276) ∨ (p 3379) ∨ (¬ p 2946) ∨ (¬ p 3156) ∨ (¬ p 3193) ∨ (¬ p 5119) :=
  ElevenRUP.step124395 (p 2248) (p 2946) (p 3156) (p 3193) (p 3276) (p 3379) (p 3969) (p 5119) (derived105365 p h) (derived98707 p h)

theorem derived124396 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3969) ∨ (p 3461) ∨ (p 3093) ∨ (¬ p 3156) ∨ (p 3319) ∨ (¬ p 5119) :=
  ElevenRUP.step124396 (p 2248) (p 2946) (p 3093) (p 3156) (p 3319) (p 3461) (p 3969) (p 5119) (derived105365 p h) (derived98712 p h)

theorem derived124399 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (p 2727) ∨ (¬ p 2274) ∨ (p 2608) ∨ (¬ p 2563) :=
  ElevenRUP.step124399 (p 2274) (p 2284) (p 2563) (p 2608) (p 2727) (p 4882) (derived105453 p h) (derived98734 p h)

theorem derived124401 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (¬ p 3519) ∨ (¬ p 4399) ∨ (¬ p 2156) ∨ (p 3527) ∨ (p 2563) ∨ (¬ p 2608) ∨ (¬ p 2373) :=
  ElevenRUP.step124401 (p 2156) (p 2373) (p 2563) (p 2608) (p 3399) (p 3519) (p 3527) (p 4376) (p 4399) (p 4902) (derived105456 p h) (derived106320 p h) (derived98741 p h)

theorem derived124402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2427) ∨ (p 3246) ∨ (¬ p 4042) :=
  ElevenRUP.step124402 (p 2373) (p 2427) (p 3246) (p 4042) (p 4666) (derived105658 p h) (derived98746 p h)

theorem derived124403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2427) ∨ (¬ p 4042) ∨ (p 2177) :=
  ElevenRUP.step124403 (p 2177) (p 2373) (p 2427) (p 4042) (p 4559) (derived105701 p h) (derived98747 p h)

theorem derived124405 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2427) ∨ (p 2264) ∨ (¬ p 4042) :=
  ElevenRUP.step124405 (p 2264) (p 2373) (p 2427) (p 4042) (p 4280) (derived105599 p h) (derived98760 p h)

theorem derived124414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3755) ∨ (¬ p 5284) ∨ (¬ p 2573) ∨ (¬ p 4419) ∨ (p 2696) ∨ (¬ p 2553) :=
  ElevenRUP.step124414 (p 2553) (p 2573) (p 2696) (p 3755) (p 3791) (p 4419) (p 4826) (p 5284) (derived105444 p h) (derived98803 p h)

theorem derived124416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 3402) :=
  ElevenRUP.step124416 (p 2255) (p 2509) (p 2651) (p 3083) (p 3402) (derived105367 p h) (derived48491 p h)

theorem derived124418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3402) ∨ (¬ p 3343) ∨ (¬ p 2630) :=
  ElevenRUP.step124418 (p 2630) (p 2745) (p 3193) (p 3343) (p 3402) (derived105523 p h) (derived58770 p h)

theorem derived124419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3402) ∨ (¬ p 2651) ∨ (¬ p 3343) :=
  ElevenRUP.step124419 (p 2255) (p 2651) (p 3193) (p 3343) (p 3402) (derived105367 p h) (derived48292 p h)

theorem derived124424 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2891) ∨ (¬ p 2459) ∨ (¬ p 2210) ∨ (¬ p 2177) :=
  ElevenRUP.step124424 (p 2177) (p 2210) (p 2459) (p 2891) (p 3146) (p 4556) (derived105399 p h) (derived98852 p h)

theorem derived124427 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4386) ∨ (¬ p 2891) ∨ (p 2264) ∨ (¬ p 2881) :=
  ElevenRUP.step124427 (p 2264) (p 2881) (p 2891) (p 4386) (p 4960) (derived106209 p h) (derived98858 p h)

theorem derived124428 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3699) ∨ (p 2807) ∨ (¬ p 2891) :=
  ElevenRUP.step124428 (p 2807) (p 2891) (p 2946) (p 3699) (p 4960) (derived106209 p h) (derived98859 p h)

theorem derived124430 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (p 3051) ∨ (¬ p 4365) ∨ (¬ p 2957) ∨ (¬ p 2891) :=
  ElevenRUP.step124430 (p 2751) (p 2891) (p 2957) (p 3051) (p 3136) (p 4365) (derived106343 p h) (derived98865 p h)

theorem derived124431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 2850) ∨ (p 2427) ∨ (¬ p 3948) :=
  ElevenRUP.step124431 (p 2427) (p 2850) (p 2891) (p 3948) (p 5217) (derived105493 p h) (derived98874 p h)

theorem derived124436 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (¬ p 2946) ∨ (¬ p 2284) :=
  ElevenRUP.step124436 (p 2284) (p 2807) (p 2946) (p 4555) (derived105542 p h) (derived98897 p h)

theorem derived124438 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 2598) ∨ (¬ p 2187) ∨ (¬ p 2946) ∨ (¬ p 2284) ∨ (p 2911) :=
  ElevenRUP.step124438 (p 2187) (p 2284) (p 2598) (p 2911) (p 2946) (p 3201) (p 4133) (p 4786) (derived105712 p h) (derived106425 p h) (derived98900 p h)

theorem derived124440 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 2946) ∨ (¬ p 2459) ∨ (¬ p 2284) ∨ (p 3449) ∨ (¬ p 2187) :=
  ElevenRUP.step124440 (p 2187) (p 2248) (p 2284) (p 2459) (p 2946) (p 3073) (p 3449) (p 4133) (derived105365 p h) (derived105712 p h) (derived98904 p h)

theorem derived124441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2819) ∨ (¬ p 2187) :=
  ElevenRUP.step124441 (p 2187) (p 2284) (p 2819) (p 4906) (derived105632 p h) (derived98906 p h)

theorem derived124446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3115) ∨ (¬ p 2946) ∨ (¬ p 3923) ∨ (¬ p 5580) ∨ (p 3093) ∨ (¬ p 5123) :=
  ElevenRUP.step124446 (p 2248) (p 2946) (p 3093) (p 3115) (p 3680) (p 3923) (p 5123) (p 5580) (derived105365 p h) (derived98922 p h)

theorem derived124455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4512) ∨ (¬ p 2860) ∨ (p 3319) ∨ (¬ p 3125) :=
  ElevenRUP.step124455 (p 2860) (p 3125) (p 3319) (p 4512) (p 4875) (derived106227 p h) (derived98953 p h)

theorem derived124458 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 2156) ∨ (¬ p 4418) ∨ (¬ p 2192) ∨ (¬ p 4313) ∨ (¬ p 2136) :=
  ElevenRUP.step124458 (p 2136) (p 2156) (p 2192) (p 2598) (p 4313) (p 4418) (p 4752) (derived105434 p h) (derived98970 p h)

theorem derived124460 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 2192) ∨ (¬ p 4365) ∨ (p 2284) :=
  ElevenRUP.step124460 (p 2192) (p 2284) (p 2751) (p 3136) (p 4365) (derived106343 p h) (derived98976 p h)

theorem derived124461 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2598) ∨ (p 2156) ∨ (¬ p 2742) ∨ (¬ p 4365) ∨ (¬ p 2192) :=
  ElevenRUP.step124461 (p 2136) (p 2156) (p 2192) (p 2598) (p 2742) (p 4365) (p 4752) (derived105434 p h) (derived98978 p h)

theorem derived124463 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2946) ∨ (¬ p 2192) ∨ (¬ p 3745) :=
  ElevenRUP.step124463 (p 2192) (p 2331) (p 2946) (p 3745) (p 4960) (derived106209 p h) (derived98980 p h)

theorem derived124468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (p 2264) ∨ (p 2807) ∨ (¬ p 2274) :=
  ElevenRUP.step124468 (p 2192) (p 2210) (p 2254) (p 2264) (p 2274) (p 2807) (p 2911) (p 4712) (derived105366 p h) (derived105422 p h) (derived98990 p h)

theorem derived124469 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 3564) ∨ (¬ p 3125) ∨ (¬ p 2590) :=
  ElevenRUP.step124469 (p 2192) (p 2590) (p 3125) (p 3564) (p 4632) (derived106257 p h) (derived98991 p h)

theorem derived124470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4153) ∨ (¬ p 2192) ∨ (p 3323) ∨ (¬ p 3125) :=
  ElevenRUP.step124470 (p 2192) (p 3125) (p 3323) (p 4153) (p 4960) (derived106209 p h) (derived98993 p h)

theorem derived124486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2850) ∨ (p 3449) ∨ (p 3073) ∨ (¬ p 2459) ∨ (¬ p 2373) :=
  ElevenRUP.step124486 (p 2373) (p 2459) (p 2598) (p 2850) (p 3073) (p 3449) (p 4733) (p 4902) (derived105430 p h) (derived105456 p h) (derived99033 p h)

theorem derived124487 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (¬ p 2619) ∨ (¬ p 4521) ∨ (p 3449) ∨ (¬ p 2156) ∨ (¬ p 2459) ∨ (p 2860) :=
  ElevenRUP.step124487 (p 2156) (p 2459) (p 2619) (p 2860) (p 3073) (p 3449) (p 4521) (p 4902) (derived105456 p h) (derived99035 p h)

theorem derived124488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3453) ∨ (¬ p 3083) ∨ (¬ p 2528) ∨ (p 3073) :=
  ElevenRUP.step124488 (p 2528) (p 3073) (p 3083) (p 3453) (p 4811) (derived105633 p h) (derived99039 p h)

theorem derived124490 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (p 3073) ∨ (p 2440) ∨ (¬ p 2651) ∨ (¬ p 2373) ∨ (¬ p 2459) :=
  ElevenRUP.step124490 (p 2248) (p 2373) (p 2440) (p 2459) (p 2651) (p 3073) (p 3449) (p 4902) (derived105365 p h) (derived105456 p h) (derived99052 p h)

theorem derived124491 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 3093) ∨ (¬ p 2363) ∨ (¬ p 2881) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 4371) :=
  ElevenRUP.step124491 (p 2132) (p 2363) (p 2870) (p 2881) (p 3073) (p 3093) (p 4371) (p 4503) (p 4733) (derived105430 p h) (derived106530 p h) (derived99053 p h)

theorem derived124492 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 3449) ∨ (¬ p 2528) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2177) ∨ (¬ p 4438) :=
  ElevenRUP.step124492 (p 2122) (p 2177) (p 2528) (p 2774) (p 3073) (p 3449) (p 4438) (p 4733) (derived105430 p h) (derived99055 p h)

theorem derived124493 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (p 3073) ∨ (¬ p 4596) ∨ (p 3449) ∨ (¬ p 2363) ∨ (¬ p 3083) ∨ (¬ p 3389) ∨ (¬ p 3683) ∨ (¬ p 2663) :=
  ElevenRUP.step124493 (p 2248) (p 2363) (p 2663) (p 3073) (p 3083) (p 3201) (p 3389) (p 3449) (p 3683) (p 4596) (derived105365 p h) (derived99056 p h)

theorem derived124495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3286) ∨ (p 3073) ∨ (¬ p 2608) ∨ (p 2761) ∨ (p 3449) ∨ (¬ p 2246) ∨ (¬ p 3950) :=
  ElevenRUP.step124495 (p 2246) (p 2608) (p 2744) (p 2761) (p 3073) (p 3286) (p 3449) (p 3506) (p 3950) (derived106503 p h) (derived99061 p h)

theorem derived124496 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2630) ∨ (¬ p 3343) ∨ (¬ p 2210) ∨ (p 3073) ∨ (¬ p 4332) :=
  ElevenRUP.step124496 (p 2210) (p 2630) (p 2696) (p 2753) (p 3073) (p 3343) (p 3449) (p 4332) (p 4877) (derived105451 p h) (derived99062 p h)

theorem derived124497 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (¬ p 2717) ∨ (¬ p 2753) ∨ (p 3449) ∨ (p 3073) ∨ (¬ p 3941) ∨ (¬ p 2241) :=
  ElevenRUP.step124497 (p 2241) (p 2717) (p 2750) (p 2753) (p 3073) (p 3425) (p 3449) (p 3941) (p 5122) (derived106345 p h) (derived105483 p h) (derived99066 p h)

theorem derived124498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 2717) ∨ (p 3449) ∨ (p 3073) ∨ (p 3425) ∨ (¬ p 2753) ∨ (¬ p 4138) ∨ (¬ p 3379) :=
  ElevenRUP.step124498 (p 2717) (p 2753) (p 3073) (p 3379) (p 3425) (p 3449) (p 3979) (p 4138) (p 5122) (derived105483 p h) (derived99067 p h)

theorem derived124504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 2584) ∨ (p 2230) ∨ (p 3564) :=
  ElevenRUP.step124504 (p 2230) (p 2584) (p 3564) (p 3654) (p 4717) (derived105424 p h) (derived99114 p h)

theorem derived124505 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2493) ∨ (p 3564) ∨ (¬ p 2807) ∨ (¬ p 2264) ∨ (¬ p 2459) :=
  ElevenRUP.step124505 (p 2248) (p 2264) (p 2459) (p 2493) (p 2807) (p 3379) (p 3564) (p 4604) (derived105365 p h) (derived106293 p h) (derived99116 p h)

theorem derived124506 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 3564) ∨ (¬ p 3051) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (p 3379) ∨ (¬ p 4521) :=
  ElevenRUP.step124506 (p 2459) (p 2493) (p 2881) (p 3051) (p 3379) (p 3564) (p 4521) (p 4604) (derived106293 p h) (derived99117 p h)

theorem derived124509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3506) ∨ (¬ p 3286) ∨ (p 2573) ∨ (p 2727) ∨ (p 3266) ∨ (p 3564) ∨ (¬ p 2662) :=
  ElevenRUP.step124509 (p 2255) (p 2573) (p 2662) (p 2727) (p 3266) (p 3286) (p 3506) (p 3564) (p 4604) (derived105367 p h) (derived106293 p h) (derived99126 p h)

theorem derived124510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3422) ∨ (p 2598) ∨ (p 3564) ∨ (¬ p 2246) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3366) :=
  ElevenRUP.step124510 (p 2246) (p 2598) (p 2744) (p 2901) (p 2946) (p 3246) (p 3366) (p 3422) (p 3564) (p 4625) (derived106503 p h) (derived106455 p h) (derived99129 p h)

theorem derived124511 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 4236) ∨ (¬ p 3246) ∨ (p 3016) ∨ (p 2651) ∨ (¬ p 3571) ∨ (p 3564) ∨ (¬ p 3399) ∨ (¬ p 3366) :=
  ElevenRUP.step124511 (p 2210) (p 2651) (p 3016) (p 3246) (p 3366) (p 3399) (p 3564) (p 3571) (p 4236) (p 4377) (p 4625) (derived106170 p h) (derived106455 p h) (derived99134 p h)

theorem derived124512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (p 2573) ∨ (¬ p 5119) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (p 3564) ∨ (p 3461) ∨ (¬ p 3905) :=
  ElevenRUP.step124512 (p 2264) (p 2573) (p 2807) (p 3461) (p 3564) (p 3905) (p 3941) (p 4786) (p 5119) (derived106425 p h) (derived99139 p h)

theorem derived124513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3683) ∨ (p 3422) ∨ (¬ p 3370) ∨ (¬ p 3051) ∨ (¬ p 2459) ∨ (p 2651) ∨ (¬ p 3366) ∨ (p 3564) ∨ (¬ p 2881) ∨ (¬ p 4236) :=
  ElevenRUP.step124513 (p 2459) (p 2651) (p 2881) (p 3051) (p 3366) (p 3370) (p 3422) (p 3564) (p 3683) (p 4236) (p 4377) (p 4604) (derived106293 p h) (derived106170 p h) (derived99140 p h)

theorem derived124517 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (p 2493) ∨ (¬ p 2341) ∨ (p 2264) ∨ (p 3564) ∨ (¬ p 2449) :=
  ElevenRUP.step124517 (p 2264) (p 2341) (p 2449) (p 2493) (p 3379) (p 3564) (p 4625) (p 5207) (derived105491 p h) (derived106455 p h) (derived99145 p h)

theorem derived124519 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (p 2797) ∨ (p 2996) ∨ (¬ p 2331) :=
  ElevenRUP.step124519 (p 2331) (p 2751) (p 2797) (p 2807) (p 2996) (derived106343 p h) (derived99168 p h)

theorem derived124521 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (p 2737) ∨ (¬ p 2528) ∨ (p 2807) ∨ (p 2449) ∨ (¬ p 2598) ∨ (¬ p 3361) :=
  ElevenRUP.step124521 (p 2449) (p 2528) (p 2598) (p 2737) (p 2807) (p 3361) (p 3641) (p 4669) (derived105415 p h) (derived99170 p h)

theorem derived124525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3609) ∨ (¬ p 3537) ∨ (p 2807) ∨ (p 2132) ∨ (¬ p 2748) ∨ (p 2264) ∨ (¬ p 5558) ∨ (¬ p 2252) ∨ (¬ p 3366) :=
  ElevenRUP.step124525 (p 2132) (p 2252) (p 2264) (p 2748) (p 2807) (p 3366) (p 3537) (p 3609) (p 5118) (p 5558) (derived105482 p h) (derived99194 p h)

theorem derived124529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 3564) ∨ (p 2459) ∨ (¬ p 3379) ∨ (p 2264) ∨ (p 2807) :=
  ElevenRUP.step124529 (p 2254) (p 2264) (p 2459) (p 2493) (p 2807) (p 3379) (p 3564) (p 4330) (derived105366 p h) (derived106329 p h) (derived99206 p h)

theorem derived124531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (¬ p 2252) ∨ (p 2807) ∨ (p 2459) ∨ (p 2608) ∨ (¬ p 3449) ∨ (p 2264) :=
  ElevenRUP.step124531 (p 2252) (p 2264) (p 2459) (p 2608) (p 2750) (p 2807) (p 3449) (p 4181) (p 5122) (derived106345 p h) (derived105483 p h) (derived99221 p h)

theorem derived124532 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (¬ p 4431) ∨ (p 2449) ∨ (¬ p 4365) ∨ (¬ p 3631) :=
  ElevenRUP.step124532 (p 2249) (p 2449) (p 2807) (p 3631) (p 4365) (p 4431) (derived106513 p h) (derived99224 p h)

theorem derived124534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3105) ∨ (¬ p 2132) ∨ (p 2264) ∨ (¬ p 5558) ∨ (p 2807) ∨ (¬ p 5123) :=
  ElevenRUP.step124534 (p 2132) (p 2264) (p 2807) (p 3105) (p 3680) (p 4789) (p 5123) (p 5558) (derived105646 p h) (derived99241 p h)

theorem derived124535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3125) ∨ (¬ p 2192) ∨ (p 2264) ∨ (¬ p 2210) ∨ (p 2807) ∨ (p 2459) :=
  ElevenRUP.step124535 (p 2192) (p 2210) (p 2254) (p 2264) (p 2459) (p 2807) (p 3125) (p 4330) (derived105366 p h) (derived106329 p h) (derived99249 p h)

theorem derived124536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (p 2210) ∨ (p 2881) ∨ (p 2891) :=
  ElevenRUP.step124536 (p 2210) (p 2248) (p 2352) (p 2651) (p 2881) (p 2891) (p 3016) (p 4133) (derived105365 p h) (derived105712 p h) (derived99262 p h)

theorem derived124539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (¬ p 4443) ∨ (p 2528) :=
  ElevenRUP.step124539 (p 2528) (p 2881) (p 3246) (p 4420) (p 4443) (derived105707 p h) (derived99269 p h)

theorem derived124540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (¬ p 4443) ∨ (p 2363) :=
  ElevenRUP.step124540 (p 2363) (p 2881) (p 3246) (p 4133) (p 4443) (derived105712 p h) (derived99270 p h)

theorem derived124542 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (p 2132) ∨ (p 2881) ∨ (¬ p 2246) ∨ (¬ p 2352) ∨ (¬ p 2651) ∨ (¬ p 3366) ∨ (¬ p 3016) :=
  ElevenRUP.step124542 (p 2132) (p 2246) (p 2352) (p 2651) (p 2744) (p 2870) (p 2881) (p 3016) (p 3366) (p 4133) (derived106503 p h) (derived105712 p h) (derived99275 p h)

theorem derived124544 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2598) ∨ (p 2881) ∨ (p 2553) ∨ (¬ p 2264) ∨ (¬ p 2807) :=
  ElevenRUP.step124544 (p 2264) (p 2553) (p 2598) (p 2807) (p 2881) (p 3422) (p 4556) (p 4786) (derived105399 p h) (derived106425 p h) (derived99283 p h)

theorem derived124546 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 4192) ∨ (p 2761) ∨ (p 2881) :=
  ElevenRUP.step124546 (p 2761) (p 2881) (p 3680) (p 4192) (p 4668) (derived105414 p h) (derived99285 p h)

theorem derived124549 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (¬ p 3402) :=
  ElevenRUP.step124549 (p 2255) (p 2493) (p 2651) (p 3016) (p 3402) (derived105367 p h) (derived99300 p h)

theorem derived124552 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 2493) ∨ (¬ p 2386) ∨ (¬ p 3413) ∨ (¬ p 2284) ∨ (¬ p 3016) ∨ (¬ p 4031) :=
  ElevenRUP.step124552 (p 2156) (p 2284) (p 2386) (p 2493) (p 3016) (p 3413) (p 4031) (p 4705) (derived106238 p h) (derived99323 p h)

theorem derived124553 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2177) ∨ (p 2264) ∨ (¬ p 2449) :=
  ElevenRUP.step124553 (p 2177) (p 2264) (p 2417) (p 2449) (p 4276) (derived105516 p h) (derived99328 p h)

theorem derived124554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 3005) ∨ (¬ p 2881) ∨ (p 2264) ∨ (¬ p 2177) :=
  ElevenRUP.step124554 (p 2177) (p 2264) (p 2630) (p 2881) (p 3005) (p 4280) (derived105599 p h) (derived99341 p h)

theorem derived124556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 2459) ∨ (¬ p 2608) ∨ (¬ p 2829) ∨ (p 2264) ∨ (p 2807) :=
  ElevenRUP.step124556 (p 2254) (p 2264) (p 2459) (p 2608) (p 2807) (p 2829) (p 3483) (p 4330) (derived105366 p h) (derived106329 p h) (derived99355 p h)

theorem derived124557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (p 2807) ∨ (¬ p 2608) ∨ (p 2459) ∨ (¬ p 4450) ∨ (¬ p 2839) ∨ (p 2264) :=
  ElevenRUP.step124557 (p 2254) (p 2264) (p 2459) (p 2608) (p 2807) (p 2839) (p 3105) (p 4450) (derived105366 p h) (derived99357 p h)

theorem derived124558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2807) ∨ (p 2264) ∨ (¬ p 2982) ∨ (¬ p 3379) ∨ (p 2459) ∨ (¬ p 4450) :=
  ElevenRUP.step124558 (p 2254) (p 2264) (p 2406) (p 2459) (p 2807) (p 2982) (p 3379) (p 4450) (derived105366 p h) (derived99359 p h)

theorem derived124561 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2996) ∨ (p 2264) ∨ (¬ p 3246) :=
  ElevenRUP.step124561 (p 2230) (p 2241) (p 2264) (p 2427) (p 2996) (p 3246) (p 4668) (p 5190) (derived105414 p h) (derived105487 p h) (derived99367 p h)

theorem derived124562 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (p 2685) ∨ (¬ p 3631) ∨ (p 2264) ∨ (p 2210) ∨ (¬ p 3399) ∨ (¬ p 3366) :=
  ElevenRUP.step124562 (p 2210) (p 2264) (p 2685) (p 2696) (p 3366) (p 3399) (p 3631) (p 4377) (p 4668) (derived105414 p h) (derived106170 p h) (derived99372 p h)

theorem derived124563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2727) ∨ (p 2264) :=
  ElevenRUP.step124563 (p 2264) (p 2727) (p 3527) (p 4652) (derived105413 p h) (derived99374 p h)

theorem derived124564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2996) ∨ (¬ p 4104) ∨ (p 2264) :=
  ElevenRUP.step124564 (p 2255) (p 2264) (p 2341) (p 2996) (p 4104) (derived105367 p h) (derived99376 p h)

theorem derived124566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 2417) ∨ (p 2807) ∨ (p 2264) ∨ (¬ p 2946) ∨ (p 3136) :=
  ElevenRUP.step124566 (p 2264) (p 2417) (p 2807) (p 2922) (p 2946) (p 3136) (p 3379) (p 4668) (derived105414 p h) (derived99381 p h)

theorem derived124567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 2860) ∨ (¬ p 2252) ∨ (¬ p 3370) ∨ (p 2459) ∨ (¬ p 2156) ∨ (p 2264) ∨ (¬ p 3105) ∨ (p 2807) ∨ (¬ p 4450) :=
  ElevenRUP.step124567 (p 2156) (p 2252) (p 2264) (p 2459) (p 2750) (p 2807) (p 2860) (p 3105) (p 3370) (p 3371) (p 4450) (derived106345 p h) (derived99383 p h)

theorem derived124569 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (p 2685) ∨ (¬ p 2470) ∨ (¬ p 4079) ∨ (¬ p 2528) ∨ (p 2264) ∨ (p 3146) :=
  ElevenRUP.step124569 (p 2264) (p 2470) (p 2528) (p 2685) (p 2696) (p 3146) (p 4079) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived99390 p h)

theorem derived124573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2553) ∨ (p 2696) ∨ (¬ p 3519) ∨ (p 2685) ∨ (p 2264) ∨ (¬ p 3366) ∨ (¬ p 2396) :=
  ElevenRUP.step124573 (p 2264) (p 2396) (p 2553) (p 2573) (p 2685) (p 2696) (p 3366) (p 3519) (p 4376) (p 4668) (derived105414 p h) (derived106320 p h) (derived99400 p h)

theorem derived124576 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (p 2696) ∨ (¬ p 2210) ∨ (¬ p 2187) ∨ (p 2264) ∨ (¬ p 2192) :=
  ElevenRUP.step124576 (p 2187) (p 2192) (p 2210) (p 2264) (p 2685) (p 2696) (p 4133) (p 4736) (derived105431 p h) (derived105712 p h) (derived99405 p h)

theorem derived124577 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (p 2685) ∨ (p 2264) ∨ (¬ p 2210) ∨ (¬ p 3246) ∨ (¬ p 2891) :=
  ElevenRUP.step124577 (p 2210) (p 2264) (p 2685) (p 2696) (p 2891) (p 3246) (p 4668) (p 4736) (derived105431 p h) (derived105414 p h) (derived99406 p h)

theorem derived124578 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2860) ∨ (p 2264) ∨ (¬ p 2187) ∨ (¬ p 2996) ∨ (¬ p 2132) :=
  ElevenRUP.step124578 (p 2132) (p 2187) (p 2241) (p 2264) (p 2860) (p 2996) (p 4133) (p 4733) (derived105430 p h) (derived105712 p h) (derived99407 p h)

theorem derived124579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 3759) ∨ (¬ p 2748) ∨ (¬ p 2996) ∨ (p 2696) ∨ (p 2264) ∨ (¬ p 2230) ∨ (¬ p 2373) :=
  ElevenRUP.step124579 (p 2230) (p 2264) (p 2373) (p 2696) (p 2748) (p 2996) (p 3367) (p 3759) (p 4902) (derived105456 p h) (derived99413 p h)

theorem derived124583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2685) ∨ (p 2264) ∨ (¬ p 2663) ∨ (¬ p 5201) :=
  ElevenRUP.step124583 (p 2264) (p 2341) (p 2663) (p 2685) (p 4790) (p 5201) (derived106424 p h) (derived99434 p h)

theorem derived124584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2685) ∨ (¬ p 4104) ∨ (p 2264) :=
  ElevenRUP.step124584 (p 2264) (p 2341) (p 2685) (p 4104) (p 4790) (derived106424 p h) (derived99436 p h)

theorem derived124585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2685) ∨ (¬ p 4104) ∨ (¬ p 2246) ∨ (p 2264) :=
  ElevenRUP.step124585 (p 2246) (p 2264) (p 2341) (p 2685) (p 2751) (p 4104) (derived106343 p h) (derived99437 p h)

end ElevenLogic
