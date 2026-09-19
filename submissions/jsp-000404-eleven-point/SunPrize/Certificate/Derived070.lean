import SunPrize.Certificate.Derived069
import SunPrize.Certificate.Logic070
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived122169 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2685) ∨ (¬ p 2156) ∨ (¬ p 4043) ∨ (¬ p 2996) ∨ (¬ p 3370) ∨ (¬ p 2373) ∨ (¬ p 2741) ∨ (p 2563) :=
  ElevenRUP.step122169 (p 2156) (p 2373) (p 2563) (p 2685) (p 2741) (p 2996) (p 3005) (p 3370) (p 4043) (p 4377) (derived106170 p h) (derived89084 p h)

theorem derived122170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4774) ∨ (¬ p 2518) ∨ (p 2807) ∨ (p 2363) ∨ (p 3005) ∨ (¬ p 2528) ∨ (¬ p 2685) ∨ (¬ p 4236) ∨ (¬ p 3366) :=
  ElevenRUP.step122170 (p 2363) (p 2518) (p 2528) (p 2685) (p 2807) (p 3005) (p 3366) (p 4236) (p 4376) (p 4774) (derived106320 p h) (derived89085 p h)

theorem derived122171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (p 3005) ∨ (¬ p 4043) ∨ (¬ p 4236) ∨ (¬ p 2373) ∨ (p 2807) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step122171 (p 2373) (p 2406) (p 2685) (p 2807) (p 3005) (p 3379) (p 4043) (p 4236) (p 4736) (derived105431 p h) (derived89086 p h)

theorem derived122174 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 2470) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3347) ∨ (¬ p 2264) ∨ (¬ p 2753) ∨ (¬ p 3146) :=
  ElevenRUP.step122174 (p 2264) (p 2470) (p 2528) (p 2685) (p 2696) (p 2753) (p 3146) (p 3347) (p 4905) (derived105995 p h) (derived89096 p h)

theorem derived122175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4236) ∨ (p 3755) ∨ (p 2807) ∨ (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 2363) ∨ (¬ p 2685) ∨ (¬ p 3519) :=
  ElevenRUP.step122175 (p 2352) (p 2363) (p 2573) (p 2685) (p 2807) (p 3366) (p 3519) (p 3755) (p 4236) (p 4376) (p 5113) (derived106320 p h) (derived105481 p h) (derived89099 p h)

theorem derived122176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 4236) ∨ (¬ p 2685) ∨ (p 2807) :=
  ElevenRUP.step122176 (p 2598) (p 2685) (p 2807) (p 4236) (p 4752) (derived105434 p h) (derived89101 p h)

theorem derived122183 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 3449) ∨ (¬ p 2264) ∨ (¬ p 2696) ∨ (¬ p 2363) ∨ (¬ p 2685) :=
  ElevenRUP.step122183 (p 2264) (p 2363) (p 2685) (p 2696) (p 3073) (p 3449) (p 4503) (p 4733) (derived105430 p h) (derived106530 p h) (derived89110 p h)

theorem derived122188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (p 3631) ∨ (¬ p 2449) ∨ (¬ p 3031) :=
  ElevenRUP.step122188 (p 2449) (p 2685) (p 2745) (p 3031) (p 3631) (derived105523 p h) (derived89124 p h)

theorem derived122193 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 2210) ∨ (p 3125) ∨ (¬ p 2449) ∨ (¬ p 2696) ∨ (¬ p 2685) :=
  ElevenRUP.step122193 (p 2192) (p 2210) (p 2449) (p 2685) (p 2696) (p 3125) (p 4625) (p 4733) (derived105430 p h) (derived106455 p h) (derived89141 p h)

theorem derived122197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (p 2630) ∨ (p 2264) :=
  ElevenRUP.step122197 (p 2264) (p 2630) (p 2717) (p 4652) (derived105413 p h) (derived89150 p h)

theorem derived122199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2996) ∨ (p 3425) ∨ (¬ p 2245) ∨ (¬ p 2992) ∨ (p 2177) ∨ (¬ p 2717) ∨ (p 2946) :=
  ElevenRUP.step122199 (p 2177) (p 2245) (p 2717) (p 2946) (p 2992) (p 2996) (p 3425) (p 4361) (p 4733) (derived105430 p h) (derived105382 p h) (derived89155 p h)

theorem derived122200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4477) ∨ (¬ p 2717) ∨ (¬ p 2274) ∨ (¬ p 2284) ∨ (p 3527) ∨ (p 3399) ∨ (¬ p 2946) :=
  ElevenRUP.step122200 (p 2248) (p 2274) (p 2284) (p 2717) (p 2946) (p 3399) (p 3527) (p 4477) (derived105365 p h) (derived89158 p h)

theorem derived122202 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2717) ∨ (¬ p 3587) ∨ (p 2881) :=
  ElevenRUP.step122202 (p 2140) (p 2717) (p 2881) (p 3051) (p 3587) (derived105364 p h) (derived89171 p h)

theorem derived122212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2946) ∨ (p 3246) ∨ (p 2901) ∨ (¬ p 2717) ∨ (¬ p 2608) :=
  ElevenRUP.step122212 (p 2254) (p 2608) (p 2707) (p 2717) (p 2901) (p 2946) (p 3246) (p 4666) (derived105366 p h) (derived105658 p h) (derived89202 p h)

theorem derived122214 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2230) ∨ (¬ p 2608) ∨ (p 3246) ∨ (p 2427) ∨ (¬ p 2717) :=
  ElevenRUP.step122214 (p 2230) (p 2427) (p 2608) (p 2707) (p 2717) (p 3246) (p 4666) (p 5193) (derived105488 p h) (derived105658 p h) (derived89211 p h)

theorem derived122215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (p 3146) ∨ (¬ p 2459) ∨ (¬ p 4119) :=
  ElevenRUP.step122215 (p 2459) (p 2717) (p 3146) (p 4119) (p 4898) (derived105455 p h) (derived89212 p h)

theorem derived122219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 4781) ∨ (¬ p 4155) ∨ (¬ p 2996) ∨ (p 2341) :=
  ElevenRUP.step122219 (p 2341) (p 2717) (p 2745) (p 2996) (p 4155) (p 4781) (derived105523 p h) (derived89223 p h)

theorem derived122221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4040) ∨ (¬ p 3212) ∨ (¬ p 3506) ∨ (p 3434) ∨ (¬ p 2717) ∨ (p 2341) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 2958) ∨ (¬ p 3820) ∨ (p 3461) :=
  ElevenRUP.step122221 (p 2246) (p 2341) (p 2717) (p 2744) (p 2958) (p 3212) (p 3366) (p 3434) (p 3461) (p 3506) (p 3820) (p 4040) (p 4621) (derived106503 p h) (derived105407 p h) (derived89230 p h)

theorem derived122222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4115) ∨ (¬ p 2717) ∨ (¬ p 3960) ∨ (¬ p 2427) ∨ (p 2373) :=
  ElevenRUP.step122222 (p 2373) (p 2427) (p 2717) (p 3960) (p 4115) (p 4898) (derived105455 p h) (derived89241 p h)

theorem derived122229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (p 2992) ∨ (¬ p 4781) ∨ (p 2264) ∨ (¬ p 4386) :=
  ElevenRUP.step122229 (p 2264) (p 2717) (p 2745) (p 2992) (p 4386) (p 4781) (derived105523 p h) (derived89255 p h)

theorem derived122234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (p 3434) ∨ (¬ p 4445) ∨ (¬ p 3146) :=
  ElevenRUP.step122234 (p 2717) (p 3146) (p 3434) (p 4445) (p 4905) (derived105995 p h) (derived89266 p h)

theorem derived122235 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2230) ∨ (¬ p 2608) ∨ (¬ p 2717) ∨ (¬ p 3693) ∨ (p 2440) ∨ (¬ p 2707) :=
  ElevenRUP.step122235 (p 2230) (p 2440) (p 2608) (p 2707) (p 2717) (p 3083) (p 3693) (p 4905) (p 5193) (derived105488 p h) (derived105995 p h) (derived89267 p h)

theorem derived122236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (p 2651) ∨ (¬ p 2440) ∨ (p 2373) ∨ (¬ p 2717) ∨ (¬ p 2608) :=
  ElevenRUP.step122236 (p 2254) (p 2373) (p 2440) (p 2608) (p 2651) (p 2707) (p 2717) (p 4905) (derived105366 p h) (derived105995 p h) (derived89268 p h)

theorem derived122241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3516) ∨ (¬ p 2241) ∨ (p 2166) ∨ (p 2210) ∨ (p 3434) ∨ (¬ p 2717) ∨ (¬ p 3819) :=
  ElevenRUP.step122241 (p 2166) (p 2210) (p 2241) (p 2717) (p 2750) (p 2753) (p 3434) (p 3516) (p 3819) (p 4905) (derived106345 p h) (derived105995 p h) (derived89278 p h)

theorem derived122244 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2440) ∨ (p 2427) ∨ (¬ p 3631) ∨ (¬ p 3399) ∨ (p 2396) :=
  ElevenRUP.step122244 (p 2254) (p 2396) (p 2427) (p 2440) (p 2651) (p 3399) (p 3631) (p 4559) (derived105366 p h) (derived105701 p h) (derived89296 p h)

theorem derived122249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 4452) ∨ (p 2274) ∨ (p 2396) :=
  ElevenRUP.step122249 (p 2274) (p 2396) (p 3631) (p 4452) (p 4518) (derived106113 p h) (derived89328 p h)

theorem derived122252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 2651) ∨ (p 2608) ∨ (¬ p 2252) ∨ (¬ p 3950) ∨ (p 3083) ∨ (¬ p 3399) ∨ (p 2528) :=
  ElevenRUP.step122252 (p 2252) (p 2528) (p 2608) (p 2651) (p 2750) (p 3083) (p 3399) (p 3631) (p 3950) (derived106345 p h) (derived89337 p h)

theorem derived122260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 5206) ∨ (p 3516) ∨ (¬ p 2608) :=
  ElevenRUP.step122260 (p 2608) (p 3516) (p 3631) (p 4793) (p 5206) (derived105438 p h) (derived89366 p h)

theorem derived122262 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 3631) ∨ (¬ p 3399) ∨ (¬ p 3542) :=
  ElevenRUP.step122262 (p 3399) (p 3449) (p 3542) (p 3631) (p 4668) (derived105414 p h) (derived89374 p h)

theorem derived122264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (p 2946) ∨ (¬ p 2252) ∨ (p 2608) ∨ (p 3146) ∨ (p 3156) ∨ (¬ p 3950) :=
  ElevenRUP.step122264 (p 2252) (p 2608) (p 2750) (p 2946) (p 3146) (p 3156) (p 3399) (p 3631) (p 3950) (derived106345 p h) (derived89386 p h)

theorem derived122265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4356) ∨ (p 3516) ∨ (p 2563) ∨ (¬ p 3631) ∨ (¬ p 4431) ∨ (¬ p 2311) :=
  ElevenRUP.step122265 (p 2311) (p 2563) (p 3516) (p 3631) (p 4356) (p 4431) (p 4632) (derived106257 p h) (derived89387 p h)

theorem derived122267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 5558) ∨ (p 2177) ∨ (¬ p 3747) :=
  ElevenRUP.step122267 (p 2177) (p 3747) (p 3969) (p 4559) (p 5558) (derived105701 p h) (derived89400 p h)

theorem derived122268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3875) ∨ (¬ p 4149) ∨ (p 2881) ∨ (¬ p 5558) :=
  ElevenRUP.step122268 (p 2881) (p 3875) (p 4149) (p 4647) (p 5558) (derived105412 p h) (derived89405 p h)

theorem derived122269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4443) ∨ (¬ p 4325) ∨ (¬ p 2449) ∨ (p 2341) ∨ (¬ p 5558) ∨ (¬ p 3959) :=
  ElevenRUP.step122269 (p 2341) (p 2449) (p 3959) (p 4325) (p 4443) (p 5118) (p 5558) (derived105482 p h) (derived89407 p h)

theorem derived122270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 5558) ∨ (¬ p 4443) ∨ (p 2341) :=
  ElevenRUP.step122270 (p 2341) (p 3516) (p 4443) (p 5118) (p 5558) (derived105482 p h) (derived89409 p h)

theorem derived122273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 5558) ∨ (p 2911) ∨ (¬ p 3325) :=
  ElevenRUP.step122273 (p 2911) (p 3325) (p 3979) (p 4276) (p 5558) (derived105516 p h) (derived89417 p h)

theorem derived122274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 2972) ∨ (¬ p 5123) ∨ (p 3389) ∨ (¬ p 2210) ∨ (¬ p 5558) ∨ (p 2911) :=
  ElevenRUP.step122274 (p 2210) (p 2911) (p 2972) (p 3389) (p 3680) (p 5123) (p 5193) (p 5558) (derived105488 p h) (derived89419 p h)

theorem derived122275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3670) ∨ (¬ p 4030) ∨ (p 3389) ∨ (¬ p 3619) ∨ (¬ p 3347) ∨ (¬ p 5558) ∨ (p 2911) ∨ (p 2696) ∨ (¬ p 5123) :=
  ElevenRUP.step122275 (p 2696) (p 2911) (p 3347) (p 3389) (p 3619) (p 3670) (p 4030) (p 4752) (p 5123) (p 5558) (derived105434 p h) (derived89420 p h)

theorem derived122277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3875) ∨ (¬ p 4149) ∨ (p 2417) ∨ (¬ p 5558) :=
  ElevenRUP.step122277 (p 2417) (p 3875) (p 4149) (p 4666) (p 5558) (derived105658 p h) (derived89424 p h)

theorem derived122278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5558) ∨ (p 2911) ∨ (¬ p 3256) ∨ (¬ p 2241) ∨ (p 3389) ∨ (¬ p 3189) :=
  ElevenRUP.step122278 (p 2241) (p 2911) (p 3189) (p 3256) (p 3389) (p 5118) (p 5193) (p 5558) (derived105488 p h) (derived105482 p h) (derived89427 p h)

theorem derived122281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 5558) ∨ (p 2881) ∨ (¬ p 3325) :=
  ElevenRUP.step122281 (p 2881) (p 3325) (p 3979) (p 4556) (p 5558) (derived105399 p h) (derived89435 p h)

theorem derived122282 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3276) ∨ (p 3527) ∨ (¬ p 5558) ∨ (p 3399) ∨ (¬ p 3333) ∨ (¬ p 5123) :=
  ElevenRUP.step122282 (p 2598) (p 3276) (p 3333) (p 3399) (p 3527) (p 4733) (p 5123) (p 5558) (derived105430 p h) (derived89441 p h)

theorem derived122284 (p : Nat → Prop) (h : Inputs p) :
    (p 2641) ∨ (p 2341) ∨ (¬ p 5123) ∨ (p 3193) ∨ (¬ p 2311) ∨ (¬ p 2667) ∨ (¬ p 4116) ∨ (¬ p 3276) ∨ (¬ p 5558) ∨ (¬ p 2651) :=
  ElevenRUP.step122284 (p 2255) (p 2311) (p 2341) (p 2641) (p 2651) (p 2667) (p 3193) (p 3276) (p 4116) (p 5123) (p 5558) (derived105367 p h) (derived89445 p h)

theorem derived122286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 5558) ∨ (p 2807) ∨ (¬ p 2573) ∨ (p 2264) ∨ (¬ p 3564) ∨ (¬ p 3362) ∨ (¬ p 5123) :=
  ElevenRUP.step122286 (p 2264) (p 2573) (p 2807) (p 3362) (p 3461) (p 3564) (p 4789) (p 5123) (p 5558) (derived105646 p h) (derived89451 p h)

theorem derived122293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (p 2727) ∨ (p 3256) ∨ (¬ p 3859) ∨ (¬ p 4196) :=
  ElevenRUP.step122293 (p 2727) (p 3073) (p 3256) (p 3859) (p 4196) (p 4975) (derived105464 p h) (derived89485 p h)

theorem derived122295 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (¬ p 5600) ∨ (¬ p 2187) ∨ (¬ p 4196) :=
  ElevenRUP.step122295 (p 2187) (p 3979) (p 4196) (p 4564) (p 5600) (derived105401 p h) (derived62370 p h)

theorem derived122296 (p : Nat → Prop) (h : Inputs p) :
    (p 3343) ∨ (¬ p 3083) ∨ (¬ p 4440) ∨ (¬ p 2459) :=
  ElevenRUP.step122296 (p 2459) (p 3083) (p 3343) (p 4420) (p 4440) (derived105707 p h) (derived89504 p h)

theorem derived122298 (p : Nat → Prop) (h : Inputs p) :
    (p 3343) ∨ (p 2651) ∨ (¬ p 2946) ∨ (¬ p 4241) :=
  ElevenRUP.step122298 (p 2651) (p 2946) (p 3343) (p 4241) (p 4949) (derived105463 p h) (derived89507 p h)

theorem derived122299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2470) ∨ (¬ p 3246) ∨ (¬ p 2870) ∨ (¬ p 4440) ∨ (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2655) ∨ (¬ p 2252) ∨ (¬ p 3950) ∨ (p 3343) :=
  ElevenRUP.step122299 (p 2132) (p 2252) (p 2470) (p 2655) (p 2750) (p 2753) (p 2870) (p 3083) (p 3246) (p 3343) (p 3950) (p 4440) (derived106345 p h) (derived89516 p h)

theorem derived122300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (p 3343) ∨ (p 2651) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (p 3276) ∨ (¬ p 5119) :=
  ElevenRUP.step122300 (p 2254) (p 2651) (p 3276) (p 3343) (p 3399) (p 3527) (p 3941) (p 5119) (derived105366 p h) (derived89517 p h)

theorem derived122303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (p 3343) ∨ (¬ p 5119) ∨ (¬ p 3093) ∨ (p 3276) ∨ (p 2651) ∨ (¬ p 3063) :=
  ElevenRUP.step122303 (p 2254) (p 2651) (p 3063) (p 3093) (p 3276) (p 3343) (p 3979) (p 5119) (derived105366 p h) (derived89523 p h)

theorem derived122304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4636) ∨ (p 3343) ∨ (¬ p 2911) ∨ (¬ p 2437) :=
  ElevenRUP.step122304 (p 2437) (p 2911) (p 3343) (p 4636) (p 4666) (derived105658 p h) (derived89529 p h)

theorem derived122309 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (¬ p 3434) ∨ (p 2295) ∨ (p 2241) ∨ (p 3246) ∨ (p 2641) :=
  ElevenRUP.step122309 (p 2241) (p 2295) (p 2641) (p 3246) (p 3425) (p 3434) (p 4556) (p 4733) (derived105430 p h) (derived105399 p h) (derived89562 p h)

theorem derived122310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 3051) ∨ (p 3246) ∨ (¬ p 3587) :=
  ElevenRUP.step122310 (p 2140) (p 3051) (p 3246) (p 3434) (p 3587) (derived105364 p h) (derived89563 p h)

theorem derived122311 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 3379) ∨ (p 3425) ∨ (¬ p 3434) ∨ (p 2396) ∨ (p 2427) :=
  ElevenRUP.step122311 (p 2396) (p 2406) (p 2427) (p 3379) (p 3425) (p 3434) (p 4559) (p 4733) (derived105430 p h) (derived105701 p h) (derived89570 p h)

theorem derived122312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 4169) ∨ (¬ p 2563) ∨ (p 2417) ∨ (¬ p 2441) :=
  ElevenRUP.step122312 (p 2417) (p 2441) (p 2563) (p 3434) (p 4169) (p 4555) (derived105542 p h) (derived89574 p h)

theorem derived122318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5085) ∨ (¬ p 3434) ∨ (¬ p 3347) ∨ (p 2417) ∨ (p 3389) :=
  ElevenRUP.step122318 (p 2417) (p 3347) (p 3389) (p 3434) (p 5085) (p 5214) (derived105492 p h) (derived89586 p h)

theorem derived122320 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 4777) ∨ (¬ p 2761) ∨ (¬ p 2509) ∨ (¬ p 3434) ∨ (¬ p 2807) ∨ (p 3379) ∨ (¬ p 5123) :=
  ElevenRUP.step122320 (p 2248) (p 2509) (p 2761) (p 2807) (p 3379) (p 3434) (p 4149) (p 4777) (p 5123) (derived105365 p h) (derived89599 p h)

theorem derived122322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 2717) ∨ (p 2449) ∨ (¬ p 2911) :=
  ElevenRUP.step122322 (p 2449) (p 2717) (p 2911) (p 3434) (p 4327) (derived105381 p h) (derived89607 p h)

theorem derived122323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 2707) ∨ (p 3083) ∨ (p 2528) ∨ (¬ p 2608) ∨ (p 2651) ∨ (¬ p 3950) :=
  ElevenRUP.step122323 (p 2254) (p 2528) (p 2608) (p 2651) (p 2707) (p 3083) (p 3434) (p 3950) (derived105366 p h) (derived89609 p h)

theorem derived122324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5015) ∨ (¬ p 3434) ∨ (¬ p 3146) ∨ (p 2307) ∨ (¬ p 3156) ∨ (p 2396) ∨ (p 2717) ∨ (¬ p 2946) :=
  ElevenRUP.step122324 (p 2248) (p 2307) (p 2396) (p 2717) (p 2946) (p 3146) (p 3156) (p 3434) (p 5015) (derived105365 p h) (derived89615 p h)

theorem derived122325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 2707) ∨ (¬ p 2608) ∨ (p 2553) ∨ (p 2177) ∨ (p 2573) :=
  ElevenRUP.step122325 (p 2177) (p 2553) (p 2573) (p 2608) (p 2707) (p 3434) (p 4668) (p 5193) (derived105414 p h) (derived105488 p h) (derived89616 p h)

theorem derived122327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (p 2717) ∨ (¬ p 4443) ∨ (p 3146) :=
  ElevenRUP.step122327 (p 2717) (p 3146) (p 3434) (p 4443) (p 4902) (derived105456 p h) (derived89621 p h)

theorem derived122330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 2707) ∨ (¬ p 3950) ∨ (p 3146) ∨ (p 2230) ∨ (p 2373) ∨ (¬ p 2608) :=
  ElevenRUP.step122330 (p 2230) (p 2373) (p 2608) (p 2707) (p 3146) (p 3434) (p 3950) (p 5193) (derived105488 p h) (derived89630 p h)

theorem derived122335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3434) ∨ (¬ p 2707) ∨ (p 2284) ∨ (p 3125) ∨ (¬ p 2608) ∨ (p 2946) :=
  ElevenRUP.step122335 (p 2254) (p 2284) (p 2608) (p 2707) (p 2946) (p 3125) (p 3434) (p 4625) (derived105366 p h) (derived106455 p h) (derived89640 p h)

theorem derived122338 (p : Nat → Prop) (h : Inputs p) :
    (p 3516) ∨ (¬ p 2341) ∨ (p 2881) ∨ (¬ p 2396) :=
  ElevenRUP.step122338 (p 2341) (p 2396) (p 2881) (p 3516) (p 4556) (derived105399 p h) (derived89654 p h)

theorem derived122339 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2417) ∨ (p 3516) ∨ (p 2881) :=
  ElevenRUP.step122339 (p 2341) (p 2417) (p 2881) (p 3516) (p 4647) (derived105412 p h) (derived89655 p h)

theorem derived122341 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (¬ p 2341) ∨ (p 2881) ∨ (p 2427) :=
  ElevenRUP.step122341 (p 2341) (p 2427) (p 2881) (p 4539) (p 4988) (derived105395 p h) (derived89659 p h)

theorem derived122344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3955) ∨ (p 2363) ∨ (¬ p 2459) :=
  ElevenRUP.step122344 (p 2321) (p 2341) (p 2363) (p 2459) (p 3955) (derived105369 p h) (derived89671 p h)

theorem derived122346 (p : Nat → Prop) (h : Inputs p) :
    (p 3201) ∨ (¬ p 2341) ∨ (p 2911) :=
  ElevenRUP.step122346 (p 2341) (p 2911) (p 3201) (p 4730) (derived106074 p h) (derived89683 p h)

theorem derived122348 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2341) ∨ (¬ p 4172) ∨ (p 2911) ∨ (¬ p 4988) :=
  ElevenRUP.step122348 (p 2341) (p 2911) (p 3389) (p 4172) (p 4988) (p 5193) (derived105488 p h) (derived89689 p h)

theorem derived122352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4138) ∨ (¬ p 2274) ∨ (p 2187) ∨ (¬ p 2341) :=
  ElevenRUP.step122352 (p 2187) (p 2274) (p 2321) (p 2341) (p 4138) (derived105369 p h) (derived89699 p h)

theorem derived122353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 3193) ∨ (p 3379) ∨ (¬ p 2264) ∨ (¬ p 2807) ∨ (¬ p 5119) ∨ (p 3276) :=
  ElevenRUP.step122353 (p 2248) (p 2264) (p 2807) (p 3193) (p 3276) (p 3379) (p 3941) (p 5119) (derived105365 p h) (derived89713 p h)

theorem derived122354 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3941) ∨ (¬ p 3032) ∨ (¬ p 3527) ∨ (p 2727) ∨ (¬ p 2662) ∨ (¬ p 2807) ∨ (p 3276) ∨ (¬ p 3346) ∨ (¬ p 5119) :=
  ElevenRUP.step122354 (p 2255) (p 2662) (p 2727) (p 2807) (p 3032) (p 3276) (p 3346) (p 3527) (p 3941) (p 5119) (derived105367 p h) (derived89717 p h)

theorem derived122358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (p 2807) ∨ (¬ p 2298) ∨ (¬ p 2668) :=
  ElevenRUP.step122358 (p 2298) (p 2331) (p 2668) (p 2807) (p 4405) (derived105512 p h) (derived89731 p h)

theorem derived122359 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3873) ∨ (¬ p 2946) ∨ (¬ p 2284) ∨ (¬ p 2274) ∨ (¬ p 4477) ∨ (¬ p 3537) ∨ (p 2707) ∨ (p 2098) :=
  ElevenRUP.step122359 (p 2098) (p 2248) (p 2274) (p 2284) (p 2707) (p 2946) (p 3537) (p 3873) (p 4477) (derived105365 p h) (derived89742 p h)

theorem derived122361 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (p 2417) ∨ (¬ p 2608) ∨ (¬ p 3537) ∨ (p 2437) ∨ (¬ p 3609) :=
  ElevenRUP.step122361 (p 2254) (p 2417) (p 2437) (p 2608) (p 2651) (p 3537) (p 3609) (p 4669) (derived105366 p h) (derived105415 p h) (derived89752 p h)

theorem derived122364 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (¬ p 3609) ∨ (¬ p 2608) ∨ (¬ p 3537) ∨ (p 2274) ∨ (p 2396) :=
  ElevenRUP.step122364 (p 2156) (p 2274) (p 2396) (p 2608) (p 3537) (p 3609) (p 4669) (derived105415 p h) (derived89762 p h)

theorem derived122365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3537) ∨ (p 2177) ∨ (p 2573) ∨ (¬ p 4802) ∨ (p 2737) ∨ (¬ p 3589) ∨ (p 2553) :=
  ElevenRUP.step122365 (p 2177) (p 2553) (p 2573) (p 2696) (p 2737) (p 3537) (p 3589) (p 4802) (p 5193) (derived105488 p h) (derived89763 p h)

theorem derived122366 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (¬ p 2696) ∨ (¬ p 3537) ∨ (p 3367) :=
  ElevenRUP.step122366 (p 2098) (p 2696) (p 3367) (p 3537) (p 4749) (derived105432 p h) (derived89771 p h)

theorem derived122370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (¬ p 3537) ∨ (p 3389) ∨ (¬ p 2608) ∨ (p 2459) ∨ (p 2911) :=
  ElevenRUP.step122370 (p 2459) (p 2608) (p 2911) (p 3389) (p 3537) (p 4019) (p 5122) (p 5193) (derived105488 p h) (derived105483 p h) (derived89782 p h)

theorem derived122371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (¬ p 3537) ∨ (p 2573) ∨ (¬ p 5119) ∨ (p 3461) ∨ (¬ p 2608) ∨ (p 3564) :=
  ElevenRUP.step122371 (p 2573) (p 2608) (p 3461) (p 3537) (p 3564) (p 4019) (p 5119) (p 5193) (derived105488 p h) (derived89783 p h)

theorem derived122372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (p 2230) ∨ (¬ p 5119) ∨ (¬ p 3537) ∨ (p 2982) ∨ (¬ p 2608) ∨ (¬ p 4322) :=
  ElevenRUP.step122372 (p 2230) (p 2608) (p 2982) (p 3537) (p 4019) (p 4322) (p 5119) (p 5193) (derived105488 p h) (derived89785 p h)

theorem derived122377 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (¬ p 2449) ∨ (¬ p 4357) ∨ (p 3434) :=
  ElevenRUP.step122377 (p 2449) (p 2807) (p 3434) (p 4357) (p 4790) (derived106424 p h) (derived89812 p h)

theorem derived122379 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3527) ∨ (¬ p 2807) ∨ (¬ p 4357) ∨ (¬ p 3032) :=
  ElevenRUP.step122379 (p 2717) (p 2807) (p 3032) (p 3527) (p 4357) (p 4790) (derived106424 p h) (derived89819 p h)

theorem derived122381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4066) ∨ (¬ p 4357) ∨ (p 2717) ∨ (p 2996) ∨ (¬ p 2341) :=
  ElevenRUP.step122381 (p 2341) (p 2717) (p 2751) (p 2996) (p 4066) (p 4357) (derived106343 p h) (derived89823 p h)

theorem derived122382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4357) ∨ (¬ p 3687) ∨ (p 2598) ∨ (p 3516) ∨ (¬ p 3366) ∨ (¬ p 3631) ∨ (¬ p 3959) :=
  ElevenRUP.step122382 (p 2598) (p 3366) (p 3516) (p 3631) (p 3687) (p 3959) (p 4357) (p 4749) (derived105432 p h) (derived89830 p h)

theorem derived122383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2210) ∨ (¬ p 3461) ∨ (¬ p 3246) ∨ (¬ p 3746) ∨ (p 2573) ∨ (p 3276) :=
  ElevenRUP.step122383 (p 2210) (p 2573) (p 2891) (p 3246) (p 3276) (p 3461) (p 3746) (p 4625) (p 5193) (derived105488 p h) (derived106455 p h) (derived89843 p h)

theorem derived122385 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4399) ∨ (¬ p 5612) ∨ (¬ p 4353) ∨ (¬ p 3051) ∨ (¬ p 2761) ∨ (p 3449) ∨ (¬ p 3519) ∨ (¬ p 3246) ∨ (¬ p 2608) ∨ (¬ p 5123) :=
  ElevenRUP.step122385 (p 2608) (p 2761) (p 3051) (p 3246) (p 3449) (p 3519) (p 4353) (p 4376) (p 4399) (p 5123) (p 5612) (derived106320 p h) (derived89855 p h)

theorem derived122390 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 5612) ∨ (¬ p 4353) ∨ (¬ p 2449) ∨ (¬ p 2761) ∨ (¬ p 2246) ∨ (¬ p 2807) ∨ (¬ p 2608) ∨ (¬ p 5123) :=
  ElevenRUP.step122390 (p 2246) (p 2449) (p 2608) (p 2744) (p 2761) (p 2807) (p 3449) (p 4353) (p 5123) (p 5612) (derived106503 p h) (derived89864 p h)

theorem derived122391 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4364) ∨ (¬ p 5612) ∨ (p 2598) ∨ (¬ p 2110) ∨ (¬ p 3998) :=
  ElevenRUP.step122391 (p 2110) (p 2598) (p 3998) (p 4364) (p 4749) (p 5612) (derived105432 p h) (derived89870 p h)

theorem derived122392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3115) ∨ (¬ p 2598) ∨ (p 2098) ∨ (¬ p 5612) ∨ (¬ p 2811) ∨ (¬ p 2946) ∨ (¬ p 5123) :=
  ElevenRUP.step122392 (p 2098) (p 2598) (p 2811) (p 2946) (p 3115) (p 3680) (p 4752) (p 5123) (p 5612) (derived105434 p h) (derived89873 p h)

theorem derived122394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 2911) ∨ (¬ p 2459) ∨ (p 3449) ∨ (¬ p 4353) ∨ (¬ p 3519) ∨ (¬ p 5612) ∨ (¬ p 2608) :=
  ElevenRUP.step122394 (p 2459) (p 2608) (p 2911) (p 3389) (p 3449) (p 3519) (p 4353) (p 4376) (p 5118) (p 5612) (derived106320 p h) (derived105482 p h) (derived89875 p h)

theorem derived122395 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5612) ∨ (¬ p 2807) ∨ (¬ p 2449) ∨ (p 2608) ∨ (p 3537) ∨ (¬ p 2761) ∨ (¬ p 5123) :=
  ElevenRUP.step122395 (p 2248) (p 2449) (p 2608) (p 2761) (p 2807) (p 3537) (p 5123) (p 5612) (derived105365 p h) (derived89876 p h)

theorem derived122397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 3125) ∨ (¬ p 2742) ∨ (¬ p 5612) ∨ (p 2098) ∨ (¬ p 2598) ∨ (¬ p 2156) ∨ (¬ p 2958) ∨ (¬ p 2246) ∨ (¬ p 5123) :=
  ElevenRUP.step122397 (p 2098) (p 2156) (p 2246) (p 2598) (p 2742) (p 2958) (p 3125) (p 3461) (p 4752) (p 5123) (p 5612) (derived105434 p h) (derived89881 p h)

theorem derived122398 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 5612) ∨ (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 2696) ∨ (¬ p 3759) ∨ (p 2098) ∨ (¬ p 5123) :=
  ElevenRUP.step122398 (p 2098) (p 2230) (p 2696) (p 2982) (p 3680) (p 3759) (p 4749) (p 5123) (p 5612) (derived105432 p h) (derived89882 p h)

theorem derived122401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5612) ∨ (p 2098) ∨ (¬ p 2417) ∨ (¬ p 2696) ∨ (¬ p 2761) ∨ (¬ p 3759) ∨ (¬ p 3389) ∨ (¬ p 5123) :=
  ElevenRUP.step122401 (p 2098) (p 2417) (p 2696) (p 2761) (p 3389) (p 3759) (p 4749) (p 5123) (p 5612) (derived105432 p h) (derived89890 p h)

theorem derived122402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 5612) ∨ (p 2608) ∨ (¬ p 2230) ∨ (¬ p 2982) ∨ (p 3537) ∨ (¬ p 5123) :=
  ElevenRUP.step122402 (p 2230) (p 2608) (p 2982) (p 3537) (p 3680) (p 5123) (p 5190) (p 5612) (derived105487 p h) (derived89891 p h)

theorem derived122404 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5612) ∨ (¬ p 3461) ∨ (¬ p 5123) ∨ (¬ p 3323) ∨ (p 2098) ∨ (¬ p 2331) ∨ (¬ p 2742) ∨ (¬ p 2246) ∨ (¬ p 2598) :=
  ElevenRUP.step122404 (p 2098) (p 2246) (p 2331) (p 2598) (p 2742) (p 3323) (p 3461) (p 4752) (p 5123) (p 5612) (derived105434 p h) (derived89893 p h)

theorem derived122407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3276) ∨ (¬ p 5612) ∨ (¬ p 2651) ∨ (¬ p 2608) ∨ (¬ p 2246) ∨ (p 3449) ∨ (¬ p 4353) ∨ (¬ p 5123) :=
  ElevenRUP.step122407 (p 2246) (p 2608) (p 2651) (p 2744) (p 3276) (p 3343) (p 3449) (p 4353) (p 5123) (p 5612) (derived106503 p h) (derived89896 p h)

theorem derived122412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3819) ∨ (¬ p 2341) ∨ (p 2696) ∨ (p 3527) ∨ (¬ p 4030) ∨ (¬ p 2926) :=
  ElevenRUP.step122412 (p 2341) (p 2696) (p 2926) (p 3527) (p 3819) (p 4030) (p 4752) (derived105434 p h) (derived89906 p h)

theorem derived122415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3819) ∨ (p 3379) ∨ (¬ p 3434) ∨ (¬ p 2341) ∨ (p 3564) ∨ (p 2717) ∨ (p 2493) :=
  ElevenRUP.step122415 (p 2341) (p 2493) (p 2717) (p 3379) (p 3434) (p 3564) (p 3819) (p 4625) (p 4733) (derived105430 p h) (derived106455 p h) (derived89911 p h)

theorem derived122417 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 2475) ∨ (¬ p 2518) ∨ (¬ p 3177) ∨ (¬ p 2630) :=
  ElevenRUP.step122417 (p 2475) (p 2518) (p 2630) (p 3005) (p 3177) (p 4814) (derived105440 p h) (derived89919 p h)

theorem derived122422 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2951) ∨ (p 4149) ∨ (¬ p 5160) ∨ (¬ p 2220) ∨ (¬ p 3136) ∨ (¬ p 3146) ∨ (¬ p 3358) ∨ (p 2651) ∨ (¬ p 3683) :=
  ElevenRUP.step122422 (p 2220) (p 2651) (p 2951) (p 3136) (p 3146) (p 3358) (p 3683) (p 4149) (p 5118) (p 5160) (derived105482 p h) (derived89928 p h)

theorem derived122423 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (p 3083) ∨ (¬ p 3434) ∨ (p 3425) ∨ (p 2651) ∨ (¬ p 2761) ∨ (¬ p 5123) :=
  ElevenRUP.step122423 (p 2651) (p 2761) (p 3083) (p 3425) (p 3434) (p 4149) (p 4789) (p 5123) (derived105646 p h) (derived89930 p h)

theorem derived122424 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 3680) ∨ (p 3083) ∨ (p 2651) ∨ (¬ p 3105) ∨ (¬ p 2132) ∨ (¬ p 5123) :=
  ElevenRUP.step122424 (p 2132) (p 2651) (p 3083) (p 3105) (p 3680) (p 4149) (p 4789) (p 5123) (derived105646 p h) (derived89931 p h)

theorem derived122425 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 4149) ∨ (p 3083) ∨ (¬ p 2252) ∨ (¬ p 3105) ∨ (p 2651) ∨ (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 5123) :=
  ElevenRUP.step122425 (p 2132) (p 2252) (p 2651) (p 2750) (p 2753) (p 3083) (p 3105) (p 3680) (p 4149) (p 5123) (derived106345 p h) (derived89932 p h)

theorem derived122427 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (¬ p 3680) ∨ (¬ p 2972) ∨ (p 2651) ∨ (p 3083) ∨ (¬ p 5123) ∨ (¬ p 2210) :=
  ElevenRUP.step122427 (p 2210) (p 2254) (p 2651) (p 2972) (p 3083) (p 3680) (p 4149) (p 5123) (derived105366 p h) (derived89936 p h)

theorem derived122431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 4149) ∨ (p 2651) ∨ (¬ p 2641) ∨ (¬ p 3461) ∨ (¬ p 3323) ∨ (¬ p 3487) ∨ (¬ p 5123) :=
  ElevenRUP.step122431 (p 2249) (p 2509) (p 2641) (p 2651) (p 3323) (p 3461) (p 3487) (p 4149) (p 5123) (derived106513 p h) (derived89950 p h)

theorem derived122435 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (p 4149) ∨ (¬ p 4121) ∨ (p 3422) ∨ (¬ p 3683) ∨ (¬ p 4607) :=
  ElevenRUP.step122435 (p 3422) (p 3683) (p 4009) (p 4121) (p 4149) (p 4607) (p 4715) (derived105423 p h) (derived89965 p h)

theorem derived122436 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (p 4149) ∨ (p 3083) ∨ (¬ p 3461) ∨ (p 2651) ∨ (¬ p 3093) ∨ (¬ p 5123) :=
  ElevenRUP.step122436 (p 2254) (p 2651) (p 3083) (p 3093) (p 3319) (p 3461) (p 4149) (p 5123) (derived105366 p h) (derived89966 p h)

theorem derived122437 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 4149) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 2829) ∨ (p 3083) ∨ (¬ p 3461) ∨ (¬ p 5123) :=
  ElevenRUP.step122437 (p 2252) (p 2651) (p 2750) (p 2829) (p 3083) (p 3461) (p 3483) (p 4149) (p 5123) (derived106345 p h) (derived89972 p h)

theorem derived122441 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (p 3641) ∨ (¬ p 2156) ∨ (¬ p 3370) ∨ (¬ p 2363) ∨ (¬ p 3366) ∨ (p 2598) ∨ (¬ p 2187) :=
  ElevenRUP.step122441 (p 2156) (p 2187) (p 2363) (p 2598) (p 3366) (p 3370) (p 3641) (p 4149) (p 4377) (p 5118) (derived106170 p h) (derived105482 p h) (derived89980 p h)

theorem derived122444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 4149) ∨ (¬ p 3115) ∨ (¬ p 2509) ∨ (¬ p 2946) ∨ (p 3379) ∨ (¬ p 5123) :=
  ElevenRUP.step122444 (p 2248) (p 2509) (p 2946) (p 3115) (p 3379) (p 3680) (p 4149) (p 5123) (derived105365 p h) (derived89983 p h)

theorem derived122446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (p 4149) ∨ (¬ p 2156) ∨ (¬ p 3370) ∨ (p 3083) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 4236) ∨ (p 2651) ∨ (¬ p 5123) :=
  ElevenRUP.step122446 (p 2156) (p 2651) (p 3083) (p 3125) (p 3366) (p 3370) (p 3461) (p 4149) (p 4236) (p 4377) (p 5123) (derived106170 p h) (derived89988 p h)

theorem derived122447 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 4149) ∨ (p 3641) ∨ (¬ p 3115) ∨ (p 2598) ∨ (¬ p 2946) ∨ (¬ p 5123) :=
  ElevenRUP.step122447 (p 2598) (p 2946) (p 3115) (p 3641) (p 3680) (p 4149) (p 4786) (p 5123) (derived106425 p h) (derived89989 p h)

theorem derived122450 (p : Nat → Prop) (h : Inputs p) :
    (p 4149) ∨ (p 2598) ∨ (p 3641) ∨ (¬ p 3323) ∨ (¬ p 2331) ∨ (¬ p 3461) ∨ (¬ p 5123) :=
  ElevenRUP.step122450 (p 2331) (p 2598) (p 3323) (p 3461) (p 3641) (p 4149) (p 4786) (p 5123) (derived106425 p h) (derived90005 p h)

theorem derived122451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4403) ∨ (¬ p 5590) ∨ (¬ p 2417) ∨ (¬ p 4443) ∨ (p 2911) :=
  ElevenRUP.step122451 (p 2417) (p 2911) (p 4403) (p 4443) (p 5118) (p 5590) (derived105482 p h) (derived90018 p h)

theorem derived122452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4403) ∨ (¬ p 3579) ∨ (p 2264) ∨ (¬ p 2417) ∨ (¬ p 5590) ∨ (¬ p 4443) :=
  ElevenRUP.step122452 (p 2264) (p 2417) (p 3579) (p 4403) (p 4443) (p 5118) (p 5590) (derived105482 p h) (derived90026 p h)

theorem derived122456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3998) ∨ (p 3189) ∨ (¬ p 5600) ∨ (¬ p 3178) :=
  ElevenRUP.step122456 (p 2255) (p 3178) (p 3189) (p 3998) (p 5600) (derived105367 p h) (derived90036 p h)

theorem derived122457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3998) ∨ (¬ p 5600) ∨ (p 3166) ∨ (¬ p 5242) :=
  ElevenRUP.step122457 (p 2254) (p 3166) (p 3998) (p 5242) (p 5600) (derived105366 p h) (derived90038 p h)

theorem derived122459 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3370) ∨ (¬ p 3461) ∨ (¬ p 3366) ∨ (p 2696) ∨ (¬ p 3125) ∨ (p 3005) ∨ (¬ p 5600) ∨ (¬ p 5123) :=
  ElevenRUP.step122459 (p 2156) (p 2696) (p 3005) (p 3125) (p 3366) (p 3370) (p 3461) (p 4377) (p 5123) (p 5600) (derived106170 p h) (derived90042 p h)

theorem derived122462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5600) ∨ (¬ p 4238) ∨ (¬ p 3016) ∨ (¬ p 4109) ∨ (¬ p 3998) ∨ (¬ p 3878) :=
  ElevenRUP.step122462 (p 3016) (p 3878) (p 3998) (p 4109) (p 4238) (p 4717) (p 5600) (derived105424 p h) (derived61412 p h)

theorem derived122464 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3519) ∨ (¬ p 2230) ∨ (¬ p 3366) ∨ (p 2696) ∨ (¬ p 2982) ∨ (p 3005) ∨ (¬ p 5600) ∨ (¬ p 5123) :=
  ElevenRUP.step122464 (p 2230) (p 2696) (p 2982) (p 3005) (p 3366) (p 3519) (p 3680) (p 4376) (p 5123) (p 5600) (derived106320 p h) (derived90051 p h)

theorem derived122465 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 5600) ∨ (p 2241) ∨ (¬ p 2156) ∨ (¬ p 3791) ∨ (¬ p 2274) ∨ (¬ p 4521) :=
  ElevenRUP.step122465 (p 2156) (p 2241) (p 2274) (p 3189) (p 3791) (p 4521) (p 5560) (p 5600) (derived106188 p h) (derived90055 p h)

theorem derived122466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (¬ p 5600) ∨ (¬ p 3878) ∨ (¬ p 2590) ∨ (¬ p 3016) :=
  ElevenRUP.step122466 (p 2590) (p 3016) (p 3878) (p 4149) (p 4608) (p 5600) (derived105540 p h) (derived48729 p h)

theorem derived122468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4121) ∨ (¬ p 2509) ∨ (p 2088) ∨ (¬ p 3256) ∨ (¬ p 2481) :=
  ElevenRUP.step122468 (p 2088) (p 2481) (p 2509) (p 3256) (p 4121) (p 4811) (derived105633 p h) (derived90076 p h)

theorem derived122470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3019) ∨ (p 2850) ∨ (p 3564) ∨ (¬ p 2590) ∨ (¬ p 3323) :=
  ElevenRUP.step122470 (p 2590) (p 2850) (p 3019) (p 3323) (p 3564) (p 4750) (derived105433 p h) (derived90083 p h)

theorem derived122472 (p : Nat → Prop) (h : Inputs p) :
    (p 3422) ∨ (p 2230) ∨ (p 2440) ∨ (¬ p 2573) :=
  ElevenRUP.step122472 (p 2230) (p 2440) (p 2573) (p 3422) (p 4750) (derived105433 p h) (derived90085 p h)

theorem derived122473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (p 2850) ∨ (p 2982) ∨ (¬ p 3413) :=
  ElevenRUP.step122473 (p 2850) (p 2982) (p 3115) (p 3413) (p 4750) (derived105433 p h) (derived90087 p h)

theorem derived122476 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (¬ p 2341) ∨ (p 3527) ∨ (¬ p 3545) ∨ (¬ p 4400) :=
  ElevenRUP.step122476 (p 2210) (p 2341) (p 3527) (p 3545) (p 4377) (p 4400) (derived106170 p h) (derived90131 p h)

theorem derived122478 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 3527) ∨ (¬ p 3545) ∨ (¬ p 4400) ∨ (p 3379) :=
  ElevenRUP.step122478 (p 2341) (p 3379) (p 3527) (p 3545) (p 4376) (p 4400) (derived106320 p h) (derived90136 p h)

theorem derived122482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4400) ∨ (¬ p 3367) ∨ (p 3527) ∨ (¬ p 2717) ∨ (¬ p 4781) :=
  ElevenRUP.step122482 (p 2717) (p 3367) (p 3527) (p 4400) (p 4752) (p 4781) (derived105434 p h) (derived90145 p h)

theorem derived122486 (p : Nat → Prop) (h : Inputs p) :
    (p 3631) ∨ (¬ p 3516) ∨ (¬ p 4400) ∨ (¬ p 3545) ∨ (p 3379) :=
  ElevenRUP.step122486 (p 3379) (p 3516) (p 3545) (p 3631) (p 4376) (p 4400) (derived106320 p h) (derived90150 p h)

theorem derived122487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2590) ∨ (¬ p 2187) ∨ (p 2352) ∨ (¬ p 2982) :=
  ElevenRUP.step122487 (p 2187) (p 2352) (p 2590) (p 2982) (p 5046) (derived105472 p h) (derived90197 p h)

theorem derived122488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (p 2352) ∨ (¬ p 2590) :=
  ElevenRUP.step122488 (p 2156) (p 2187) (p 2352) (p 2590) (p 4539) (derived105395 p h) (derived90199 p h)

theorem derived122489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4198) ∨ (¬ p 3483) ∨ (p 3654) ∨ (¬ p 4375) ∨ (¬ p 4031) ∨ (p 3201) :=
  ElevenRUP.step122489 (p 3201) (p 3483) (p 3654) (p 4031) (p 4198) (p 4375) (p 4644) (derived105411 p h) (derived90205 p h)

theorem derived122491 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 3483) ∨ (p 2459) ∨ (¬ p 2829) ∨ (¬ p 2608) ∨ (p 2911) :=
  ElevenRUP.step122491 (p 2459) (p 2608) (p 2829) (p 2911) (p 3389) (p 3483) (p 4330) (p 5193) (derived105488 p h) (derived106329 p h) (derived90215 p h)

theorem derived122493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (p 3516) ∨ (p 2122) :=
  ElevenRUP.step122493 (p 2122) (p 2315) (p 3483) (p 3516) (derived105368 p h) (derived90221 p h)

theorem derived122494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5015) ∨ (¬ p 3483) ∨ (p 3654) ∨ (¬ p 2901) ∨ (p 2819) ∨ (¬ p 2946) ∨ (¬ p 2881) :=
  ElevenRUP.step122494 (p 2248) (p 2819) (p 2881) (p 2901) (p 2946) (p 3483) (p 3654) (p 4503) (p 5015) (derived105365 p h) (derived106530 p h) (derived90222 p h)

theorem derived122496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5503) ∨ (¬ p 3483) ∨ (¬ p 2774) ∨ (p 2437) ∨ (p 2651) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (¬ p 3461) :=
  ElevenRUP.step122496 (p 2252) (p 2437) (p 2651) (p 2750) (p 2753) (p 2774) (p 3461) (p 3483) (p 4831) (p 5503) (derived106345 p h) (derived105445 p h) (derived90226 p h)

theorem derived122497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 2829) ∨ (p 2373) ∨ (p 2230) ∨ (¬ p 2608) ∨ (p 3146) :=
  ElevenRUP.step122497 (p 2230) (p 2373) (p 2608) (p 2829) (p 3146) (p 3483) (p 4330) (p 5193) (derived105488 p h) (derived106329 p h) (derived90235 p h)

theorem derived122502 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 5164) ∨ (p 2598) ∨ (p 2946) ∨ (¬ p 3361) ∨ (p 3156) ∨ (¬ p 5568) ∨ (¬ p 5123) ∨ (¬ p 3619) :=
  ElevenRUP.step122502 (p 2598) (p 2946) (p 3156) (p 3276) (p 3361) (p 3619) (p 4749) (p 5123) (p 5164) (p 5568) (derived105432 p h) (derived90263 p h)

theorem derived122504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3590) ∨ (¬ p 2737) ∨ (p 3379) ∨ (¬ p 2608) :=
  ElevenRUP.step122504 (p 2608) (p 2737) (p 3379) (p 3590) (p 4749) (derived105432 p h) (derived90265 p h)

theorem derived122506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4257) ∨ (¬ p 2737) ∨ (¬ p 3759) ∨ (p 2406) ∨ (¬ p 2230) :=
  ElevenRUP.step122506 (p 2230) (p 2406) (p 2737) (p 3759) (p 4257) (p 4749) (derived105432 p h) (derived90269 p h)

theorem derived122507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 2737) ∨ (¬ p 4257) ∨ (¬ p 2509) :=
  ElevenRUP.step122507 (p 2509) (p 2737) (p 3641) (p 4257) (p 4749) (derived105432 p h) (derived42163 p h)

theorem derived122512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (p 2819) ∨ (¬ p 2331) ∨ (¬ p 2246) ∨ (¬ p 2668) :=
  ElevenRUP.step122512 (p 2246) (p 2331) (p 2668) (p 2751) (p 2819) (p 4841) (derived106343 p h) (derived90286 p h)

theorem derived122513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2786) ∨ (p 2598) ∨ (p 2122) ∨ (¬ p 2307) ∨ (¬ p 4841) :=
  ElevenRUP.step122513 (p 2122) (p 2307) (p 2598) (p 2786) (p 4749) (p 4841) (derived105432 p h) (derived90289 p h)

theorem derived122514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (p 2122) ∨ (¬ p 2331) ∨ (¬ p 2295) :=
  ElevenRUP.step122514 (p 2122) (p 2295) (p 2331) (p 4790) (p 4841) (derived106424 p h) (derived90293 p h)

theorem derived122515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (¬ p 4841) ∨ (¬ p 2641) ∨ (¬ p 2383) ∨ (p 2819) :=
  ElevenRUP.step122515 (p 2383) (p 2641) (p 2751) (p 2819) (p 3567) (p 4841) (derived106343 p h) (derived90294 p h)

theorem derived122517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4841) ∨ (¬ p 4869) ∨ (¬ p 3063) ∨ (p 2819) ∨ (p 3367) :=
  ElevenRUP.step122517 (p 2819) (p 3063) (p 3367) (p 4749) (p 4841) (p 4869) (derived105432 p h) (derived90297 p h)

theorem derived122520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2819) ∨ (¬ p 2383) ∨ (p 2274) :=
  ElevenRUP.step122520 (p 2122) (p 2274) (p 2383) (p 2819) (p 4489) (derived105390 p h) (derived90330 p h)

theorem derived122522 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (p 2417) ∨ (¬ p 2177) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (p 3379) :=
  ElevenRUP.step122522 (p 2122) (p 2177) (p 2417) (p 2774) (p 2922) (p 3379) (p 4666) (p 4733) (derived105430 p h) (derived105658 p h) (derived90342 p h)

theorem derived122525 (p : Nat → Prop) (h : Inputs p) :
    (p 2230) ∨ (¬ p 2829) ∨ (p 2563) ∨ (¬ p 2122) ∨ (¬ p 2608) ∨ (p 2187) :=
  ElevenRUP.step122525 (p 2122) (p 2187) (p 2230) (p 2563) (p 2608) (p 2829) (p 5193) (derived105488 p h) (derived90351 p h)

theorem derived122526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (p 2982) ∨ (p 2406) ∨ (p 3379) ∨ (¬ p 2396) ∨ (¬ p 2774) ∨ (¬ p 2122) :=
  ElevenRUP.step122526 (p 2122) (p 2396) (p 2406) (p 2761) (p 2774) (p 2982) (p 3379) (p 4733) (derived105430 p h) (derived90354 p h)

theorem derived122528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3083) ∨ (¬ p 3950) ∨ (p 2528) ∨ (p 2651) ∨ (¬ p 2829) ∨ (¬ p 2252) ∨ (¬ p 2396) :=
  ElevenRUP.step122528 (p 2122) (p 2252) (p 2396) (p 2528) (p 2651) (p 2750) (p 2829) (p 3083) (p 3950) (derived106345 p h) (derived90359 p h)

theorem derived122530 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2819) ∨ (p 2307) ∨ (¬ p 2651) ∨ (¬ p 2778) ∨ (p 2440) ∨ (¬ p 2373) :=
  ElevenRUP.step122530 (p 2122) (p 2307) (p 2373) (p 2440) (p 2651) (p 2778) (p 2819) (p 4433) (p 4786) (derived106150 p h) (derived106425 p h) (derived90362 p h)

theorem derived122531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2651) ∨ (p 2437) ∨ (p 2911) ∨ (¬ p 2774) ∨ (¬ p 2396) :=
  ElevenRUP.step122531 (p 2122) (p 2396) (p 2437) (p 2651) (p 2774) (p 2911) (p 4668) (p 4789) (derived105414 p h) (derived105646 p h) (derived90364 p h)

theorem derived122532 (p : Nat → Prop) (h : Inputs p) :
    (p 2819) ∨ (¬ p 3575) ∨ (¬ p 2341) ∨ (¬ p 2122) ∨ (¬ p 4138) :=
  ElevenRUP.step122532 (p 2122) (p 2341) (p 2819) (p 3575) (p 4138) (p 4712) (derived105422 p h) (derived90365 p h)

theorem derived122534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2819) ∨ (¬ p 4138) ∨ (¬ p 2881) :=
  ElevenRUP.step122534 (p 2122) (p 2819) (p 2881) (p 4138) (p 4559) (derived105701 p h) (derived90368 p h)

theorem derived122537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 4426) ∨ (p 2630) ∨ (p 2307) ∨ (¬ p 2667) :=
  ElevenRUP.step122537 (p 2122) (p 2307) (p 2630) (p 2667) (p 4426) (p 4975) (derived105464 p h) (derived90374 p h)

theorem derived122539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2651) ∨ (¬ p 2177) ∨ (¬ p 2252) ∨ (p 2437) ∨ (¬ p 2122) ∨ (p 2417) ∨ (¬ p 2753) :=
  ElevenRUP.step122539 (p 2122) (p 2177) (p 2252) (p 2417) (p 2437) (p 2651) (p 2750) (p 2753) (p 2774) (p 4666) (derived106345 p h) (derived105658 p h) (derived90381 p h)

theorem derived122541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (p 3379) ∨ (p 2563) ∨ (p 2406) ∨ (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 2774) :=
  ElevenRUP.step122541 (p 2122) (p 2396) (p 2406) (p 2563) (p 2761) (p 2774) (p 3379) (p 4733) (derived105430 p h) (derived90391 p h)

theorem derived122542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2122) ∨ (¬ p 2778) ∨ (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 2651) ∨ (p 2307) :=
  ElevenRUP.step122542 (p 2122) (p 2246) (p 2307) (p 2528) (p 2651) (p 2744) (p 2778) (p 3083) (p 3366) (p 3917) (p 4604) (derived106503 p h) (derived106293 p h) (derived90392 p h)

theorem derived122544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3661) ∨ (¬ p 2245) ∨ (p 2946) ∨ (¬ p 3146) ∨ (¬ p 2774) ∨ (p 3256) ∨ (¬ p 2122) ∨ (¬ p 2177) :=
  ElevenRUP.step122544 (p 2122) (p 2177) (p 2245) (p 2774) (p 2946) (p 3146) (p 3256) (p 3661) (p 4733) (p 4905) (derived105430 p h) (derived105995 p h) (derived90394 p h)

theorem derived122545 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2373) ∨ (p 2230) ∨ (p 3146) ∨ (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 3950) :=
  ElevenRUP.step122545 (p 2122) (p 2230) (p 2373) (p 2396) (p 2774) (p 3146) (p 3950) (p 4729) (derived105429 p h) (derived90395 p h)

theorem derived122548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4375) ∨ (¬ p 2122) ∨ (p 2553) ∨ (p 3016) :=
  ElevenRUP.step122548 (p 2122) (p 2553) (p 3016) (p 4375) (p 4753) (derived105514 p h) (derived90404 p h)

theorem derived122549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 3115) ∨ (¬ p 2252) ∨ (¬ p 2774) ∨ (¬ p 2122) ∨ (¬ p 4322) ∨ (¬ p 2753) ∨ (p 2946) :=
  ElevenRUP.step122549 (p 2122) (p 2252) (p 2750) (p 2753) (p 2774) (p 2946) (p 3115) (p 3791) (p 4322) (p 4826) (derived106345 p h) (derived105444 p h) (derived90407 p h)

theorem derived122551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3399) ∨ (¬ p 3093) ∨ (¬ p 4427) :=
  ElevenRUP.step122551 (p 2122) (p 3093) (p 3399) (p 4427) (p 4867) (derived106410 p h) (derived90410 p h)

theorem derived122552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 2774) ∨ (¬ p 2241) ∨ (p 3399) ∨ (¬ p 2753) ∨ (¬ p 2177) ∨ (p 2449) ∨ (¬ p 2122) :=
  ElevenRUP.step122552 (p 2122) (p 2177) (p 2241) (p 2449) (p 2750) (p 2753) (p 2774) (p 3032) (p 3399) (p 4666) (derived106345 p h) (derived105658 p h) (derived90411 p h)

theorem derived122553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2122) ∨ (p 3399) ∨ (¬ p 2177) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (p 3631) :=
  ElevenRUP.step122553 (p 2122) (p 2177) (p 2753) (p 2774) (p 3379) (p 3399) (p 3631) (p 4666) (derived105658 p h) (derived90412 p h)

theorem derived122554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3950) ∨ (p 3073) ∨ (¬ p 2241) ∨ (¬ p 2396) ∨ (p 3449) ∨ (¬ p 2753) :=
  ElevenRUP.step122554 (p 2122) (p 2241) (p 2396) (p 2750) (p 2753) (p 2774) (p 3073) (p 3449) (p 3950) (derived106345 p h) (derived90414 p h)

theorem derived122555 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2992) ∨ (¬ p 2122) ∨ (¬ p 2177) ∨ (p 2241) ∨ (¬ p 2774) :=
  ElevenRUP.step122555 (p 2122) (p 2177) (p 2241) (p 2774) (p 2992) (p 3156) (p 4733) (p 4905) (derived105430 p h) (derived105995 p h) (derived90418 p h)

theorem derived122558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2651) ∨ (¬ p 3950) ∨ (¬ p 2396) ∨ (¬ p 2753) ∨ (p 2528) ∨ (p 3083) ∨ (¬ p 2774) ∨ (¬ p 2252) :=
  ElevenRUP.step122558 (p 2122) (p 2252) (p 2396) (p 2528) (p 2651) (p 2750) (p 2753) (p 2774) (p 3083) (p 3950) (derived106345 p h) (derived90422 p h)

theorem derived122561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4342) ∨ (¬ p 3367) ∨ (p 2829) ∨ (¬ p 2573) :=
  ElevenRUP.step122561 (p 2573) (p 2829) (p 3367) (p 4342) (p 4730) (derived106074 p h) (derived90444 p h)

theorem derived122564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 2598) ∨ (¬ p 3590) ∨ (p 2177) ∨ (p 2307) ∨ (p 2829) ∨ (¬ p 2406) ∨ (¬ p 2373) :=
  ElevenRUP.step122564 (p 2177) (p 2307) (p 2373) (p 2406) (p 2598) (p 2785) (p 2829) (p 3590) (p 4902) (derived105456 p h) (derived90450 p h)

theorem derived122565 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3917) ∨ (¬ p 2807) ∨ (¬ p 2459) ∨ (p 2608) ∨ (¬ p 2264) :=
  ElevenRUP.step122565 (p 2248) (p 2264) (p 2459) (p 2608) (p 2807) (p 2829) (p 3917) (p 4604) (derived105365 p h) (derived106293 p h) (derived90454 p h)

theorem derived122566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (¬ p 3917) ∨ (¬ p 4988) ∨ (p 2829) ∨ (¬ p 2341) ∨ (p 2608) ∨ (¬ p 4521) :=
  ElevenRUP.step122566 (p 2341) (p 2608) (p 2829) (p 2881) (p 3246) (p 3917) (p 4521) (p 4625) (p 4988) (derived106455 p h) (derived90455 p h)

theorem derived122569 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2911) ∨ (¬ p 2651) ∨ (p 2608) ∨ (¬ p 2437) ∨ (p 2819) :=
  ElevenRUP.step122569 (p 2248) (p 2437) (p 2608) (p 2651) (p 2819) (p 2829) (p 2911) (p 4503) (derived105365 p h) (derived106530 p h) (derived90470 p h)

theorem derived122570 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2122) ∨ (¬ p 2651) ∨ (¬ p 3016) ∨ (p 2608) ∨ (¬ p 2352) :=
  ElevenRUP.step122570 (p 2122) (p 2248) (p 2352) (p 2608) (p 2651) (p 2829) (p 3016) (p 4405) (derived105512 p h) (derived105365 p h) (derived90471 p h)

theorem derived122571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2829) ∨ (p 2241) ∨ (¬ p 3589) :=
  ElevenRUP.step122571 (p 2241) (p 2744) (p 2774) (p 2829) (p 3589) (derived106503 p h) (derived90472 p h)

theorem derived122573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3917) ∨ (¬ p 2911) ∨ (p 2829) ∨ (p 2608) ∨ (¬ p 3389) ∨ (¬ p 2459) :=
  ElevenRUP.step122573 (p 2459) (p 2608) (p 2829) (p 2911) (p 3389) (p 3917) (p 4604) (p 5190) (derived106293 p h) (derived105487 p h) (derived90487 p h)

theorem derived122575 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2819) ∨ (¬ p 2881) ∨ (¬ p 2230) ∨ (p 2608) ∨ (¬ p 2427) :=
  ElevenRUP.step122575 (p 2230) (p 2427) (p 2608) (p 2819) (p 2829) (p 2881) (p 4503) (p 5190) (derived106530 p h) (derived105487 p h) (derived90497 p h)

theorem derived122576 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2807) ∨ (p 2829) ∨ (p 2608) ∨ (p 2122) ∨ (¬ p 2449) :=
  ElevenRUP.step122576 (p 2122) (p 2248) (p 2449) (p 2608) (p 2807) (p 2829) (p 3246) (p 4556) (derived105365 p h) (derived105399 p h) (derived90503 p h)

theorem derived122577 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (p 2608) ∨ (¬ p 2807) ∨ (p 2122) ∨ (p 2881) ∨ (¬ p 2264) :=
  ElevenRUP.step122577 (p 2122) (p 2248) (p 2264) (p 2608) (p 2807) (p 2829) (p 2881) (p 4556) (derived105365 p h) (derived105399 p h) (derived90505 p h)

theorem derived122578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2785) ∨ (¬ p 2696) ∨ (p 2177) ∨ (¬ p 2992) ∨ (¬ p 2742) ∨ (¬ p 3156) ∨ (p 2307) ∨ (p 2829) :=
  ElevenRUP.step122578 (p 2177) (p 2307) (p 2696) (p 2742) (p 2785) (p 2829) (p 2992) (p 3156) (p 4902) (derived105456 p h) (derived90506 p h)

theorem derived122581 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (p 2264) ∨ (p 2807) ∨ (¬ p 2707) ∨ (¬ p 2881) ∨ (¬ p 3589) ∨ (¬ p 4895) :=
  ElevenRUP.step122581 (p 2254) (p 2264) (p 2707) (p 2774) (p 2807) (p 2829) (p 2881) (p 3589) (p 4895) (derived105366 p h) (derived90513 p h)

theorem derived122582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3917) ∨ (p 2829) ∨ (¬ p 3246) ∨ (p 2608) ∨ (¬ p 2946) :=
  ElevenRUP.step122582 (p 2248) (p 2608) (p 2829) (p 2901) (p 2946) (p 3246) (p 3917) (p 4625) (derived105365 p h) (derived106455 p h) (derived90523 p h)

theorem derived122583 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (¬ p 3367) ∨ (p 2696) :=
  ElevenRUP.step122583 (p 2696) (p 2774) (p 2829) (p 3367) (p 4752) (derived105434 p h) (derived90529 p h)

theorem derived122585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4181) ∨ (¬ p 3449) ∨ (p 2241) ∨ (p 2829) ∨ (¬ p 5119) ∨ (p 3461) ∨ (¬ p 3917) :=
  ElevenRUP.step122585 (p 2241) (p 2744) (p 2829) (p 3449) (p 3461) (p 3917) (p 4181) (p 5119) (derived106503 p h) (derived90537 p h)

theorem derived122588 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 4030) ∨ (¬ p 3379) ∨ (p 2608) :=
  ElevenRUP.step122588 (p 2608) (p 2829) (p 3379) (p 4030) (p 5221) (derived105796 p h) (derived90548 p h)

theorem derived122590 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3917) ∨ (p 2608) ∨ (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 2651) :=
  ElevenRUP.step122590 (p 2248) (p 2528) (p 2608) (p 2651) (p 2829) (p 3083) (p 3917) (p 4604) (derived105365 p h) (derived106293 p h) (derived90562 p h)

theorem derived122593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (p 2829) ∨ (p 2608) ∨ (¬ p 3146) ∨ (¬ p 4521) ∨ (p 2819) ∨ (p 2459) :=
  ElevenRUP.step122593 (p 2220) (p 2459) (p 2608) (p 2819) (p 2829) (p 3146) (p 4503) (p 4521) (derived106530 p h) (derived90570 p h)

theorem derived122594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (p 2829) ∨ (¬ p 2946) ∨ (p 2608) ∨ (p 2122) ∨ (¬ p 2187) :=
  ElevenRUP.step122594 (p 2122) (p 2187) (p 2248) (p 2284) (p 2608) (p 2829) (p 2946) (p 4405) (derived105512 p h) (derived105365 p h) (derived90572 p h)

theorem derived122595 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (¬ p 4475) ∨ (p 2553) :=
  ElevenRUP.step122595 (p 2553) (p 2707) (p 2829) (p 4475) (p 5225) (derived105495 p h) (derived90585 p h)

theorem derived122600 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2132) ∨ (p 3399) ∨ (¬ p 3589) :=
  ElevenRUP.step122600 (p 2132) (p 2839) (p 3399) (p 3589) (p 4793) (derived105438 p h) (derived90626 p h)

theorem derived122601 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2132) ∨ (¬ p 3589) ∨ (p 3379) :=
  ElevenRUP.step122601 (p 2132) (p 2839) (p 3379) (p 3589) (p 4376) (derived106320 p h) (derived90634 p h)

theorem derived122605 (p : Nat → Prop) (h : Inputs p) :
    (p 2839) ∨ (¬ p 2707) ∨ (¬ p 2132) ∨ (¬ p 3589) ∨ (p 2264) ∨ (¬ p 2177) ∨ (¬ p 4473) ∨ (p 2807) :=
  ElevenRUP.step122605 (p 2132) (p 2177) (p 2254) (p 2264) (p 2707) (p 2807) (p 2839) (p 3589) (p 4473) (derived105366 p h) (derived90648 p h)

theorem derived122608 (p : Nat → Prop) (h : Inputs p) :
    (p 2807) ∨ (¬ p 2132) ∨ (p 2982) ∨ (¬ p 3589) ∨ (¬ p 3105) ∨ (p 2264) ∨ (p 2459) ∨ (¬ p 2563) :=
  ElevenRUP.step122608 (p 2132) (p 2254) (p 2264) (p 2459) (p 2563) (p 2807) (p 2982) (p 3105) (p 3589) (derived105366 p h) (derived90652 p h)

theorem derived122609 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 2911) ∨ (¬ p 5197) ∨ (p 2341) ∨ (¬ p 2132) ∨ (¬ p 3125) ∨ (¬ p 2860) :=
  ElevenRUP.step122609 (p 2132) (p 2341) (p 2417) (p 2860) (p 2911) (p 3125) (p 4621) (p 4729) (p 5197) (derived105407 p h) (derived105429 p h) (derived90653 p h)

theorem derived122611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2651) ∨ (¬ p 2881) ∨ (p 2417) ∨ (¬ p 2870) ∨ (p 2437) :=
  ElevenRUP.step122611 (p 2132) (p 2417) (p 2437) (p 2651) (p 2870) (p 2881) (p 4666) (p 4789) (derived105658 p h) (derived105646 p h) (derived90655 p h)

theorem derived122612 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (p 2651) ∨ (¬ p 3146) ∨ (p 2437) ∨ (¬ p 2619) ∨ (¬ p 2132) :=
  ElevenRUP.step122612 (p 2132) (p 2417) (p 2437) (p 2619) (p 2651) (p 3146) (p 4669) (p 4789) (derived105415 p h) (derived105646 p h) (derived90656 p h)

theorem derived122613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2860) ∨ (¬ p 3379) ∨ (¬ p 2927) ∨ (p 2911) ∨ (¬ p 2187) ∨ (p 3399) :=
  ElevenRUP.step122613 (p 2132) (p 2187) (p 2753) (p 2860) (p 2911) (p 2927) (p 3379) (p 3399) (p 4133) (derived105712 p h) (derived90659 p h)

theorem derived122614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2753) ∨ (p 3093) ∨ (¬ p 2132) ∨ (¬ p 3246) ∨ (p 3319) ∨ (¬ p 2241) :=
  ElevenRUP.step122614 (p 2132) (p 2241) (p 2750) (p 2753) (p 2870) (p 3093) (p 3246) (p 3319) (p 4625) (derived106345 p h) (derived106455 p h) (derived90660 p h)

theorem derived122615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (p 3093) ∨ (¬ p 2870) ∨ (p 2363) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 3950) :=
  ElevenRUP.step122615 (p 2132) (p 2363) (p 2870) (p 3093) (p 3246) (p 3923) (p 3950) (p 4733) (derived105430 p h) (derived90663 p h)

theorem derived122616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2870) ∨ (p 3083) ∨ (p 2528) ∨ (¬ p 3246) ∨ (p 2651) ∨ (¬ p 3950) :=
  ElevenRUP.step122616 (p 2132) (p 2528) (p 2651) (p 2870) (p 3083) (p 3246) (p 3950) (p 4789) (derived105646 p h) (derived90664 p h)

theorem derived122617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2132) ∨ (p 2352) ∨ (¬ p 3246) ∨ (p 2573) ∨ (p 2363) ∨ (¬ p 3950) :=
  ElevenRUP.step122617 (p 2132) (p 2352) (p 2363) (p 2573) (p 2870) (p 3246) (p 3950) (p 4729) (derived105429 p h) (derived90665 p h)

theorem derived122618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3166) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (p 3256) ∨ (¬ p 2132) ∨ (¬ p 4438) :=
  ElevenRUP.step122618 (p 2132) (p 2528) (p 2870) (p 2881) (p 3166) (p 3256) (p 4438) (p 4789) (derived105646 p h) (derived90666 p h)

theorem derived122621 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (¬ p 2870) ∨ (¬ p 2753) ∨ (¬ p 3950) ∨ (p 2651) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 2252) ∨ (p 2528) :=
  ElevenRUP.step122621 (p 2132) (p 2252) (p 2528) (p 2651) (p 2750) (p 2753) (p 2870) (p 3083) (p 3246) (p 3950) (derived106345 p h) (derived90669 p h)

theorem derived122622 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2245) ∨ (¬ p 2132) ∨ (p 2363) ∨ (p 2668) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3950) :=
  ElevenRUP.step122622 (p 2132) (p 2245) (p 2331) (p 2363) (p 2668) (p 2870) (p 3246) (p 3950) (p 4733) (derived105430 p h) (derived90670 p h)

theorem derived122630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (p 2493) ∨ (¬ p 2132) ∨ (¬ p 4030) ∨ (p 2598) :=
  ElevenRUP.step122630 (p 2132) (p 2493) (p 2598) (p 3695) (p 4030) (p 4715) (derived105423 p h) (derived90681 p h)

theorem derived122635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (p 3399) ∨ (p 3527) ∨ (¬ p 2132) ∨ (¬ p 5558) ∨ (¬ p 3105) ∨ (¬ p 5123) :=
  ElevenRUP.step122635 (p 2132) (p 3105) (p 3399) (p 3527) (p 3680) (p 4733) (p 5123) (p 5558) (derived105430 p h) (derived90691 p h)

theorem derived122638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3905) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (p 3389) :=
  ElevenRUP.step122638 (p 2132) (p 2870) (p 3389) (p 3905) (p 4647) (derived105412 p h) (derived90709 p h)

theorem derived122639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4342) ∨ (p 2774) ∨ (¬ p 2132) ∨ (¬ p 2870) ∨ (¬ p 3096) :=
  ElevenRUP.step122639 (p 2132) (p 2774) (p 2870) (p 3096) (p 4342) (p 4558) (derived105400 p h) (derived90718 p h)

theorem derived122640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3695) ∨ (p 3201) ∨ (p 2598) ∨ (¬ p 2132) :=
  ElevenRUP.step122640 (p 2132) (p 2598) (p 3201) (p 3695) (p 4644) (derived105411 p h) (derived90721 p h)

theorem derived122641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3695) ∨ (p 3641) ∨ (p 2598) :=
  ElevenRUP.step122641 (p 2132) (p 2598) (p 3641) (p 3695) (p 4608) (derived105540 p h) (derived90722 p h)

theorem derived122642 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (p 2807) ∨ (p 2427) ∨ (¬ p 2132) ∨ (¬ p 2245) ∨ (p 2996) ∨ (¬ p 2870) :=
  ElevenRUP.step122642 (p 2132) (p 2245) (p 2427) (p 2807) (p 2870) (p 2992) (p 2996) (p 4705) (p 4733) (derived105430 p h) (derived106238 p h) (derived90726 p h)

theorem derived122645 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 2753) ∨ (p 2417) ∨ (p 2437) ∨ (¬ p 2860) ∨ (¬ p 3125) :=
  ElevenRUP.step122645 (p 2132) (p 2252) (p 2417) (p 2437) (p 2651) (p 2750) (p 2753) (p 2860) (p 3125) (p 4621) (derived106345 p h) (derived105407 p h) (derived90731 p h)

theorem derived122648 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2132) ∨ (¬ p 2641) ∨ (¬ p 4769) ∨ (¬ p 2245) ∨ (¬ p 2881) ∨ (p 2331) ∨ (¬ p 2870) :=
  ElevenRUP.step122648 (p 2132) (p 2245) (p 2331) (p 2641) (p 2870) (p 2881) (p 3189) (p 4503) (p 4733) (p 4769) (derived105430 p h) (derived106530 p h) (derived90737 p h)

theorem derived122650 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2870) ∨ (p 2668) ∨ (p 2641) ∨ (¬ p 2881) ∨ (¬ p 2132) :=
  ElevenRUP.step122650 (p 2132) (p 2241) (p 2641) (p 2668) (p 2870) (p 2881) (p 4503) (p 4733) (derived105430 p h) (derived106530 p h) (derived90740 p h)

theorem derived122656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2870) ∨ (p 3379) ∨ (p 2528) ∨ (¬ p 3246) ∨ (¬ p 2132) ∨ (¬ p 3950) :=
  ElevenRUP.step122656 (p 2132) (p 2509) (p 2528) (p 2870) (p 3246) (p 3379) (p 3950) (p 4733) (derived105430 p h) (derived90755 p h)

theorem derived122657 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2509) ∨ (p 2528) ∨ (p 3379) ∨ (¬ p 2860) ∨ (¬ p 3125) :=
  ElevenRUP.step122657 (p 2132) (p 2509) (p 2528) (p 2860) (p 3125) (p 3379) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived90764 p h)

theorem derived122658 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2598) ∨ (¬ p 3695) ∨ (p 2406) :=
  ElevenRUP.step122658 (p 2132) (p 2406) (p 2598) (p 3695) (p 5214) (derived105492 p h) (derived90766 p h)

theorem derived122659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2187) ∨ (p 3309) ∨ (¬ p 2860) ∨ (p 3093) ∨ (¬ p 2241) :=
  ElevenRUP.step122659 (p 2132) (p 2187) (p 2241) (p 2750) (p 2753) (p 2860) (p 3093) (p 3309) (p 4405) (derived105512 p h) (derived106345 p h) (derived90770 p h)

theorem derived122660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2132) ∨ (p 3449) ∨ (p 3073) ∨ (¬ p 2459) ∨ (¬ p 2187) :=
  ElevenRUP.step122660 (p 2132) (p 2187) (p 2459) (p 2860) (p 3073) (p 3449) (p 4133) (p 4733) (derived105430 p h) (derived105712 p h) (derived90771 p h)

theorem derived122661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3453) ∨ (¬ p 2132) ∨ (¬ p 2881) ∨ (¬ p 4438) ∨ (p 3073) ∨ (p 3379) ∨ (¬ p 2528) ∨ (¬ p 2870) :=
  ElevenRUP.step122661 (p 2132) (p 2528) (p 2870) (p 2881) (p 3073) (p 3379) (p 3453) (p 4438) (p 4733) (derived105430 p h) (derived90773 p h)

theorem derived122662 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 4140) ∨ (¬ p 2996) ∨ (¬ p 2870) ∨ (¬ p 2177) ∨ (p 2449) ∨ (p 2241) :=
  ElevenRUP.step122662 (p 2132) (p 2177) (p 2241) (p 2449) (p 2870) (p 2996) (p 4140) (p 4666) (p 4733) (derived105430 p h) (derived105658 p h) (derived90775 p h)

theorem derived122663 (p : Nat → Prop) (h : Inputs p) :
    (p 2663) ∨ (¬ p 2891) ∨ (¬ p 3579) ∨ (p 3389) ∨ (p 2737) ∨ (¬ p 3246) ∨ (¬ p 3361) ∨ (¬ p 2132) ∨ (p 2264) ∨ (¬ p 4418) :=
  ElevenRUP.step122663 (p 2132) (p 2264) (p 2663) (p 2737) (p 2891) (p 3246) (p 3361) (p 3389) (p 3579) (p 4418) (p 4668) (derived105414 p h) (derived90776 p h)

theorem derived122665 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (p 2241) ∨ (¬ p 3950) ∨ (¬ p 2132) ∨ (p 3256) ∨ (¬ p 2870) ∨ (¬ p 3246) :=
  ElevenRUP.step122665 (p 2132) (p 2241) (p 2870) (p 3189) (p 3246) (p 3256) (p 3950) (p 4733) (derived105430 p h) (derived90779 p h)

theorem derived122666 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 3189) ∨ (p 3256) ∨ (¬ p 2132) ∨ (¬ p 3125) ∨ (¬ p 2860) :=
  ElevenRUP.step122666 (p 2132) (p 2241) (p 2860) (p 3125) (p 3189) (p 3256) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived90781 p h)

theorem derived122670 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 3527) ∨ (¬ p 2742) ∨ (¬ p 3038) ∨ (¬ p 2132) ∨ (¬ p 3820) :=
  ElevenRUP.step122670 (p 2132) (p 2341) (p 2742) (p 3038) (p 3527) (p 3820) (p 5052) (derived105473 p h) (derived90798 p h)

theorem derived122671 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2132) ∨ (¬ p 4759) ∨ (¬ p 2742) ∨ (p 2307) ∨ (¬ p 3309) :=
  ElevenRUP.step122671 (p 2132) (p 2307) (p 2742) (p 2778) (p 3309) (p 4759) (p 5052) (derived105473 p h) (derived90801 p h)

theorem derived122672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2122) ∨ (¬ p 4426) ∨ (p 2307) ∨ (¬ p 2132) :=
  ElevenRUP.step122672 (p 2122) (p 2132) (p 2307) (p 2778) (p 4426) (p 5052) (derived105473 p h) (derived90808 p h)

theorem derived122677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3413) ∨ (p 4919) :=
  ElevenRUP.step122677 (p 3413) (p 4652) (p 4919) (derived105413 p h) (h 33775)

theorem derived122679 (p : Nat → Prop) (h : Inputs p) :
    (p 2098) ∨ (p 3609) ∨ (¬ p 2139) ∨ (p 2427) ∨ (¬ p 2363) ∨ (¬ p 3051) ∨ (¬ p 2373) :=
  ElevenRUP.step122679 (p 2098) (p 2139) (p 2363) (p 2373) (p 2427) (p 3051) (p 3609) (p 4433) (derived106150 p h) (derived90871 p h)

theorem derived122682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (p 2156) ∨ (p 2427) ∨ (¬ p 2284) :=
  ElevenRUP.step122682 (p 2156) (p 2284) (p 2427) (p 3051) (p 4705) (derived106238 p h) (derived90894 p h)

theorem derived122683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 3146) ∨ (p 2427) ∨ (p 2459) :=
  ElevenRUP.step122683 (p 2427) (p 2459) (p 2982) (p 3146) (p 4905) (derived105995 p h) (derived90900 p h)

theorem derived122685 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 2881) ∨ (¬ p 2901) :=
  ElevenRUP.step122685 (p 2881) (p 2901) (p 2911) (p 4705) (derived106238 p h) (derived90904 p h)

theorem derived122687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2441) ∨ (¬ p 3246) ∨ (p 2417) :=
  ElevenRUP.step122687 (p 2417) (p 2441) (p 2901) (p 3246) (p 4705) (derived106238 p h) (derived90909 p h)

theorem derived122688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2187) ∨ (p 2352) ∨ (¬ p 2590) :=
  ElevenRUP.step122688 (p 2187) (p 2284) (p 2352) (p 2590) (p 4705) (derived106238 p h) (derived90910 p h)

theorem derived122693 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 3389) ∨ (¬ p 2406) ∨ (p 2230) :=
  ElevenRUP.step122693 (p 2230) (p 2406) (p 2493) (p 3389) (p 4711) (derived105655 p h) (derived90955 p h)

theorem derived122694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3743) ∨ (p 2493) ∨ (¬ p 2406) ∨ (¬ p 2284) ∨ (¬ p 2386) :=
  ElevenRUP.step122694 (p 2284) (p 2386) (p 2406) (p 2493) (p 3743) (p 4705) (derived106238 p h) (derived90960 p h)

theorem derived122697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3379) ∨ (p 2295) ∨ (p 2177) ∨ (p 2331) ∨ (¬ p 2373) :=
  ElevenRUP.step122697 (p 2177) (p 2254) (p 2295) (p 2331) (p 2373) (p 2406) (p 3379) (p 4902) (derived105366 p h) (derived105456 p h) (derived90972 p h)

theorem derived122698 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 2406) ∨ (¬ p 2901) ∨ (¬ p 4001) :=
  ElevenRUP.step122698 (p 2406) (p 2901) (p 2922) (p 4001) (p 4705) (derived106238 p h) (derived90974 p h)

theorem derived122700 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 4001) ∨ (¬ p 2563) ∨ (¬ p 2406) :=
  ElevenRUP.step122700 (p 2406) (p 2563) (p 2922) (p 4001) (p 4555) (derived105542 p h) (derived90976 p h)

theorem derived122702 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 3096) ∨ (¬ p 2406) ∨ (¬ p 2427) :=
  ElevenRUP.step122702 (p 2406) (p 2427) (p 2493) (p 3096) (p 4558) (derived105400 p h) (derived90987 p h)

theorem derived122704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 3156) ∨ (¬ p 2406) ∨ (¬ p 3693) :=
  ElevenRUP.step122704 (p 2406) (p 2509) (p 3156) (p 3693) (p 4705) (derived106238 p h) (derived54203 p h)

theorem derived122706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 2819) ∨ (¬ p 3379) ∨ (¬ p 2373) ∨ (p 2307) ∨ (¬ p 2406) ∨ (¬ p 5021) :=
  ElevenRUP.step122706 (p 2122) (p 2307) (p 2373) (p 2406) (p 2819) (p 3379) (p 4433) (p 5021) (derived106150 p h) (derived90993 p h)

theorem derived122707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 3016) ∨ (¬ p 2406) ∨ (p 2230) :=
  ElevenRUP.step122707 (p 2230) (p 2406) (p 2573) (p 3016) (p 4814) (derived105440 p h) (derived90998 p h)

theorem derived122710 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (p 2850) ∨ (¬ p 2406) ∨ (¬ p 3016) :=
  ElevenRUP.step122710 (p 2406) (p 2493) (p 2850) (p 3016) (p 4750) (derived105433 p h) (derived91014 p h)

theorem derived122712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 2493) ∨ (¬ p 2982) ∨ (¬ p 3096) :=
  ElevenRUP.step122712 (p 2406) (p 2493) (p 2982) (p 3096) (p 5046) (derived105472 p h) (derived91018 p h)

theorem derived122718 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2774) ∨ (p 2230) ∨ (¬ p 4438) ∨ (¬ p 2177) ∨ (¬ p 2122) ∨ (¬ p 4108) ∨ (¬ p 2406) :=
  ElevenRUP.step122718 (p 2122) (p 2177) (p 2230) (p 2406) (p 2509) (p 2774) (p 4108) (p 4438) (p 4733) (derived105430 p h) (derived91034 p h)

theorem derived122721 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 3379) ∨ (¬ p 2459) ∨ (p 2363) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 5021) :=
  ElevenRUP.step122721 (p 2363) (p 2373) (p 2383) (p 2406) (p 2459) (p 3379) (p 4902) (p 5021) (derived105456 p h) (derived91044 p h)

theorem derived122722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (p 2493) ∨ (¬ p 2406) ∨ (p 2437) :=
  ElevenRUP.step122722 (p 2406) (p 2437) (p 2493) (p 3016) (p 4644) (derived105411 p h) (derived91049 p h)

theorem derived122723 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 3879) ∨ (¬ p 2651) ∨ (¬ p 2406) :=
  ElevenRUP.step122723 (p 2406) (p 2651) (p 2946) (p 3879) (p 4814) (derived105440 p h) (derived91050 p h)

theorem derived122724 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2440) ∨ (¬ p 4281) ∨ (¬ p 2406) :=
  ElevenRUP.step122724 (p 2249) (p 2406) (p 2440) (p 2651) (p 4281) (derived106513 p h) (derived91054 p h)

theorem derived122726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2497) ∨ (¬ p 2578) ∨ (p 3309) ∨ (¬ p 2307) :=
  ElevenRUP.step122726 (p 2307) (p 2406) (p 2497) (p 2578) (p 3309) (p 4715) (derived105423 p h) (derived91060 p h)

theorem derived122729 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 3379) ∨ (¬ p 2406) :=
  ElevenRUP.step122729 (p 2406) (p 3379) (p 3830) (p 4949) (derived105463 p h) (derived91066 p h)

theorem derived122730 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2156) ∨ (¬ p 2406) ∨ (¬ p 3096) :=
  ElevenRUP.step122730 (p 2156) (p 2406) (p 2493) (p 3096) (p 4539) (derived105395 p h) (derived91073 p h)

theorem derived122731 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 3379) ∨ (p 2363) ∨ (¬ p 2406) ∨ (¬ p 2982) ∨ (¬ p 4450) ∨ (p 2668) :=
  ElevenRUP.step122731 (p 2254) (p 2331) (p 2363) (p 2406) (p 2668) (p 2982) (p 3379) (p 4450) (derived105366 p h) (derived91078 p h)

theorem derived122733 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 2493) ∨ (¬ p 4371) ∨ (¬ p 3573) ∨ (¬ p 2406) ∨ (¬ p 2363) :=
  ElevenRUP.step122733 (p 2363) (p 2406) (p 2493) (p 3073) (p 3573) (p 4371) (p 4608) (derived105540 p h) (derived91087 p h)

theorem derived122734 (p : Nat → Prop) (h : Inputs p) :
    (p 3005) ∨ (¬ p 3379) ∨ (¬ p 2982) ∨ (p 2696) ∨ (p 3256) ∨ (¬ p 2406) ∨ (¬ p 4450) :=
  ElevenRUP.step122734 (p 2406) (p 2696) (p 2982) (p 3005) (p 3256) (p 3379) (p 4450) (p 4736) (derived105431 p h) (derived91094 p h)

theorem derived122742 (p : Nat → Prop) (h : Inputs p) :
    (p 2088) ∨ (¬ p 3347) ∨ (¬ p 2528) ∨ (¬ p 2406) ∨ (¬ p 2474) :=
  ElevenRUP.step122742 (p 2088) (p 2406) (p 2474) (p 2528) (p 3347) (p 4608) (derived105540 p h) (derived91111 p h)

theorem derived122746 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2497) ∨ (¬ p 3923) ∨ (¬ p 2352) :=
  ElevenRUP.step122746 (p 2352) (p 2406) (p 2497) (p 3923) (p 4715) (derived105423 p h) (derived41298 p h)

theorem derived122748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2497) ∨ (p 3319) ∨ (¬ p 3564) :=
  ElevenRUP.step122748 (p 2406) (p 2497) (p 3319) (p 3564) (p 4715) (derived105423 p h) (derived91125 p h)

theorem derived122751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2926) ∨ (¬ p 2406) ∨ (p 3527) ∨ (¬ p 2911) :=
  ElevenRUP.step122751 (p 2406) (p 2911) (p 2926) (p 3527) (p 4644) (derived105411 p h) (derived91138 p h)

theorem derived122755 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2922) ∨ (¬ p 2437) ∨ (¬ p 2406) :=
  ElevenRUP.step122755 (p 2406) (p 2437) (p 2850) (p 2922) (p 4750) (derived105433 p h) (derived91149 p h)

theorem derived122757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (p 3051) ∨ (p 3246) ∨ (¬ p 2742) ∨ (¬ p 2264) ∨ (p 2996) ∨ (¬ p 2696) ∨ (p 2839) :=
  ElevenRUP.step122757 (p 2143) (p 2264) (p 2696) (p 2742) (p 2839) (p 2996) (p 3051) (p 3246) (p 4666) (derived105658 p h) (derived91197 p h)

theorem derived122759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 3051) ∨ (¬ p 2449) ∨ (¬ p 2696) ∨ (p 2839) ∨ (¬ p 3919) ∨ (p 2881) ∨ (¬ p 2143) :=
  ElevenRUP.step122759 (p 2143) (p 2449) (p 2696) (p 2839) (p 2881) (p 3005) (p 3051) (p 3919) (p 4668) (derived105414 p h) (derived91199 p h)

theorem derived122761 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2143) ∨ (p 3125) ∨ (¬ p 3256) ∨ (p 2839) ∨ (p 2156) ∨ (¬ p 3189) ∨ (¬ p 2742) :=
  ElevenRUP.step122761 (p 2143) (p 2156) (p 2696) (p 2742) (p 2839) (p 3125) (p 3189) (p 3256) (p 4604) (derived106293 p h) (derived91203 p h)

theorem derived122765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 3969) ∨ (¬ p 5590) ∨ (¬ p 4198) ∨ (¬ p 4197) ∨ (¬ p 2373) :=
  ElevenRUP.step122765 (p 2143) (p 2373) (p 3969) (p 4197) (p 4198) (p 4882) (p 5590) (derived105453 p h) (derived50786 p h)

theorem derived122766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (p 3051) ∨ (¬ p 2829) ∨ (¬ p 3366) ∨ (¬ p 2459) ∨ (¬ p 4119) ∨ (p 2696) ∨ (¬ p 2143) ∨ (p 3146) :=
  ElevenRUP.step122766 (p 2143) (p 2459) (p 2696) (p 2819) (p 2829) (p 3051) (p 3146) (p 3366) (p 4119) (p 4133) (p 5052) (derived105712 p h) (derived105473 p h) (derived91220 p h)

theorem derived122767 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3564) ∨ (¬ p 2493) ∨ (¬ p 2143) ∨ (p 3146) ∨ (¬ p 2598) ∨ (p 2839) ∨ (¬ p 3590) :=
  ElevenRUP.step122767 (p 2143) (p 2220) (p 2493) (p 2598) (p 2839) (p 3146) (p 3564) (p 3590) (p 4330) (derived106329 p h) (derived91222 p h)

theorem derived122772 (p : Nat → Prop) (h : Inputs p) :
    (p 2341) ∨ (¬ p 4984) ∨ (¬ p 2881) ∨ (¬ p 2870) :=
  ElevenRUP.step122772 (p 2140) (p 2341) (p 2870) (p 2881) (p 4984) (derived105364 p h) (derived91255 p h)

theorem derived122775 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2122) ∨ (p 2307) ∨ (¬ p 4375) ∨ (¬ p 2386) :=
  ElevenRUP.step122775 (p 2122) (p 2307) (p 2386) (p 2850) (p 4375) (p 4717) (derived105424 p h) (derived91261 p h)

theorem derived122781 (p : Nat → Prop) (h : Inputs p) :
    (p 2417) ∨ (¬ p 3581) ∨ (¬ p 2274) ∨ (¬ p 2396) :=
  ElevenRUP.step122781 (p 2274) (p 2396) (p 2417) (p 3581) (p 3958) (derived105378 p h) (derived91291 p h)

theorem derived122782 (p : Nat → Prop) (h : Inputs p) :
    (p 2911) ∨ (¬ p 3581) ∨ (¬ p 2274) ∨ (¬ p 2177) :=
  ElevenRUP.step122782 (p 2177) (p 2274) (p 2911) (p 3581) (p 3958) (derived105378 p h) (derived91294 p h)

theorem derived122787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4331) ∨ (p 3016) ∨ (p 2553) ∨ (¬ p 3343) :=
  ElevenRUP.step122787 (p 2553) (p 3016) (p 3343) (p 4331) (p 4624) (derived105408 p h) (derived91309 p h)

theorem derived122788 (p : Nat → Prop) (h : Inputs p) :
    (p 3830) ∨ (¬ p 2246) ∨ (¬ p 5119) ∨ (¬ p 2264) ∨ (¬ p 3941) ∨ (p 3707) ∨ (¬ p 2608) ∨ (¬ p 2807) :=
  ElevenRUP.step122788 (p 2246) (p 2264) (p 2608) (p 2744) (p 2807) (p 3707) (p 3830) (p 3941) (p 5119) (derived106503 p h) (derived91330 p h)

theorem derived122789 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (p 3830) ∨ (¬ p 5119) ∨ (¬ p 2608) ∨ (¬ p 2946) ∨ (¬ p 2246) ∨ (p 3707) ∨ (¬ p 3156) :=
  ElevenRUP.step122789 (p 2246) (p 2608) (p 2744) (p 2946) (p 3156) (p 3707) (p 3830) (p 3969) (p 5119) (derived106503 p h) (derived91359 p h)

theorem derived122790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 3830) ∨ (¬ p 2246) ∨ (¬ p 2651) ∨ (¬ p 2437) ∨ (¬ p 2608) ∨ (p 3707) :=
  ElevenRUP.step122790 (p 2246) (p 2437) (p 2608) (p 2651) (p 2744) (p 3707) (p 3830) (p 3868) (p 4826) (derived106503 p h) (derived105444 p h) (derived91364 p h)

theorem derived122794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 2122) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (p 3830) ∨ (p 3707) ∨ (¬ p 2241) :=
  ElevenRUP.step122794 (p 2122) (p 2241) (p 2750) (p 2753) (p 2774) (p 3707) (p 3791) (p 3830) (p 4826) (derived106345 p h) (derived105444 p h) (derived91378 p h)

theorem derived122795 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 3051) ∨ (¬ p 4202) ∨ (¬ p 4109) ∨ (p 2440) :=
  ElevenRUP.step122795 (p 2440) (p 2891) (p 3051) (p 4109) (p 4202) (p 4811) (derived105633 p h) (derived91413 p h)

theorem derived122796 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 3051) ∨ (¬ p 4109) ∨ (¬ p 2493) ∨ (¬ p 4202) :=
  ElevenRUP.step122796 (p 2493) (p 2891) (p 3051) (p 4109) (p 4202) (p 4717) (derived105424 p h) (derived91414 p h)

theorem derived122797 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 4202) ∨ (¬ p 3051) ∨ (p 2241) ∨ (¬ p 4172) ∨ (¬ p 4257) :=
  ElevenRUP.step122797 (p 2241) (p 2744) (p 2891) (p 3051) (p 4172) (p 4202) (p 4257) (derived106503 p h) (derived91415 p h)

theorem derived122798 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2578) ∨ (¬ p 4202) ∨ (¬ p 4512) ∨ (p 3309) ∨ (¬ p 3016) ∨ (¬ p 2307) :=
  ElevenRUP.step122798 (p 2307) (p 2578) (p 3016) (p 3309) (p 4202) (p 4512) (p 4811) (derived105633 p h) (derived91416 p h)

theorem derived122801 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 3051) ∨ (¬ p 4202) ∨ (¬ p 4109) ∨ (¬ p 2850) :=
  ElevenRUP.step122801 (p 2850) (p 2891) (p 3051) (p 4109) (p 4202) (p 5214) (derived105492 p h) (derived91421 p h)

theorem derived122802 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5201) ∨ (¬ p 3516) ∨ (p 2437) ∨ (p 2417) :=
  ElevenRUP.step122802 (p 2417) (p 2437) (p 2665) (p 3516) (p 5201) (derived105373 p h) (derived91427 p h)

theorem derived122803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5201) ∨ (¬ p 3516) ∨ (p 2573) ∨ (¬ p 2441) ∨ (p 2417) :=
  ElevenRUP.step122803 (p 2417) (p 2441) (p 2573) (p 3516) (p 4715) (p 5201) (derived105423 p h) (derived91429 p h)

theorem derived122804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 5201) ∨ (p 2911) ∨ (p 2230) :=
  ElevenRUP.step122804 (p 2230) (p 2341) (p 2911) (p 4646) (p 5201) (derived105534 p h) (derived91434 p h)

theorem derived122806 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (p 2911) ∨ (p 2437) :=
  ElevenRUP.step122806 (p 2341) (p 2437) (p 2665) (p 2911) (derived105373 p h) (derived91440 p h)

theorem derived122808 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 5201) ∨ (p 2911) ∨ (¬ p 2341) :=
  ElevenRUP.step122808 (p 2341) (p 2911) (p 2922) (p 5194) (p 5201) (derived105489 p h) (derived91444 p h)

theorem derived122810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2584) ∨ (p 2437) ∨ (¬ p 2590) ∨ (¬ p 2656) ∨ (p 2352) :=
  ElevenRUP.step122810 (p 2352) (p 2383) (p 2437) (p 2584) (p 2590) (p 2656) (p 4644) (derived105411 p h) (derived91449 p h)

theorem derived122811 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 4399) ∨ (p 2563) ∨ (¬ p 2156) :=
  ElevenRUP.step122811 (p 2156) (p 2563) (p 3389) (p 4399) (p 4644) (derived105411 p h) (derived91450 p h)

theorem derived122816 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2946) ∨ (¬ p 3412) ∨ (p 2651) ∨ (¬ p 4210) :=
  ElevenRUP.step122816 (p 2651) (p 2850) (p 2946) (p 3412) (p 4210) (p 4750) (derived105433 p h) (derived91466 p h)

theorem derived122826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4210) ∨ (¬ p 4512) ∨ (¬ p 3093) ∨ (p 3379) ∨ (¬ p 3193) :=
  ElevenRUP.step122826 (p 3093) (p 3193) (p 3379) (p 4210) (p 4512) (p 4949) (derived105463 p h) (derived91502 p h)

theorem derived122835 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 4338) ∨ (¬ p 3063) ∨ (p 2187) :=
  ElevenRUP.step122835 (p 2187) (p 2891) (p 3063) (p 4338) (p 4555) (derived105542 p h) (derived91542 p h)

theorem derived122838 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 2608) ∨ (¬ p 5015) ∨ (p 2383) :=
  ElevenRUP.step122838 (p 2383) (p 2608) (p 3063) (p 4866) (p 5015) (derived106063 p h) (derived91571 p h)

theorem derived122840 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4869) ∨ (¬ p 3319) ∨ (¬ p 2210) ∨ (p 3654) ∨ (¬ p 5015) :=
  ElevenRUP.step122840 (p 2210) (p 3319) (p 3654) (p 4869) (p 4877) (p 5015) (derived105451 p h) (derived91574 p h)

theorem derived122843 (p : Nat → Prop) (h : Inputs p) :
    (p 2946) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (p 3246) ∨ (¬ p 2363) ∨ (p 2901) :=
  ElevenRUP.step122843 (p 2363) (p 2774) (p 2819) (p 2901) (p 2946) (p 3246) (p 4669) (p 4789) (derived105415 p h) (derived105646 p h) (derived91577 p h)

theorem derived122844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (p 3051) ∨ (p 3367) ∨ (¬ p 2891) ∨ (¬ p 3371) :=
  ElevenRUP.step122844 (p 2143) (p 2891) (p 3051) (p 3367) (p 3371) (p 4884) (derived105454 p h) (derived91578 p h)

theorem derived122848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 4448) :=
  ElevenRUP.step122848 (p 2750) (p 3371) (p 4448) (derived106345 p h) (h 6916)

theorem derived122852 (p : Nat → Prop) (h : Inputs p) :
    (p 3083) ∨ (p 2651) ∨ (¬ p 2252) ∨ (¬ p 3371) ∨ (¬ p 2156) ∨ (p 2528) ∨ (¬ p 3105) ∨ (¬ p 3370) ∨ (p 2860) ∨ (¬ p 4450) :=
  ElevenRUP.step122852 (p 2156) (p 2252) (p 2528) (p 2651) (p 2750) (p 2860) (p 3083) (p 3105) (p 3370) (p 3371) (p 4450) (derived106345 p h) (derived91593 p h)

theorem derived122853 (p : Nat → Prop) (h : Inputs p) :
    (p 2870) ∨ (¬ p 2891) ∨ (p 2737) ∨ (¬ p 3371) :=
  ElevenRUP.step122853 (p 2737) (p 2870) (p 2891) (p 3371) (p 5052) (derived105473 p h) (derived91594 p h)

theorem derived122854 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3371) ∨ (p 2737) ∨ (¬ p 2192) :=
  ElevenRUP.step122854 (p 2192) (p 2737) (p 2860) (p 3371) (p 5052) (derived105473 p h) (derived91595 p h)

theorem derived122856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (p 3051) ∨ (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 2241) :=
  ElevenRUP.step122856 (p 2241) (p 2750) (p 2891) (p 3051) (p 3369) (p 3371) (derived106345 p h) (derived91598 p h)

theorem derived122857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3371) ∨ (¬ p 2241) ∨ (¬ p 3950) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 2192) ∨ (p 3449) ∨ (p 3073) :=
  ElevenRUP.step122857 (p 2192) (p 2241) (p 2274) (p 2396) (p 2750) (p 3073) (p 3371) (p 3449) (p 3950) (derived106345 p h) (derived91600 p h)

theorem derived122858 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3370) ∨ (¬ p 3461) ∨ (p 2807) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (p 2264) ∨ (¬ p 3371) ∨ (¬ p 5558) ∨ (¬ p 5123) :=
  ElevenRUP.step122858 (p 2156) (p 2264) (p 2807) (p 3125) (p 3366) (p 3370) (p 3371) (p 3461) (p 4789) (p 5123) (p 5558) (derived105646 p h) (derived91602 p h)

theorem derived122865 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5316) ∨ (¬ p 4416) ∨ (¬ p 2241) ∨ (p 2088) ∨ (¬ p 3073) :=
  ElevenRUP.step122865 (p 2088) (p 2241) (p 2750) (p 3073) (p 4416) (p 5316) (derived106345 p h) (derived91639 p h)

theorem derived122866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5316) ∨ (¬ p 4364) ∨ (p 3367) ∨ (p 3609) ∨ (¬ p 3073) :=
  ElevenRUP.step122866 (p 3073) (p 3367) (p 3609) (p 4364) (p 4749) (p 5316) (derived105432 p h) (derived91640 p h)

theorem derived122867 (p : Nat → Prop) (h : Inputs p) :
    (p 2373) ∨ (¬ p 2532) ∨ (¬ p 2982) ∨ (p 2459) :=
  ElevenRUP.step122867 (p 2373) (p 2459) (p 2532) (p 2982) (p 4905) (derived105995 p h) (derived91642 p h)

theorem derived122869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4260) ∨ (¬ p 3680) ∨ (p 2641) ∨ (¬ p 2972) ∨ (¬ p 4116) ∨ (¬ p 2811) ∨ (¬ p 2667) ∨ (p 2307) ∨ (¬ p 3948) ∨ (¬ p 2651) :=
  ElevenRUP.step122869 (p 2307) (p 2641) (p 2651) (p 2667) (p 2745) (p 2811) (p 2972) (p 3680) (p 3948) (p 4116) (p 4260) (p 4831) (derived105523 p h) (derived105445 p h) (derived91656 p h)

theorem derived122870 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2166) ∨ (p 2373) ∨ (¬ p 3948) :=
  ElevenRUP.step122870 (p 2166) (p 2373) (p 2493) (p 3948) (p 4715) (derived105423 p h) (derived91663 p h)

theorem derived122872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3948) ∨ (p 2156) ∨ (p 2922) ∨ (¬ p 2957) ∨ (¬ p 2192) ∨ (¬ p 4241) :=
  ElevenRUP.step122872 (p 2156) (p 2192) (p 2922) (p 2957) (p 3948) (p 4241) (p 4644) (derived105411 p h) (derived91671 p h)

theorem derived122876 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3948) ∨ (p 2922) ∨ (¬ p 2972) ∨ (p 2982) :=
  ElevenRUP.step122876 (p 2922) (p 2972) (p 2982) (p 3948) (p 4644) (derived105411 p h) (derived91677 p h)

theorem derived122878 (p : Nat → Prop) (h : Inputs p) :
    (p 2493) ∨ (¬ p 2972) ∨ (¬ p 3948) ∨ (p 2982) :=
  ElevenRUP.step122878 (p 2493) (p 2972) (p 2982) (p 3948) (p 4715) (derived105423 p h) (derived91679 p h)

theorem derived122884 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 2166) ∨ (¬ p 4031) ∨ (¬ p 3948) ∨ (p 2922) :=
  ElevenRUP.step122884 (p 2166) (p 2220) (p 2922) (p 3948) (p 4031) (p 4644) (derived105411 p h) (derived91687 p h)

theorem derived122885 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4031) ∨ (p 3051) ∨ (p 3016) ∨ (¬ p 2891) ∨ (¬ p 4116) ∨ (¬ p 3948) :=
  ElevenRUP.step122885 (p 2891) (p 3016) (p 3051) (p 3948) (p 4031) (p 4116) (p 4715) (derived105423 p h) (derived91688 p h)

theorem derived122899 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (p 2870) ∨ (p 2132) ∨ (p 2881) ∨ (¬ p 5564) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (p 2241) ∨ (¬ p 3547) :=
  ElevenRUP.step122899 (p 2132) (p 2241) (p 2744) (p 2870) (p 2881) (p 3366) (p 3399) (p 3547) (p 3791) (p 5564) (derived106503 p h) (derived91721 p h)

theorem derived122902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (p 3564) ∨ (p 2295) ∨ (¬ p 3323) :=
  ElevenRUP.step122902 (p 2295) (p 2352) (p 3323) (p 3564) (p 4405) (derived105512 p h) (derived91735 p h)

theorem derived122903 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3983) ∨ (¬ p 3323) ∨ (¬ p 3019) ∨ (¬ p 2807) ∨ (p 3654) :=
  ElevenRUP.step122903 (p 2807) (p 3019) (p 3323) (p 3654) (p 3983) (p 4652) (derived105413 p h) (derived91738 p h)

theorem derived122908 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2927) ∨ (¬ p 3389) ∨ (¬ p 3323) ∨ (¬ p 3527) ∨ (¬ p 2459) ∨ (p 2493) ∨ (p 3564) ∨ (p 2295) :=
  ElevenRUP.step122908 (p 2295) (p 2459) (p 2493) (p 2927) (p 3323) (p 3389) (p 3527) (p 3564) (p 5194) (derived105489 p h) (derived91756 p h)

theorem derived122909 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3323) ∨ (¬ p 2331) ∨ (p 2553) ∨ (p 2493) ∨ (¬ p 2992) ∨ (p 2946) :=
  ElevenRUP.step122909 (p 2331) (p 2493) (p 2553) (p 2946) (p 2992) (p 3323) (p 3379) (p 4624) (derived105408 p h) (derived91758 p h)

theorem derived122912 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (p 3379) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (p 2528) ∨ (¬ p 3323) :=
  ElevenRUP.step122912 (p 2509) (p 2528) (p 2696) (p 2797) (p 3323) (p 3379) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived91764 p h)

theorem derived122916 (p : Nat → Prop) (h : Inputs p) :
    (p 3073) ∨ (p 2774) ∨ (¬ p 4371) ∨ (¬ p 2363) ∨ (¬ p 2737) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 4024) :=
  ElevenRUP.step122916 (p 2363) (p 2737) (p 2774) (p 3073) (p 3136) (p 3156) (p 4024) (p 4371) (p 4433) (derived106150 p h) (derived91806 p h)

theorem derived122920 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (p 2598) ∨ (p 2396) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 2717) ∨ (p 3425) ∨ (p 2295) :=
  ElevenRUP.step122920 (p 2252) (p 2295) (p 2331) (p 2396) (p 2598) (p 2717) (p 2748) (p 3425) (p 4666) (p 4749) (derived105658 p h) (derived105432 p h) (derived91828 p h)

theorem derived122925 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (¬ p 2761) ∨ (p 2331) ∨ (p 3425) ∨ (¬ p 3434) ∨ (¬ p 2753) ∨ (¬ p 5580) ∨ (¬ p 2252) ∨ (¬ p 5123) :=
  ElevenRUP.step122925 (p 2252) (p 2331) (p 2668) (p 2750) (p 2753) (p 2761) (p 3425) (p 3434) (p 5123) (p 5580) (derived106345 p h) (derived91838 p h)

theorem derived122926 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4243) ∨ (¬ p 2252) ∨ (p 2177) ∨ (p 2331) ∨ (¬ p 2210) ∨ (p 2608) ∨ (¬ p 2619) ∨ (p 2295) :=
  ElevenRUP.step122926 (p 2177) (p 2210) (p 2252) (p 2295) (p 2331) (p 2608) (p 2619) (p 2750) (p 4243) (p 4902) (derived105456 p h) (derived106345 p h) (derived91840 p h)

theorem derived122927 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (p 2608) ∨ (p 2668) ∨ (¬ p 2252) ∨ (p 2331) ∨ (¬ p 3950) ∨ (p 2363) :=
  ElevenRUP.step122927 (p 2252) (p 2331) (p 2363) (p 2608) (p 2668) (p 2750) (p 3399) (p 3631) (p 3950) (derived106345 p h) (derived91841 p h)

theorem derived122928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (¬ p 5284) ∨ (p 2608) ∨ (¬ p 2252) ∨ (¬ p 3266) ∨ (¬ p 3950) ∨ (p 3286) :=
  ElevenRUP.step122928 (p 2252) (p 2608) (p 2750) (p 3266) (p 3286) (p 3399) (p 3631) (p 3950) (p 5284) (derived106345 p h) (derived91842 p h)

theorem derived122931 (p : Nat → Prop) (h : Inputs p) :
    (p 2573) ∨ (¬ p 2630) ∨ (¬ p 2655) ∨ (¬ p 2252) ∨ (¬ p 3016) :=
  ElevenRUP.step122931 (p 2252) (p 2573) (p 2630) (p 2655) (p 2745) (p 3016) (derived105523 p h) (derived91846 p h)

theorem derived122936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 2946) ∨ (p 3246) ∨ (¬ p 2252) ∨ (¬ p 3201) ∨ (¬ p 2753) ∨ (p 2901) ∨ (¬ p 2911) :=
  ElevenRUP.step122936 (p 2252) (p 2598) (p 2750) (p 2753) (p 2901) (p 2911) (p 2946) (p 3201) (p 3246) (p 4666) (derived106345 p h) (derived105658 p h) (derived91862 p h)

theorem derived122937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 5164) ∨ (p 2807) ∨ (p 2264) ∨ (¬ p 5558) ∨ (p 2598) ∨ (¬ p 3619) ∨ (¬ p 2748) ∨ (¬ p 5123) ∨ (¬ p 2252) :=
  ElevenRUP.step122937 (p 2252) (p 2264) (p 2598) (p 2748) (p 2807) (p 3276) (p 3619) (p 4749) (p 5123) (p 5164) (p 5558) (derived105432 p h) (derived91863 p h)

theorem derived122938 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 2608) ∨ (¬ p 2655) ∨ (p 2470) ∨ (¬ p 3146) ∨ (¬ p 3527) ∨ (¬ p 3399) ∨ (¬ p 2252) :=
  ElevenRUP.step122938 (p 2252) (p 2470) (p 2528) (p 2608) (p 2655) (p 2750) (p 3146) (p 3399) (p 3527) (p 4905) (derived106345 p h) (derived105995 p h) (derived91864 p h)

theorem derived122939 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3399) ∨ (p 3016) ∨ (p 2608) ∨ (¬ p 2252) ∨ (p 2651) ∨ (p 3564) :=
  ElevenRUP.step122939 (p 2252) (p 2608) (p 2651) (p 2750) (p 3016) (p 3399) (p 3564) (p 3631) (p 4625) (derived106345 p h) (derived106455 p h) (derived91866 p h)

theorem derived122941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2252) ∨ (¬ p 2860) ∨ (p 2807) ∨ (p 2264) ∨ (¬ p 3125) ∨ (p 2459) :=
  ElevenRUP.step122941 (p 2132) (p 2252) (p 2264) (p 2459) (p 2750) (p 2753) (p 2807) (p 2860) (p 3125) (p 4330) (derived106345 p h) (derived106329 p h) (derived91872 p h)

theorem derived122943 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5503) ∨ (p 2651) ∨ (¬ p 2252) ∨ (¬ p 3399) ∨ (p 2437) ∨ (¬ p 3527) ∨ (p 2210) ∨ (¬ p 4448) :=
  ElevenRUP.step122943 (p 2210) (p 2252) (p 2437) (p 2651) (p 3399) (p 3527) (p 4448) (p 5503) (p 5559) (derived106189 p h) (derived91876 p h)

theorem derived122947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 2655) ∨ (p 2573) ∨ (¬ p 3016) ∨ (p 3083) ∨ (¬ p 2144) ∨ (p 2459) ∨ (¬ p 2220) ∨ (¬ p 2252) ∨ (¬ p 4438) :=
  ElevenRUP.step122947 (p 2144) (p 2220) (p 2252) (p 2459) (p 2573) (p 2655) (p 2750) (p 2753) (p 3016) (p 3083) (p 3146) (p 4438) (derived106345 p h) (derived91881 p h)

theorem derived122950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (p 2331) ∨ (¬ p 3256) ∨ (p 3309) ∨ (p 3146) ∨ (p 2177) ∨ (¬ p 3922) :=
  ElevenRUP.step122950 (p 2177) (p 2249) (p 2331) (p 3146) (p 3189) (p 3256) (p 3309) (p 3922) (p 4902) (derived105456 p h) (derived106513 p h) (derived91917 p h)

theorem derived122951 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4311) ∨ (p 2992) ∨ (p 2373) ∨ (¬ p 3189) :=
  ElevenRUP.step122951 (p 2373) (p 2992) (p 3189) (p 4311) (p 4705) (derived106238 p h) (derived91935 p h)

theorem derived122952 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3171) ∨ (p 2819) ∨ (¬ p 4113) ∨ (¬ p 3189) ∨ (p 2641) :=
  ElevenRUP.step122952 (p 2641) (p 2819) (p 3171) (p 3189) (p 4113) (p 4843) (derived105449 p h) (derived91941 p h)

theorem derived122953 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4283) ∨ (¬ p 4066) ∨ (¬ p 3919) ∨ (p 2427) ∨ (¬ p 3189) ∨ (p 2992) :=
  ElevenRUP.step122953 (p 2427) (p 2992) (p 3189) (p 3919) (p 4066) (p 4283) (p 4705) (derived106238 p h) (derived91948 p h)

theorem derived122955 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (p 2230) ∨ (¬ p 3256) ∨ (¬ p 2241) ∨ (¬ p 3189) ∨ (p 3246) :=
  ElevenRUP.step122955 (p 2230) (p 2241) (p 2427) (p 3189) (p 3246) (p 3256) (p 4669) (p 5193) (derived105488 p h) (derived105415 p h) (derived91959 p h)

theorem derived122956 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) ∨ (p 2573) ∨ (p 2396) ∨ (¬ p 2241) ∨ (¬ p 3256) ∨ (¬ p 3189) :=
  ElevenRUP.step122956 (p 2241) (p 2396) (p 2553) (p 2573) (p 3189) (p 3256) (p 4669) (p 5193) (derived105488 p h) (derived105415 p h) (derived91960 p h)

theorem derived122957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3171) ∨ (p 2177) ∨ (¬ p 2996) ∨ (¬ p 4403) :=
  ElevenRUP.step122957 (p 2177) (p 2996) (p 3171) (p 3189) (p 4361) (p 4403) (derived105382 p h) (derived91963 p h)

theorem derived122958 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4390) ∨ (¬ p 3189) ∨ (p 2573) ∨ (p 2396) ∨ (p 2122) ∨ (¬ p 2241) ∨ (¬ p 3256) :=
  ElevenRUP.step122958 (p 2122) (p 2241) (p 2396) (p 2573) (p 3189) (p 3256) (p 4390) (p 4669) (p 5193) (derived105488 p h) (derived105415 p h) (derived91974 p h)

theorem derived122960 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4311) ∨ (p 2992) ∨ (p 2284) ∨ (¬ p 3189) :=
  ElevenRUP.step122960 (p 2284) (p 2992) (p 3189) (p 4311) (p 4509) (derived105392 p h) (derived91980 p h)

theorem derived122968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3527) ∨ (p 2727) ∨ (p 2911) ∨ (¬ p 4653) ∨ (¬ p 3189) :=
  ElevenRUP.step122968 (p 2727) (p 2911) (p 3189) (p 3527) (p 4652) (p 4653) (derived105413 p h) (derived91992 p h)

theorem derived122972 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4869) ∨ (¬ p 3319) ∨ (¬ p 3917) ∨ (p 3367) :=
  ElevenRUP.step122972 (p 3319) (p 3367) (p 3917) (p 4869) (p 5224) (derived105494 p h) (derived92031 p h)

theorem derived122976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 2220) ∨ (p 2982) ∨ (¬ p 2373) ∨ (p 2608) ∨ (¬ p 3904) ∨ (¬ p 3347) ∨ (¬ p 3399) :=
  ElevenRUP.step122976 (p 2220) (p 2373) (p 2608) (p 2982) (p 3347) (p 3399) (p 3631) (p 3904) (p 3951) (derived106536 p h) (derived92047 p h)

theorem derived122979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 3904) ∨ (¬ p 2427) ∨ (¬ p 2533) ∨ (¬ p 3256) ∨ (¬ p 3166) ∨ (p 3051) ∨ (p 2982) ∨ (p 2363) :=
  ElevenRUP.step122979 (p 2363) (p 2427) (p 2533) (p 2982) (p 3051) (p 3166) (p 3256) (p 3904) (p 4117) (p 4134) (p 4729) (derived105379 p h) (derived105429 p h) (derived92074 p h)

theorem derived122983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (p 2982) ∨ (¬ p 4203) ∨ (¬ p 3016) :=
  ElevenRUP.step122983 (p 2440) (p 2982) (p 3016) (p 4203) (p 5043) (derived105471 p h) (derived92090 p h)

theorem derived122985 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 3212) ∨ (¬ p 4399) ∨ (p 2982) :=
  ElevenRUP.step122985 (p 2850) (p 2982) (p 3212) (p 4399) (p 4730) (derived106074 p h) (derived92092 p h)

theorem derived122990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4399) ∨ (¬ p 3212) ∨ (p 2982) ∨ (p 2573) :=
  ElevenRUP.step122990 (p 2573) (p 2982) (p 3212) (p 4399) (p 4715) (derived105423 p h) (derived92102 p h)

theorem derived122993 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 2210) ∨ (¬ p 2427) ∨ (p 2717) ∨ (p 2459) ∨ (p 2982) ∨ (¬ p 2972) :=
  ElevenRUP.step122993 (p 2210) (p 2427) (p 2459) (p 2717) (p 2972) (p 2982) (p 3425) (p 4736) (derived105431 p h) (derived92110 p h)

theorem derived122999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 2440) ∨ (¬ p 3461) ∨ (p 2761) ∨ (p 2651) ∨ (p 2982) ∨ (¬ p 2786) :=
  ElevenRUP.step122999 (p 2440) (p 2651) (p 2761) (p 2786) (p 2982) (p 3461) (p 3654) (p 3951) (p 4789) (derived105646 p h) (derived106536 p h) (derived92132 p h)

theorem derived123001 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2590) ∨ (¬ p 3984) ∨ (p 2406) ∨ (p 2630) ∨ (¬ p 2797) :=
  ElevenRUP.step123001 (p 2406) (p 2590) (p 2630) (p 2797) (p 3984) (p 4811) (derived105633 p h) (derived92143 p h)

theorem derived123005 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2192) ∨ (¬ p 2696) ∨ (p 2274) ∨ (¬ p 2797) ∨ (¬ p 2668) :=
  ElevenRUP.step123005 (p 2192) (p 2210) (p 2274) (p 2668) (p 2696) (p 2797) (p 4405) (p 4733) (derived105512 p h) (derived105430 p h) (derived92148 p h)

theorem derived123007 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2696) ∨ (p 2553) ∨ (¬ p 2797) ∨ (p 3379) ∨ (p 2493) :=
  ElevenRUP.step123007 (p 2493) (p 2553) (p 2668) (p 2696) (p 2797) (p 3379) (p 4405) (p 4733) (derived105512 p h) (derived105430 p h) (derived92151 p h)

theorem derived123009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2797) ∨ (p 2331) :=
  ElevenRUP.step123009 (p 2331) (p 2598) (p 2797) (p 4752) (derived105434 p h) (derived92165 p h)

theorem derived123010 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2493) ∨ (¬ p 2797) ∨ (¬ p 3984) :=
  ElevenRUP.step123010 (p 2493) (p 2630) (p 2797) (p 3984) (p 4811) (derived105633 p h) (derived92168 p h)

theorem derived123011 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (p 3093) ∨ (¬ p 2668) ∨ (¬ p 3379) ∨ (¬ p 2797) ∨ (p 3309) :=
  ElevenRUP.step123011 (p 2668) (p 2696) (p 2753) (p 2797) (p 3093) (p 3309) (p 3379) (p 4405) (derived105512 p h) (derived92170 p h)

theorem derived123013 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4228) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (p 2761) ∨ (p 3246) ∨ (¬ p 2797) ∨ (p 3051) ∨ (¬ p 3645) ∨ (¬ p 5250) :=
  ElevenRUP.step123013 (p 2696) (p 2753) (p 2761) (p 2797) (p 3051) (p 3246) (p 3645) (p 4228) (p 4877) (p 5250) (derived105451 p h) (derived92172 p h)

theorem derived123017 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 2696) ∨ (p 2341) ∨ (¬ p 2911) ∨ (p 2417) ∨ (¬ p 3323) ∨ (¬ p 2797) ∨ (¬ p 3546) :=
  ElevenRUP.step123017 (p 2341) (p 2417) (p 2696) (p 2753) (p 2797) (p 2911) (p 3323) (p 3546) (p 4621) (p 4796) (derived105407 p h) (derived105439 p h) (derived92176 p h)

theorem derived123018 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3399) ∨ (p 2459) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 2696) :=
  ElevenRUP.step123018 (p 2459) (p 2696) (p 2797) (p 3323) (p 3399) (p 3527) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived92177 p h)

theorem derived123024 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (p 3115) ∨ (¬ p 3986) ∨ (¬ p 2797) :=
  ElevenRUP.step123024 (p 2797) (p 3115) (p 3136) (p 3986) (p 5043) (derived105471 p h) (derived92195 p h)

theorem derived123025 (p : Nat → Prop) (h : Inputs p) :
    (p 2685) ∨ (¬ p 2797) ∨ (p 2651) ∨ (¬ p 2807) :=
  ElevenRUP.step123025 (p 2651) (p 2685) (p 2797) (p 2807) (p 4975) (derived105464 p h) (derived92197 p h)

theorem derived123027 (p : Nat → Prop) (h : Inputs p) :
    (p 2470) ∨ (¬ p 2668) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 2459) ∨ (p 2528) :=
  ElevenRUP.step123027 (p 2459) (p 2470) (p 2528) (p 2668) (p 2696) (p 2797) (p 4133) (p 4729) (derived105712 p h) (derived105429 p h) (derived92204 p h)

theorem derived123028 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 3051) ∨ (p 2459) ∨ (¬ p 2753) ∨ (¬ p 3323) ∨ (p 2881) ∨ (¬ p 2797) ∨ (¬ p 3645) :=
  ElevenRUP.step123028 (p 2459) (p 2696) (p 2753) (p 2797) (p 2881) (p 3051) (p 3323) (p 3645) (p 4330) (p 4877) (derived106329 p h) (derived105451 p h) (derived92206 p h)

theorem derived123029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 4032) ∨ (¬ p 2753) ∨ (¬ p 3645) ∨ (¬ p 3323) ∨ (¬ p 2797) ∨ (¬ p 4322) ∨ (¬ p 3266) :=
  ElevenRUP.step123029 (p 2696) (p 2753) (p 2797) (p 3266) (p 3323) (p 3645) (p 4032) (p 4322) (p 4330) (p 4877) (derived106329 p h) (derived105451 p h) (derived53808 p h)

theorem derived123031 (p : Nat → Prop) (h : Inputs p) :
    (p 2331) ∨ (¬ p 2797) ∨ (p 2727) ∨ (¬ p 2651) :=
  ElevenRUP.step123031 (p 2331) (p 2651) (p 2727) (p 2745) (p 2797) (derived105523 p h) (derived92211 p h)

theorem derived123032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 2630) ∨ (¬ p 2386) ∨ (p 2493) ∨ (¬ p 2797) :=
  ElevenRUP.step123032 (p 2386) (p 2493) (p 2630) (p 2797) (p 3567) (p 4811) (derived105633 p h) (derived92214 p h)

theorem derived123034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 2696) ∨ (p 3146) ∨ (p 2230) ∨ (p 2373) ∨ (¬ p 2797) :=
  ElevenRUP.step123034 (p 2230) (p 2373) (p 2696) (p 2797) (p 3146) (p 3323) (p 4330) (p 4729) (derived106329 p h) (derived105429 p h) (derived92221 p h)

theorem derived123036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2741) ∨ (¬ p 3367) ∨ (p 2641) ∨ (¬ p 2797) :=
  ElevenRUP.step123036 (p 2641) (p 2741) (p 2797) (p 3367) (p 4752) (derived105434 p h) (derived92232 p h)

theorem derived123037 (p : Nat → Prop) (h : Inputs p) :
    (p 2166) ∨ (¬ p 2696) ∨ (p 3146) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (p 2210) :=
  ElevenRUP.step123037 (p 2166) (p 2210) (p 2696) (p 2797) (p 3146) (p 3323) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived92235 p h)

theorem derived123038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2911) ∨ (¬ p 2295) ∨ (¬ p 2797) ∨ (p 3399) ∨ (p 3527) :=
  ElevenRUP.step123038 (p 2295) (p 2696) (p 2797) (p 2911) (p 3399) (p 3527) (p 4712) (p 4733) (derived105430 p h) (derived105422 p h) (derived92236 p h)

theorem derived123039 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (p 2156) ∨ (¬ p 2797) ∨ (¬ p 3986) :=
  ElevenRUP.step123039 (p 2156) (p 2797) (p 2954) (p 3136) (p 3986) (derived106494 p h) (derived92237 p h)

theorem derived123041 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (¬ p 2383) ∨ (¬ p 2797) ∨ (¬ p 4245) ∨ (¬ p 3923) :=
  ElevenRUP.step123041 (p 2383) (p 2745) (p 2797) (p 3567) (p 3923) (p 4245) (derived105523 p h) (derived62921 p h)

theorem derived123042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 2685) ∨ (¬ p 2383) ∨ (¬ p 2797) ∨ (¬ p 2298) :=
  ElevenRUP.step123042 (p 2298) (p 2383) (p 2685) (p 2797) (p 3567) (p 4405) (derived105512 p h) (derived92249 p h)

theorem derived123043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (p 3005) ∨ (¬ p 2891) ∨ (¬ p 2210) ∨ (p 2331) ∨ (¬ p 2881) ∨ (¬ p 4041) :=
  ElevenRUP.step123043 (p 2210) (p 2254) (p 2331) (p 2797) (p 2881) (p 2891) (p 3005) (p 4041) (derived105366 p h) (derived92254 p h)

theorem derived123044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3567) ∨ (p 2685) ∨ (¬ p 2797) ∨ (¬ p 3654) ∨ (¬ p 2298) :=
  ElevenRUP.step123044 (p 2298) (p 2685) (p 2797) (p 3567) (p 3654) (p 4624) (derived105408 p h) (derived92257 p h)

theorem derived123052 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4343) ∨ (¬ p 2737) ∨ (p 3367) ∨ (¬ p 2797) :=
  ElevenRUP.step123052 (p 2737) (p 2797) (p 3367) (p 4343) (p 4975) (derived105464 p h) (derived92304 p h)

theorem derived123055 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (p 2427) ∨ (¬ p 3051) ∨ (p 3093) ∨ (¬ p 3923) ∨ (¬ p 2373) ∨ (¬ p 2608) :=
  ElevenRUP.step123055 (p 2373) (p 2427) (p 2608) (p 3051) (p 3093) (p 3370) (p 3923) (p 4377) (p 4433) (derived106150 p h) (derived106170 p h) (derived92309 p h)

theorem derived123057 (p : Nat → Prop) (h : Inputs p) :
    (p 3343) ∨ (¬ p 3370) ∨ (p 2630) ∨ (¬ p 3366) ∨ (¬ p 3051) ∨ (p 2696) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (¬ p 4697) :=
  ElevenRUP.step123057 (p 2459) (p 2630) (p 2696) (p 2881) (p 3051) (p 3343) (p 3366) (p 3370) (p 4377) (p 4697) (derived106170 p h) (derived92313 p h)

theorem derived123058 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (¬ p 3366) ∨ (p 3201) ∨ (¬ p 3125) ∨ (¬ p 2383) ∨ (¬ p 2962) ∨ (¬ p 3370) ∨ (p 2187) ∨ (p 2417) :=
  ElevenRUP.step123058 (p 2187) (p 2383) (p 2417) (p 2598) (p 2962) (p 3125) (p 3201) (p 3366) (p 3370) (p 4377) (p 4621) (derived106170 p h) (derived105407 p h) (derived92314 p h)

theorem derived123059 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3343) ∨ (p 2696) ∨ (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 3370) ∨ (¬ p 2363) ∨ (p 3276) ∨ (¬ p 3366) :=
  ElevenRUP.step123059 (p 2156) (p 2187) (p 2363) (p 2630) (p 2696) (p 3276) (p 3343) (p 3366) (p 3370) (p 4377) (derived106170 p h) (derived92316 p h)

theorem derived123061 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (p 3005) ∨ (p 2696) ∨ (¬ p 3366) ∨ (¬ p 2982) ∨ (¬ p 5045) ∨ (p 3256) ∨ (¬ p 2156) ∨ (p 2563) :=
  ElevenRUP.step123061 (p 2156) (p 2563) (p 2696) (p 2982) (p 3005) (p 3256) (p 3366) (p 3370) (p 4330) (p 4377) (p 5045) (derived106170 p h) (derived106329 p h) (derived92318 p h)

theorem derived123062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3370) ∨ (p 2797) ∨ (p 3323) ∨ (¬ p 2459) ∨ (¬ p 3051) ∨ (¬ p 2881) ∨ (¬ p 3366) ∨ (p 2696) :=
  ElevenRUP.step123062 (p 2459) (p 2696) (p 2797) (p 2881) (p 3051) (p 3323) (p 3366) (p 3370) (p 4377) (p 4604) (derived106293 p h) (derived106170 p h) (derived92320 p h)

theorem derived123064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2590) ∨ (p 2352) ∨ (¬ p 3370) :=
  ElevenRUP.step123064 (p 2156) (p 2187) (p 2352) (p 2590) (p 3370) (p 4632) (derived106257 p h) (derived92327 p h)

theorem derived123068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4365) ∨ (p 2210) ∨ (¬ p 2807) ∨ (¬ p 2996) :=
  ElevenRUP.step123068 (p 2210) (p 2248) (p 2807) (p 2996) (p 4365) (derived105365 p h) (derived92341 p h)

theorem derived123073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (p 3093) ∨ (p 2668) ∨ (¬ p 4318) :=
  ElevenRUP.step123073 (p 2668) (p 3093) (p 3449) (p 4318) (p 4761) (derived106234 p h) (derived92366 p h)

theorem derived123076 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (p 3083) ∨ (¬ p 4236) ∨ (p 2210) ∨ (¬ p 4318) ∨ (¬ p 3366) ∨ (p 2528) ∨ (p 2651) ∨ (¬ p 3449) :=
  ElevenRUP.step123076 (p 2210) (p 2528) (p 2651) (p 3083) (p 3366) (p 3449) (p 3979) (p 4236) (p 4318) (p 4377) (p 5122) (derived106170 p h) (derived105483 p h) (derived92372 p h)

theorem derived123078 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 2528) ∨ (p 3146) ∨ (¬ p 4355) ∨ (¬ p 3988) :=
  ElevenRUP.step123078 (p 2427) (p 2528) (p 3146) (p 3988) (p 4355) (p 4555) (derived105542 p h) (derived92391 p h)

theorem derived123079 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3741) ∨ (p 2156) ∨ (¬ p 3875) ∨ (¬ p 3988) ∨ (¬ p 2528) ∨ (p 3146) :=
  ElevenRUP.step123079 (p 2156) (p 2528) (p 3146) (p 3741) (p 3875) (p 3988) (p 4533) (derived105394 p h) (derived92398 p h)

theorem derived123080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2352) ∨ (p 3146) ∨ (p 2187) ∨ (¬ p 3988) :=
  ElevenRUP.step123080 (p 2187) (p 2352) (p 2528) (p 3146) (p 3988) (p 4718) (derived105425 p h) (derived92404 p h)

theorem derived123084 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4009) ∨ (p 2685) ∨ (¬ p 2807) ∨ (p 3146) ∨ (¬ p 2246) ∨ (p 2230) ∨ (p 2373) ∨ (¬ p 3005) ∨ (¬ p 3347) ∨ (¬ p 2749) :=
  ElevenRUP.step123084 (p 2230) (p 2246) (p 2373) (p 2685) (p 2749) (p 2807) (p 3005) (p 3146) (p 3347) (p 4009) (p 5122) (derived105483 p h) (derived92432 p h)

theorem derived123088 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (¬ p 2532) ∨ (p 2363) ∨ (p 2220) :=
  ElevenRUP.step123088 (p 2220) (p 2363) (p 2532) (p 3212) (p 4134) (derived105379 p h) (derived92466 p h)

theorem derived123090 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3212) ∨ (p 2220) ∨ (p 2528) ∨ (¬ p 2532) :=
  ElevenRUP.step123090 (p 2220) (p 2528) (p 2532) (p 3212) (p 4158) (derived106187 p h) (derived92473 p h)

theorem derived123095 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 4117) ∨ (¬ p 2373) ∨ (¬ p 2295) ∨ (¬ p 2145) ∨ (p 2982) ∨ (¬ p 2396) ∨ (¬ p 2331) :=
  ElevenRUP.step123095 (p 2145) (p 2220) (p 2295) (p 2331) (p 2373) (p 2396) (p 2982) (p 3951) (p 4117) (derived106536 p h) (derived92483 p h)

theorem derived123096 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3156) ∨ (¬ p 3413) ∨ (¬ p 4031) ∨ (p 2850) :=
  ElevenRUP.step123096 (p 2220) (p 2850) (p 3156) (p 3413) (p 4031) (p 4750) (derived105433 p h) (derived92487 p h)

theorem derived123097 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3156) ∨ (¬ p 3879) ∨ (¬ p 3904) ∨ (¬ p 2573) :=
  ElevenRUP.step123097 (p 2220) (p 2573) (p 3156) (p 3879) (p 3904) (p 4717) (derived105424 p h) (derived92488 p h)

theorem derived123101 (p : Nat → Prop) (h : Inputs p) :
    (p 2220) ∨ (¬ p 3156) ∨ (¬ p 3434) ∨ (¬ p 2707) ∨ (¬ p 2608) ∨ (p 3115) :=
  ElevenRUP.step123101 (p 2220) (p 2608) (p 2707) (p 3115) (p 3156) (p 3434) (p 3951) (derived106536 p h) (derived92508 p h)

theorem derived123102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 4368) ∨ (¬ p 3564) ∨ (¬ p 2950) ∨ (¬ p 3156) ∨ (p 2220) ∨ (¬ p 2252) ∨ (p 3115) :=
  ElevenRUP.step123102 (p 2220) (p 2252) (p 2598) (p 2750) (p 2753) (p 2950) (p 3115) (p 3156) (p 3422) (p 3564) (p 4368) (derived106345 p h) (derived92512 p h)

theorem derived123104 (p : Nat → Prop) (h : Inputs p) :
    (p 2992) ∨ (¬ p 3319) ∨ (¬ p 2957) ∨ (¬ p 5568) ∨ (¬ p 3461) ∨ (¬ p 2331) ∨ (p 2220) ∨ (¬ p 4319) ∨ (¬ p 5123) :=
  ElevenRUP.step123104 (p 2220) (p 2255) (p 2331) (p 2957) (p 2992) (p 3319) (p 3461) (p 4319) (p 5123) (p 5568) (derived105367 p h) (derived92527 p h)

theorem derived123106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (¬ p 2950) ∨ (p 2220) ∨ (p 3266) ∨ (p 3256) ∨ (¬ p 2922) ∨ (¬ p 4311) ∨ (¬ p 3379) :=
  ElevenRUP.step123106 (p 2220) (p 2254) (p 2922) (p 2950) (p 3256) (p 3266) (p 3379) (p 3868) (p 4311) (p 4826) (derived105366 p h) (derived105444 p h) (derived92543 p h)

theorem derived123110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4988) ∨ (p 2156) ∨ (p 3527) ∨ (¬ p 2341) ∨ (¬ p 3571) :=
  ElevenRUP.step123110 (p 2156) (p 2341) (p 3527) (p 3571) (p 4558) (p 4988) (derived105400 p h) (derived92558 p h)

theorem derived123118 (p : Nat → Prop) (h : Inputs p) :
    (p 2922) ∨ (¬ p 3580) ∨ (p 2911) ∨ (¬ p 2264) :=
  ElevenRUP.step123118 (p 2264) (p 2911) (p 2922) (p 3580) (p 4811) (derived105633 p h) (derived92579 p h)

theorem derived123119 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3580) ∨ (p 2911) ∨ (¬ p 2264) :=
  ElevenRUP.step123119 (p 2264) (p 2911) (p 3016) (p 3580) (p 4711) (derived105655 p h) (derived92584 p h)

theorem derived123122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4452) ∨ (p 2685) ∨ (¬ p 3527) ∨ (¬ p 3093) ∨ (p 2177) ∨ (¬ p 3136) ∨ (p 2946) :=
  ElevenRUP.step123122 (p 2177) (p 2254) (p 2685) (p 2946) (p 3093) (p 3136) (p 3527) (p 4361) (p 4452) (derived105366 p h) (derived105382 p h) (derived92603 p h)

theorem derived123125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 3166) ∨ (¬ p 4653) ∨ (¬ p 3093) ∨ (p 2911) ∨ (p 2685) ∨ (¬ p 4452) ∨ (¬ p 3527) :=
  ElevenRUP.step123125 (p 2254) (p 2685) (p 2911) (p 3005) (p 3093) (p 3166) (p 3527) (p 4452) (p 4653) (derived105366 p h) (derived92610 p h)

theorem derived123126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4452) ∨ (¬ p 3527) ∨ (¬ p 3093) ∨ (p 2598) ∨ (p 2427) ∨ (p 2850) ∨ (p 2177) :=
  ElevenRUP.step123126 (p 2177) (p 2427) (p 2598) (p 2850) (p 3093) (p 3527) (p 4452) (p 4559) (p 4736) (derived105431 p h) (derived105701 p h) (derived92614 p h)

theorem derived123130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (¬ p 5152) ∨ (p 3323) ∨ (p 3093) :=
  ElevenRUP.step123130 (p 3093) (p 3323) (p 3830) (p 4761) (p 5152) (derived106234 p h) (derived92629 p h)

theorem derived123132 (p : Nat → Prop) (h : Inputs p) :
    (p 3449) ∨ (¬ p 5152) ∨ (¬ p 3542) ∨ (¬ p 3830) ∨ (p 2459) :=
  ElevenRUP.step123132 (p 2459) (p 3449) (p 3542) (p 3830) (p 4330) (p 5152) (derived106329 p h) (derived92635 p h)

theorem derived123133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3830) ∨ (¬ p 5152) ∨ (p 3093) ∨ (p 2553) ∨ (¬ p 2498) :=
  ElevenRUP.step123133 (p 2498) (p 2553) (p 3093) (p 3830) (p 4624) (p 5152) (derived105408 p h) (derived92640 p h)

theorem derived123135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (p 2891) ∨ (¬ p 2901) ∨ (p 2563) :=
  ElevenRUP.step123135 (p 2192) (p 2563) (p 2891) (p 2901) (p 4705) (derived106238 p h) (derived92669 p h)

theorem derived123137 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2166) ∨ (¬ p 2427) ∨ (p 2220) :=
  ElevenRUP.step123137 (p 2166) (p 2220) (p 2427) (p 2891) (p 4533) (derived105394 p h) (derived92677 p h)

theorem derived123139 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 4202) ∨ (¬ p 2427) ∨ (¬ p 2230) :=
  ElevenRUP.step123139 (p 2230) (p 2427) (p 2891) (p 4202) (p 5194) (derived105489 p h) (derived92686 p h)

theorem derived123142 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 4172) ∨ (p 2608) ∨ (¬ p 3051) :=
  ElevenRUP.step123142 (p 2608) (p 2891) (p 3051) (p 4172) (p 4877) (derived105451 p h) (derived92709 p h)

theorem derived123144 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 2166) ∨ (p 2177) ∨ (¬ p 4042) :=
  ElevenRUP.step123144 (p 2166) (p 2177) (p 2891) (p 4042) (p 4559) (derived105701 p h) (derived92716 p h)

theorem derived123145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (p 2891) ∨ (¬ p 2753) ∨ (p 2881) ∨ (p 2459) ∨ (¬ p 2651) ∨ (¬ p 3564) ∨ (¬ p 3016) :=
  ElevenRUP.step123145 (p 2459) (p 2651) (p 2753) (p 2881) (p 2891) (p 3016) (p 3564) (p 4117) (p 4330) (p 4877) (derived106329 p h) (derived105451 p h) (derived92717 p h)

theorem derived123148 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 4172) ∨ (¬ p 3051) ∨ (p 2598) ∨ (p 3422) ∨ (p 2352) ∨ (¬ p 2166) :=
  ElevenRUP.step123148 (p 2166) (p 2352) (p 2598) (p 2891) (p 3051) (p 3422) (p 4172) (p 4433) (p 4736) (derived105431 p h) (derived106150 p h) (derived92728 p h)

theorem derived123150 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2891) ∨ (¬ p 4516) ∨ (¬ p 3093) :=
  ElevenRUP.step123150 (p 2210) (p 2891) (p 3093) (p 4516) (p 4555) (derived105542 p h) (derived92731 p h)

theorem derived123151 (p : Nat → Prop) (h : Inputs p) :
    (p 2210) ∨ (p 2891) ∨ (p 3246) ∨ (¬ p 2264) ∨ (¬ p 2696) ∨ (¬ p 2685) :=
  ElevenRUP.step123151 (p 2210) (p 2264) (p 2685) (p 2696) (p 2891) (p 3246) (p 4666) (p 4733) (derived105430 p h) (derived105658 p h) (derived92738 p h)

theorem derived123152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 4243) ∨ (¬ p 3759) ∨ (¬ p 3367) ∨ (p 2891) ∨ (p 2881) ∨ (p 2132) ∨ (¬ p 2417) :=
  ElevenRUP.step123152 (p 2132) (p 2417) (p 2881) (p 2891) (p 3367) (p 3389) (p 3759) (p 4243) (p 4668) (derived105414 p h) (derived92742 p h)

theorem derived123153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4172) ∨ (p 2891) ∨ (p 3379) ∨ (¬ p 3051) ∨ (¬ p 4874) :=
  ElevenRUP.step123153 (p 2891) (p 3051) (p 3379) (p 4172) (p 4376) (p 4874) (derived106320 p h) (derived92746 p h)

theorem derived123158 (p : Nat → Prop) (h : Inputs p) :
    (p 2891) ∨ (¬ p 3519) ∨ (p 2177) ∨ (¬ p 3389) ∨ (p 2210) ∨ (¬ p 2608) ∨ (¬ p 2911) :=
  ElevenRUP.step123158 (p 2177) (p 2210) (p 2608) (p 2891) (p 2911) (p 3389) (p 3519) (p 4376) (p 4559) (derived105701 p h) (derived106320 p h) (derived92755 p h)

theorem derived123159 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2156) ∨ (p 2284) ∨ (p 3051) :=
  ElevenRUP.step123159 (p 2156) (p 2284) (p 2891) (p 3051) (p 4960) (derived106209 p h) (derived92758 p h)

theorem derived123161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3051) ∨ (¬ p 3741) ∨ (p 3246) :=
  ElevenRUP.step123161 (p 2417) (p 3051) (p 3246) (p 3741) (p 4533) (derived105394 p h) (derived92770 p h)

theorem derived123163 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2992) ∨ (¬ p 2528) ∨ (¬ p 3083) ∨ (¬ p 2651) ∨ (¬ p 2957) ∨ (p 3246) :=
  ElevenRUP.step123163 (p 2255) (p 2528) (p 2651) (p 2957) (p 2992) (p 3051) (p 3083) (p 3246) (p 4669) (derived105367 p h) (derived105415 p h) (derived92773 p h)

theorem derived123165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 4119) ∨ (¬ p 3083) ∨ (p 3146) ∨ (¬ p 2630) ∨ (¬ p 3645) ∨ (p 3051) ∨ (¬ p 2459) :=
  ElevenRUP.step123165 (p 2459) (p 2630) (p 2696) (p 2753) (p 3051) (p 3083) (p 3146) (p 3645) (p 4119) (p 4420) (p 4877) (derived105451 p h) (derived105707 p h) (derived92775 p h)

theorem derived123166 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3051) ∨ (p 3125) ∨ (¬ p 2962) :=
  ElevenRUP.step123166 (p 2962) (p 3051) (p 3125) (p 3654) (p 4555) (derived105542 p h) (derived92785 p h)

theorem derived123169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (p 3051) ∨ (p 2563) ∨ (¬ p 2156) :=
  ElevenRUP.step123169 (p 2156) (p 2563) (p 2901) (p 3051) (p 4705) (derived106238 p h) (derived92806 p h)

theorem derived123170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (p 3051) ∨ (p 3246) ∨ (¬ p 4431) :=
  ElevenRUP.step123170 (p 3051) (p 3246) (p 3631) (p 4431) (p 4522) (derived105393 p h) (derived92811 p h)

theorem derived123171 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 3564) ∨ (¬ p 3379) ∨ (p 2459) ∨ (p 2881) ∨ (¬ p 2493) :=
  ElevenRUP.step123171 (p 2459) (p 2493) (p 2881) (p 3051) (p 3379) (p 3564) (p 4330) (derived106329 p h) (derived92827 p h)

theorem derived123172 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2493) ∨ (¬ p 2962) ∨ (¬ p 3413) ∨ (¬ p 2386) ∨ (¬ p 2901) :=
  ElevenRUP.step123172 (p 2386) (p 2493) (p 2901) (p 2962) (p 3051) (p 3413) (p 4811) (derived105633 p h) (derived92828 p h)

theorem derived123173 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2220) ∨ (¬ p 4042) ∨ (p 2911) :=
  ElevenRUP.step123173 (p 2220) (p 2911) (p 3051) (p 4042) (p 4277) (derived105380 p h) (derived92830 p h)

theorem derived123175 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 3904) ∨ (¬ p 2427) ∨ (¬ p 2573) :=
  ElevenRUP.step123175 (p 2427) (p 2573) (p 3051) (p 3904) (p 4717) (derived105424 p h) (derived92836 p h)

theorem derived123179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2598) ∨ (¬ p 3641) ∨ (p 3051) ∨ (¬ p 2528) ∨ (p 3246) ∨ (p 2839) :=
  ElevenRUP.step123179 (p 2143) (p 2528) (p 2598) (p 2839) (p 3051) (p 3246) (p 3641) (p 4669) (derived105415 p h) (derived92865 p h)

theorem derived123181 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (p 2608) ∨ (p 2881) ∨ (¬ p 2177) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3645) :=
  ElevenRUP.step123181 (p 2177) (p 2608) (p 2881) (p 2922) (p 3051) (p 3379) (p 3645) (p 4276) (p 4877) (derived105516 p h) (derived105451 p h) (derived92875 p h)

theorem derived123183 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2950) ∨ (p 3051) ∨ (¬ p 2901) ∨ (¬ p 2331) :=
  ElevenRUP.step123183 (p 2331) (p 2901) (p 2950) (p 3051) (p 4566) (derived106307 p h) (derived92883 p h)

theorem derived123184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (p 2881) ∨ (¬ p 3323) ∨ (¬ p 3904) ∨ (p 3051) ∨ (¬ p 2331) ∨ (¬ p 5558) ∨ (¬ p 3461) ∨ (¬ p 5123) :=
  ElevenRUP.step123184 (p 2331) (p 2881) (p 3051) (p 3323) (p 3461) (p 3904) (p 4117) (p 4729) (p 5123) (p 5558) (derived105429 p h) (derived92884 p h)

theorem derived123186 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2727) ∨ (¬ p 2241) ∨ (¬ p 2177) ∨ (p 2881) ∨ (¬ p 2437) :=
  ElevenRUP.step123186 (p 2177) (p 2241) (p 2437) (p 2727) (p 2881) (p 3051) (p 4276) (derived105516 p h) (derived92892 p h)

theorem derived123187 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (p 3051) ∨ (¬ p 2901) ∨ (¬ p 2563) :=
  ElevenRUP.step123187 (p 2284) (p 2563) (p 2901) (p 3051) (p 4533) (derived105394 p h) (derived92896 p h)

theorem derived123189 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 4368) ∨ (p 3051) ∨ (¬ p 2901) ∨ (p 3115) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 2950) :=
  ElevenRUP.step123189 (p 2598) (p 2901) (p 2950) (p 3051) (p 3115) (p 3422) (p 3564) (p 4368) (p 4789) (derived105646 p h) (derived92906 p h)

theorem derived123190 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 2992) ∨ (¬ p 3904) ∨ (¬ p 2655) ∨ (¬ p 2901) :=
  ElevenRUP.step123190 (p 2249) (p 2655) (p 2901) (p 2992) (p 3051) (p 3904) (derived106513 p h) (derived92911 p h)

theorem derived123191 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 4031) ∨ (¬ p 3413) ∨ (¬ p 2901) ∨ (p 3016) :=
  ElevenRUP.step123191 (p 2901) (p 3016) (p 3051) (p 3413) (p 4031) (p 4715) (derived105423 p h) (derived92912 p h)

theorem derived123193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3645) ∨ (¬ p 2459) ∨ (p 3146) ∨ (¬ p 4874) ∨ (p 3051) ∨ (¬ p 3083) ∨ (p 3016) ∨ (¬ p 4119) ∨ (¬ p 3519) :=
  ElevenRUP.step123193 (p 2459) (p 2573) (p 3016) (p 3051) (p 3083) (p 3146) (p 3519) (p 3645) (p 4119) (p 4376) (p 4420) (p 4874) (derived106320 p h) (derived105707 p h) (derived92920 p h)

theorem derived123198 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (¬ p 4243) ∨ (p 2132) ∨ (p 2192) ∨ (¬ p 4344) :=
  ElevenRUP.step123198 (p 2132) (p 2192) (p 3425) (p 4243) (p 4344) (p 4558) (derived105400 p h) (derived92946 p h)

theorem derived123203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4243) ∨ (p 4629) :=
  ElevenRUP.step123203 (p 4243) (p 4629) (p 4882) (derived105453 p h) (h 23767)

theorem derived123204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4243) ∨ (p 2737) ∨ (p 2608) ∨ (¬ p 2210) :=
  ElevenRUP.step123204 (p 2210) (p 2608) (p 2737) (p 4243) (p 5052) (derived105473 p h) (derived92982 p h)

theorem derived123218 (p : Nat → Prop) (h : Inputs p) :
    (p 2156) ∨ (p 3115) ∨ (¬ p 2284) ∨ (¬ p 2417) ∨ (¬ p 3201) ∨ (¬ p 2598) ∨ (¬ p 2145) :=
  ElevenRUP.step123218 (p 2145) (p 2156) (p 2284) (p 2417) (p 2598) (p 3115) (p 3201) (p 3951) (derived106536 p h) (derived93025 p h)

theorem derived123219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2598) ∨ (¬ p 2417) ∨ (¬ p 2950) ∨ (p 3115) ∨ (p 2156) ∨ (¬ p 2284) :=
  ElevenRUP.step123219 (p 2156) (p 2284) (p 2417) (p 2598) (p 2950) (p 3115) (p 3201) (p 3951) (p 4789) (derived105646 p h) (derived106536 p h) (derived93026 p h)

theorem derived123221 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (¬ p 3949) ∨ (¬ p 3156) ∨ (¬ p 2459) :=
  ElevenRUP.step123221 (p 2459) (p 3115) (p 3156) (p 3949) (p 4902) (derived105456 p h) (derived93037 p h)

theorem derived123223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3979) ∨ (p 3115) ∨ (¬ p 4322) ∨ (¬ p 3093) ∨ (¬ p 5119) ∨ (p 2946) ∨ (¬ p 3063) :=
  ElevenRUP.step123223 (p 2254) (p 2946) (p 3063) (p 3093) (p 3115) (p 3979) (p 4322) (p 5119) (derived105366 p h) (derived93041 p h)

theorem derived123224 (p : Nat → Prop) (h : Inputs p) :
    (p 3115) ∨ (p 3389) ∨ (p 2911) ∨ (¬ p 2972) ∨ (¬ p 2210) ∨ (¬ p 2284) ∨ (p 2459) :=
  ElevenRUP.step123224 (p 2210) (p 2284) (p 2459) (p 2911) (p 2972) (p 3115) (p 3389) (p 5193) (derived105488 p h) (derived93047 p h)

theorem derived123225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 3115) ∨ (p 2946) ∨ (¬ p 2598) ∨ (¬ p 4322) ∨ (¬ p 3201) :=
  ElevenRUP.step123225 (p 2598) (p 2946) (p 3115) (p 3201) (p 3868) (p 4322) (p 4789) (p 4826) (derived105444 p h) (derived105646 p h) (derived93059 p h)

theorem derived123226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3868) ∨ (p 3115) ∨ (¬ p 2922) ∨ (¬ p 4322) ∨ (p 2946) ∨ (¬ p 3379) :=
  ElevenRUP.step123226 (p 2254) (p 2922) (p 2946) (p 3115) (p 3379) (p 3868) (p 4322) (p 4826) (derived105366 p h) (derived105444 p h) (derived93060 p h)

theorem derived123229 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (p 3115) ∨ (¬ p 3366) ∨ (¬ p 2573) ∨ (¬ p 2352) ∨ (¬ p 3519) ∨ (¬ p 5059) ∨ (p 3136) ∨ (¬ p 2363) :=
  ElevenRUP.step123229 (p 2352) (p 2363) (p 2573) (p 2696) (p 3115) (p 3136) (p 3366) (p 3519) (p 4376) (p 5059) (derived106320 p h) (derived93064 p h)

theorem derived123231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 3156) ∨ (p 3115) ∨ (¬ p 3949) :=
  ElevenRUP.step123231 (p 3115) (p 3156) (p 3949) (p 3969) (p 5122) (derived105483 p h) (derived93070 p h)

theorem derived123232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4149) ∨ (p 2946) ∨ (¬ p 3641) ∨ (¬ p 2598) ∨ (¬ p 4322) ∨ (p 3115) ∨ (¬ p 5119) :=
  ElevenRUP.step123232 (p 2598) (p 2946) (p 3115) (p 3641) (p 4149) (p 4322) (p 4789) (p 5119) (derived105646 p h) (derived93072 p h)

theorem derived123235 (p : Nat → Prop) (h : Inputs p) :
    (p 3189) ∨ (¬ p 2122) ∨ (p 3256) ∨ (¬ p 2396) ∨ (p 2241) ∨ (¬ p 2774) ∨ (¬ p 3950) :=
  ElevenRUP.step123235 (p 2122) (p 2241) (p 2396) (p 2774) (p 3189) (p 3256) (p 3950) (p 4733) (derived105430 p h) (derived93079 p h)

theorem derived123237 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (p 3527) ∨ (¬ p 2911) ∨ (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 2132) :=
  ElevenRUP.step123237 (p 2132) (p 2274) (p 2860) (p 2911) (p 3399) (p 3527) (p 4712) (p 4733) (derived105430 p h) (derived105422 p h) (derived93086 p h)

theorem derived123238 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (p 3527) ∨ (¬ p 3125) ∨ (p 2459) ∨ (¬ p 2860) ∨ (¬ p 2132) :=
  ElevenRUP.step123238 (p 2132) (p 2459) (p 2860) (p 3125) (p 3399) (p 3527) (p 4330) (p 4733) (derived105430 p h) (derived106329 p h) (derived93087 p h)

theorem derived123246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2696) ∨ (p 3309) ∨ (¬ p 3156) ∨ (p 3093) ∨ (p 2177) :=
  ElevenRUP.step123246 (p 2177) (p 2696) (p 3093) (p 3136) (p 3156) (p 3309) (p 4733) (p 4902) (derived105430 p h) (derived105456 p h) (derived93097 p h)

theorem derived123247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 2406) ∨ (p 2373) ∨ (p 3379) ∨ (¬ p 2668) ∨ (¬ p 2797) :=
  ElevenRUP.step123247 (p 2373) (p 2406) (p 2668) (p 2696) (p 2797) (p 3379) (p 4134) (p 4733) (derived105430 p h) (derived105379 p h) (derived93098 p h)

theorem derived123250 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2655) ∨ (¬ p 2786) ∨ (p 2230) ∨ (p 3146) ∨ (p 3156) ∨ (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3654) ∨ (¬ p 3950) ∨ (¬ p 4241) :=
  ElevenRUP.step123250 (p 2230) (p 2655) (p 2761) (p 2786) (p 3146) (p 3156) (p 3461) (p 3654) (p 3950) (p 4241) (p 4789) (derived105646 p h) (derived93105 p h)

theorem derived123251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3791) ∨ (¬ p 2122) ∨ (p 3256) ∨ (p 3166) ∨ (¬ p 2774) ∨ (p 3266) :=
  ElevenRUP.step123251 (p 2122) (p 2774) (p 3166) (p 3256) (p 3266) (p 3791) (p 4789) (p 4826) (derived105444 p h) (derived105646 p h) (derived93106 p h)

theorem derived123252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2295) ∨ (p 2307) :=
  ElevenRUP.step123252 (p 2295) (p 2307) (p 2383) (p 2819) (p 4843) (derived105449 p h) (derived93114 p h)

theorem derived123255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4117) ∨ (¬ p 3461) ∨ (p 2230) ∨ (p 2373) ∨ (¬ p 3323) ∨ (¬ p 2331) ∨ (¬ p 5568) ∨ (¬ p 5123) :=
  ElevenRUP.step123255 (p 2230) (p 2331) (p 2373) (p 3323) (p 3461) (p 4117) (p 4729) (p 5123) (p 5568) (derived105429 p h) (derived93117 p h)

theorem derived123258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3931) ∨ (¬ p 2696) ∨ (p 3125) ∨ (p 2156) ∨ (¬ p 2685) ∨ (¬ p 2753) ∨ (p 3461) ∨ (¬ p 3645) :=
  ElevenRUP.step123258 (p 2156) (p 2685) (p 2696) (p 2753) (p 3125) (p 3461) (p 3645) (p 3931) (p 4826) (p 4877) (derived105451 p h) (derived105444 p h) (derived93123 p h)

theorem derived123259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4253) ∨ (¬ p 5503) ∨ (p 3461) ∨ (p 3125) ∨ (p 3425) ∨ (p 2156) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3645) :=
  ElevenRUP.step123259 (p 2156) (p 2753) (p 2911) (p 3125) (p 3425) (p 3461) (p 3645) (p 4253) (p 4877) (p 5503) (derived105451 p h) (derived93124 p h)

theorem derived123262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 3449) ∨ (¬ p 3323) ∨ (p 3073) ∨ (¬ p 2753) ∨ (¬ p 2210) ∨ (¬ p 2797) :=
  ElevenRUP.step123262 (p 2210) (p 2696) (p 2753) (p 2797) (p 3073) (p 3323) (p 3449) (p 4330) (p 4877) (derived106329 p h) (derived105451 p h) (derived93127 p h)

theorem derived123267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (¬ p 2748) ∨ (p 2668) ∨ (p 2363) ∨ (¬ p 2098) ∨ (¬ p 2252) ∨ (p 2598) ∨ (p 2331) :=
  ElevenRUP.step123267 (p 2098) (p 2252) (p 2331) (p 2363) (p 2598) (p 2668) (p 2748) (p 4019) (p 4749) (p 5122) (derived105432 p h) (derived105483 p h) (derived93141 p h)

theorem derived123268 (p : Nat → Prop) (h : Inputs p) :
    (p 3051) ∨ (¬ p 3368) ∨ (p 3115) ∨ (¬ p 2901) ∨ (¬ p 5059) ∨ (¬ p 3609) ∨ (¬ p 2098) ∨ (¬ p 2748) ∨ (p 2598) ∨ (¬ p 3645) :=
  ElevenRUP.step123268 (p 2098) (p 2598) (p 2748) (p 2901) (p 3051) (p 3115) (p 3368) (p 3609) (p 3645) (p 4749) (p 5059) (derived105432 p h) (derived93147 p h)

theorem derived123271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 4804) ∨ (¬ p 3425) ∨ (p 2881) :=
  ElevenRUP.step123271 (p 2098) (p 2881) (p 3425) (p 4804) (p 4898) (derived105455 p h) (derived93166 p h)

theorem derived123273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (p 2493) ∨ (p 2459) ∨ (p 3379) ∨ (¬ p 3609) ∨ (p 2352) :=
  ElevenRUP.step123273 (p 2098) (p 2352) (p 2459) (p 2493) (p 3379) (p 3609) (p 4503) (p 4733) (derived105430 p h) (derived106530 p h) (derived93169 p h)

theorem derived123276 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4019) ∨ (p 3115) ∨ (¬ p 5119) ∨ (p 2598) ∨ (p 2946) ∨ (¬ p 2098) ∨ (¬ p 3361) ∨ (¬ p 4322) :=
  ElevenRUP.step123276 (p 2098) (p 2598) (p 2946) (p 3115) (p 3361) (p 4019) (p 4322) (p 4749) (p 5119) (derived105432 p h) (derived93178 p h)

theorem derived123277 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (p 2696) ∨ (¬ p 2210) ∨ (¬ p 2274) ∨ (p 3323) ∨ (¬ p 2192) ∨ (¬ p 4620) :=
  ElevenRUP.step123277 (p 2192) (p 2210) (p 2274) (p 2696) (p 2797) (p 3323) (p 4620) (p 4736) (derived105431 p h) (derived93185 p h)

theorem derived123279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2441) ∨ (p 2911) ∨ (¬ p 2563) ∨ (¬ p 2881) :=
  ElevenRUP.step123279 (p 2441) (p 2563) (p 2881) (p 2911) (p 4555) (derived105542 p h) (derived93202 p h)

theorem derived123282 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (p 3286) ∨ (¬ p 3246) ∨ (¬ p 5284) ∨ (¬ p 2210) ∨ (¬ p 3266) ∨ (¬ p 3950) :=
  ElevenRUP.step123282 (p 2210) (p 2254) (p 2891) (p 3246) (p 3266) (p 3286) (p 3950) (p 5284) (derived105366 p h) (derived93265 p h)

theorem derived123283 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3362) ∨ (¬ p 3333) ∨ (¬ p 3266) ∨ (¬ p 4332) ∨ (p 2850) ∨ (p 3286) ∨ (¬ p 5284) ∨ (¬ p 2753) ∨ (¬ p 2230) ∨ (¬ p 2252) :=
  ElevenRUP.step123283 (p 2230) (p 2252) (p 2750) (p 2753) (p 2850) (p 3266) (p 3286) (p 3333) (p 3362) (p 4332) (p 5284) (derived106345 p h) (derived93266 p h)

theorem derived123290 (p : Nat → Prop) (h : Inputs p) :
    (p 3379) ∨ (¬ p 3319) ∨ (¬ p 3093) ∨ (¬ p 3266) ∨ (p 3286) ∨ (¬ p 3366) ∨ (¬ p 5284) ∨ (¬ p 4236) :=
  ElevenRUP.step123290 (p 3093) (p 3266) (p 3286) (p 3319) (p 3366) (p 3379) (p 4236) (p 4330) (p 4376) (p 5284) (derived106320 p h) (derived106329 p h) (derived93289 p h)

theorem derived123293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3969) ∨ (¬ p 2230) ∨ (¬ p 3519) ∨ (¬ p 3366) ∨ (¬ p 2373) ∨ (p 2696) ∨ (p 3755) ∨ (¬ p 5284) ∨ (¬ p 5119) :=
  ElevenRUP.step123293 (p 2230) (p 2373) (p 2696) (p 3366) (p 3519) (p 3755) (p 3969) (p 4376) (p 5119) (p 5284) (derived106320 p h) (derived93303 p h)

theorem derived123296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (p 2573) ∨ (¬ p 4710) ∨ (p 2122) :=
  ElevenRUP.step123296 (p 2122) (p 2573) (p 3389) (p 4710) (p 5222) (derived105793 p h) (derived93330 p h)

theorem derived123298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (p 2122) ∨ (p 2230) ∨ (¬ p 3093) ∨ (p 3016) ∨ (p 2440) :=
  ElevenRUP.step123298 (p 2122) (p 2230) (p 2440) (p 3016) (p 3093) (p 3309) (p 5193) (p 5222) (derived105488 p h) (derived105793 p h) (derived93332 p h)

theorem derived123302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4909) ∨ (¬ p 3051) ∨ (p 2911) ∨ (¬ p 2441) ∨ (¬ p 3527) :=
  ElevenRUP.step123302 (p 2441) (p 2911) (p 3051) (p 3527) (p 4539) (p 4909) (derived105395 p h) (derived93365 p h)

theorem derived123304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2778) ∨ (¬ p 2132) ∨ (p 3654) ∨ (¬ p 3319) ∨ (¬ p 4759) ∨ (¬ p 2742) :=
  ElevenRUP.step123304 (p 2132) (p 2742) (p 2778) (p 3319) (p 3654) (p 4759) (p 5052) (derived105473 p h) (derived93379 p h)

theorem derived123305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 2533) ∨ (p 3266) ∨ (p 2363) :=
  ElevenRUP.step123305 (p 2363) (p 2533) (p 3266) (p 3680) (p 4134) (derived105379 p h) (derived93383 p h)

theorem derived123306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 2533) ∨ (p 3266) ∨ (p 2459) :=
  ElevenRUP.step123306 (p 2459) (p 2533) (p 3266) (p 3680) (p 4905) (derived105995 p h) (derived93385 p h)

theorem derived123312 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2427) ∨ (¬ p 2748) ∨ (¬ p 2230) ∨ (p 3189) ∨ (¬ p 3873) ∨ (p 2696) ∨ (p 3256) ∨ (¬ p 3950) :=
  ElevenRUP.step123312 (p 2230) (p 2427) (p 2696) (p 2748) (p 3189) (p 3246) (p 3256) (p 3873) (p 3950) (p 5190) (derived105487 p h) (derived93392 p h)

theorem derived123314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3873) ∨ (p 4419) :=
  ElevenRUP.step123314 (p 3873) (p 4419) (p 5190) (derived105487 p h) (h 24353)

theorem derived123315 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 3051) ∨ (¬ p 2246) ∨ (¬ p 2958) ∨ (p 2901) :=
  ElevenRUP.step123315 (p 2246) (p 2751) (p 2901) (p 2958) (p 3051) (p 3136) (derived106343 p h) (derived93402 p h)

theorem derived123317 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 2437) ∨ (¬ p 2246) ∨ (¬ p 3389) ∨ (¬ p 2663) :=
  ElevenRUP.step123317 (p 2246) (p 2437) (p 2630) (p 2663) (p 2751) (p 3389) (derived106343 p h) (derived93405 p h)

theorem derived123320 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 3379) ∨ (p 2241) :=
  ElevenRUP.step123320 (p 2241) (p 2630) (p 2751) (p 3379) (derived106343 p h) (derived93410 p h)

theorem derived123321 (p : Nat → Prop) (h : Inputs p) :
    (p 3136) ∨ (¬ p 2210) ∨ (p 2241) ∨ (¬ p 4282) :=
  ElevenRUP.step123321 (p 2210) (p 2241) (p 2751) (p 3136) (p 4282) (derived106343 p h) (derived93411 p h)

theorem derived123323 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (p 3389) ∨ (¬ p 2662) ∨ (¬ p 2922) ∨ (¬ p 4281) :=
  ElevenRUP.step123323 (p 2630) (p 2662) (p 2751) (p 2922) (p 3389) (p 4281) (derived106343 p h) (derived93414 p h)

theorem derived123327 (p : Nat → Prop) (h : Inputs p) :
    (p 2797) ∨ (¬ p 3319) ∨ (¬ p 4759) ∨ (p 3323) :=
  ElevenRUP.step123327 (p 2751) (p 2797) (p 3319) (p 3323) (p 4759) (derived106343 p h) (derived93418 p h)

theorem derived123328 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) ∨ (¬ p 2493) ∨ (¬ p 4281) ∨ (p 3016) :=
  ElevenRUP.step123328 (p 2493) (p 2630) (p 2751) (p 3016) (p 4281) (derived106343 p h) (derived93419 p h)

theorem derived123331 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) ∨ (¬ p 2727) ∨ (¬ p 2245) ∨ (¬ p 2608) :=
  ElevenRUP.step123331 (p 2245) (p 2608) (p 2651) (p 2727) (p 2744) (derived106503 p h) (derived93433 p h)

theorem derived123333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2245) ∨ (¬ p 2881) ∨ (¬ p 2553) ∨ (¬ p 3422) ∨ (p 2807) ∨ (p 2264) :=
  ElevenRUP.step123333 (p 2245) (p 2264) (p 2553) (p 2598) (p 2807) (p 2881) (p 3422) (p 4559) (p 4733) (derived105430 p h) (derived105701 p h) (derived93442 p h)

end ElevenLogic
