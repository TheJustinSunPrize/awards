import SunPrize.Certificate.Derived060
import SunPrize.Certificate.Logic061
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived112263 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 4341) ∨ (p 3073) ∨ (¬ p 3256) ∨ (¬ p 2440) ∨ (¬ p 3019) ∨ (¬ p 2933) :=
  ElevenRUP.step112263 (p 2440) (p 2933) (p 3019) (p 3073) (p 3256) (p 3527) (p 3544) (p 4341) (p 4646) (derived105534 p h) (derived95553 p h) (derived102269 p h)

theorem derived112265 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (p 3073) ∨ (¬ p 3576) ∨ (¬ p 2668) ∨ (¬ p 2797) ∨ (¬ p 3425) ∨ (¬ p 2737) ∨ (¬ p 2459) :=
  ElevenRUP.step112265 (p 2459) (p 2668) (p 2737) (p 2797) (p 3073) (p 3425) (p 3527) (p 3544) (p 3576) (p 4133) (derived105712 p h) (derived88107 p h) (derived102269 p h)

theorem derived112267 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 3016) ∨ (¬ p 2352) ∨ (¬ p 2459) ∨ (p 3399) ∨ (p 3073) ∨ (¬ p 2651) :=
  ElevenRUP.step112267 (p 2248) (p 2352) (p 2459) (p 2651) (p 3016) (p 3073) (p 3399) (p 3527) (p 3544) (p 4133) (derived105365 p h) (derived105712 p h) (derived99054 p h) (derived102269 p h)

theorem derived112275 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2373) ∨ (p 2807) ∨ (¬ p 2230) ∨ (¬ p 2727) ∨ (p 3073) ∨ (¬ p 2656) ∨ (¬ p 3037) ∨ (¬ p 2459) :=
  ElevenRUP.step112275 (p 2230) (p 2249) (p 2373) (p 2459) (p 2656) (p 2727) (p 2807) (p 3037) (p 3073) (p 3527) (p 3544) (p 4902) (derived105456 p h) (derived106513 p h) (derived82299 p h) (derived102269 p h)

theorem derived112278 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2761) ∨ (¬ p 3680) :=
  ElevenRUP.step112278 (p 2761) (p 3246) (p 3680) (p 4382) (derived102083 p h) (derived93101 p h)

theorem derived112282 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2972) ∨ (¬ p 2891) ∨ (¬ p 2396) :=
  ElevenRUP.step112282 (p 2396) (p 2891) (p 2972) (p 3246) (p 4382) (p 4556) (derived105399 p h) (derived76422 p h) (derived93101 p h)

theorem derived112283 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2417) ∨ (¬ p 2891) ∨ (p 2972) :=
  ElevenRUP.step112283 (p 2417) (p 2891) (p 2972) (p 3246) (p 4382) (p 4647) (derived105412 p h) (derived76423 p h) (derived93101 p h)

theorem derived112284 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2972) ∨ (¬ p 2881) ∨ (¬ p 2891) :=
  ElevenRUP.step112284 (p 2881) (p 2891) (p 2972) (p 3246) (p 4382) (p 4666) (derived105658 p h) (derived76425 p h) (derived93101 p h)

theorem derived112285 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2891) ∨ (p 2427) ∨ (p 2972) ∨ (p 2761) :=
  ElevenRUP.step112285 (p 2427) (p 2761) (p 2891) (p 2972) (p 3246) (p 4382) (derived76437 p h) (derived93101 p h)

theorem derived112286 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2870) ∨ (p 2761) ∨ (¬ p 4032) ∨ (¬ p 3051) :=
  ElevenRUP.step112286 (p 2761) (p 2870) (p 3051) (p 3246) (p 4032) (p 4382) (derived76695 p h) (derived93101 p h)

theorem derived112287 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4032) ∨ (¬ p 3051) ∨ (¬ p 2881) :=
  ElevenRUP.step112287 (p 2881) (p 3051) (p 3246) (p 4032) (p 4382) (p 4666) (derived105658 p h) (derived41259 p h) (derived93101 p h)

theorem derived112288 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4032) ∨ (¬ p 2396) ∨ (p 2427) ∨ (¬ p 3051) :=
  ElevenRUP.step112288 (p 2396) (p 2427) (p 3051) (p 3246) (p 4032) (p 4382) (derived76697 p h) (derived93101 p h)

theorem derived112289 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2417) ∨ (¬ p 4032) ∨ (¬ p 3051) :=
  ElevenRUP.step112289 (p 2417) (p 3051) (p 3246) (p 4032) (p 4382) (p 4647) (derived105412 p h) (derived54707 p h) (derived93101 p h)

theorem derived112290 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2761) ∨ (¬ p 4032) ∨ (p 2427) ∨ (¬ p 3051) :=
  ElevenRUP.step112290 (p 2427) (p 2761) (p 3051) (p 3246) (p 4032) (p 4382) (derived76724 p h) (derived93101 p h)

theorem derived112291 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2449) ∨ (¬ p 2870) ∨ (p 3105) :=
  ElevenRUP.step112291 (p 2449) (p 2870) (p 3105) (p 3246) (p 4362) (p 4382) (derived106173 p h) (derived84460 p h) (derived93101 p h)

theorem derived112292 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 3105) ∨ (¬ p 2870) ∨ (¬ p 2396) :=
  ElevenRUP.step112292 (p 2396) (p 2870) (p 3105) (p 3246) (p 4382) (p 4556) (derived105399 p h) (derived84506 p h) (derived93101 p h)

theorem derived112294 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2982) ∨ (¬ p 3434) ∨ (¬ p 2427) :=
  ElevenRUP.step112294 (p 2427) (p 2982) (p 3246) (p 3434) (p 4382) (p 4898) (derived105455 p h) (derived92049 p h) (derived93101 p h)

theorem derived112295 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2449) ∨ (p 2982) ∨ (¬ p 2427) :=
  ElevenRUP.step112295 (p 2427) (p 2449) (p 2982) (p 3246) (p 4362) (p 4382) (derived106173 p h) (derived92051 p h) (derived93101 p h)

theorem derived112296 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2982) ∨ (¬ p 2427) ∨ (¬ p 2396) :=
  ElevenRUP.step112296 (p 2396) (p 2427) (p 2982) (p 3246) (p 4382) (p 4556) (derived105399 p h) (derived92068 p h) (derived93101 p h)

theorem derived112297 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 3115) ∨ (¬ p 2396) ∨ (¬ p 2901) :=
  ElevenRUP.step112297 (p 2396) (p 2901) (p 3115) (p 3246) (p 4382) (p 4556) (derived105399 p h) (derived93016 p h) (derived93101 p h)

theorem derived112299 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 3105) ∨ (¬ p 2136) ∨ (p 2761) ∨ (p 3051) ∨ (¬ p 2870) :=
  ElevenRUP.step112299 (p 2136) (p 2761) (p 2870) (p 3051) (p 3105) (p 3246) (p 4382) (derived84519 p h) (derived93101 p h)

theorem derived112300 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 4914) ∨ (¬ p 3543) ∨ (¬ p 2870) ∨ (p 3105) ∨ (¬ p 3516) :=
  ElevenRUP.step112300 (p 2870) (p 3105) (p 3246) (p 3516) (p 3543) (p 4382) (p 4914) (derived84558 p h) (derived93101 p h)

theorem derived112304 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (p 2982) ∨ (¬ p 3543) ∨ (¬ p 3516) ∨ (¬ p 4914) ∨ (¬ p 2427) :=
  ElevenRUP.step112304 (p 2427) (p 2982) (p 3246) (p 3516) (p 3543) (p 4382) (p 4914) (derived92128 p h) (derived93101 p h)

theorem derived112309 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 2761) ∨ (¬ p 4129) ∨ (p 2982) ∨ (¬ p 3698) ∨ (¬ p 2870) :=
  ElevenRUP.step112309 (p 2761) (p 2870) (p 2982) (p 3246) (p 3698) (p 4129) (p 4382) (derived108322 p h) (derived93101 p h)

theorem derived112321 (p : Nat → Prop) (h : Inputs p) :
    (p 3246) ∨ (¬ p 3005) ∨ (¬ p 3945) ∨ (¬ p 2331) ∨ (p 2797) ∨ (p 2982) ∨ (p 3051) ∨ (¬ p 4117) ∨ (¬ p 3904) ∨ (¬ p 2427) ∨ (¬ p 4550) :=
  ElevenRUP.step112321 (p 2331) (p 2427) (p 2797) (p 2982) (p 3005) (p 3051) (p 3246) (p 3904) (p 3945) (p 4117) (p 4382) (p 4550) (p 4729) (derived105429 p h) (derived101581 p h) (derived93101 p h)

theorem derived112322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3256) ∨ (¬ p 2363) :=
  ElevenRUP.step112322 (p 2363) (p 2668) (p 3256) (p 4417) (h 6804) (derived96398 p h)

theorem derived112323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2187) ∨ (¬ p 3166) ∨ (p 2331) :=
  ElevenRUP.step112323 (p 2187) (p 2331) (p 2668) (p 3166) (p 4417) (derived75874 p h) (derived96398 p h)

theorem derived112324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3189) ∨ (p 2641) ∨ (p 2187) :=
  ElevenRUP.step112324 (p 2187) (p 2641) (p 2668) (p 3189) (p 4417) (derived91927 p h) (derived96398 p h)

theorem derived112325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3005) ∨ (p 2187) ∨ (p 2797) :=
  ElevenRUP.step112325 (p 2187) (p 2668) (p 2797) (p 3005) (p 4417) (derived94335 p h) (derived96398 p h)

theorem derived112331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3189) ∨ (p 2641) ∨ (p 2295) :=
  ElevenRUP.step112331 (p 2295) (p 2641) (p 2668) (p 3189) (p 4405) (p 4417) (derived105512 p h) (derived91988 p h) (derived96398 p h)

theorem derived112332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2797) ∨ (p 2331) ∨ (¬ p 3166) ∨ (¬ p 2363) :=
  ElevenRUP.step112332 (p 2331) (p 2363) (p 2668) (p 2797) (p 3166) (p 4417) (derived92276 p h) (derived96398 p h)

theorem derived112333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2819) ∨ (p 2331) ∨ (¬ p 3166) :=
  ElevenRUP.step112333 (p 2331) (p 2668) (p 2819) (p 3166) (p 4417) (p 4843) (derived105449 p h) (derived93111 p h) (derived96398 p h)

theorem derived112335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3005) ∨ (p 2295) ∨ (p 2797) :=
  ElevenRUP.step112335 (p 2295) (p 2668) (p 2797) (p 3005) (p 4405) (p 4417) (derived105512 p h) (derived94058 p h) (derived96398 p h)

theorem derived112336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2352) ∨ (p 2331) ∨ (¬ p 3166) :=
  ElevenRUP.step112336 (p 2331) (p 2352) (p 2668) (p 3166) (p 4417) (p 4976) (derived105465 p h) (derived94337 p h) (derived96398 p h)

theorem derived112338 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3005) ∨ (p 2797) ∨ (p 2383) :=
  ElevenRUP.step112338 (p 2383) (p 2668) (p 2797) (p 3005) (p 4417) (p 4581) (derived105405 p h) (derived98398 p h) (derived96398 p h)

theorem derived112345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3189) ∨ (p 2641) ∨ (¬ p 2667) ∨ (p 2307) :=
  ElevenRUP.step112345 (p 2307) (p 2641) (p 2667) (p 2668) (p 3189) (p 4405) (p 4417) (derived105512 p h) (derived91929 p h) (derived96398 p h)

theorem derived112346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3005) ∨ (p 2630) ∨ (p 2352) ∨ (¬ p 4117) ∨ (¬ p 2651) :=
  ElevenRUP.step112346 (p 2352) (p 2630) (p 2651) (p 2668) (p 3005) (p 4117) (p 4417) (derived93972 p h) (derived96398 p h)

theorem derived112350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3979) ∨ (¬ p 3005) ∨ (p 2797) ∨ (¬ p 4117) ∨ (¬ p 2331) :=
  ElevenRUP.step112350 (p 2331) (p 2668) (p 2797) (p 3005) (p 3979) (p 4117) (p 4417) (derived101156 p h) (derived96398 p h)

theorem derived112351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3256) ∨ (¬ p 3319) ∨ (p 3309) ∨ (¬ p 3707) ∨ (¬ p 5284) :=
  ElevenRUP.step112351 (p 2668) (p 3256) (p 3309) (p 3319) (p 3707) (p 4417) (p 5284) (derived111103 p h) (derived96398 p h)

theorem derived112352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3256) ∨ (¬ p 4422) ∨ (¬ p 5284) ∨ (¬ p 3276) ∨ (p 2553) :=
  ElevenRUP.step112352 (p 2553) (p 2668) (p 3256) (p 3276) (p 4417) (p 4422) (p 5284) (derived111104 p h) (derived96398 p h)

theorem derived112355 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2088) ∨ (¬ p 4114) ∨ (¬ p 2578) ∨ (p 2553) ∨ (p 3256) :=
  ElevenRUP.step112355 (p 2088) (p 2553) (p 2578) (p 2668) (p 3256) (p 4114) (p 4405) (p 4417) (derived105512 p h) (derived98486 p h) (derived96398 p h)

theorem derived112361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3979) ∨ (p 3276) ∨ (p 2598) ∨ (¬ p 5119) ∨ (¬ p 3189) ∨ (¬ p 5160) ∨ (¬ p 2241) :=
  ElevenRUP.step112361 (p 2241) (p 2598) (p 2668) (p 3189) (p 3276) (p 3979) (p 4417) (p 4736) (p 5119) (p 5160) (derived105431 p h) (derived99803 p h) (derived96398 p h)

theorem derived112363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3189) ∨ (p 2598) ∨ (p 2911) ∨ (¬ p 2331) ∨ (p 2641) ∨ (¬ p 2253) ∨ (p 3201) :=
  ElevenRUP.step112363 (p 2253) (p 2331) (p 2598) (p 2641) (p 2668) (p 2911) (p 3189) (p 3201) (p 4133) (p 4417) (p 4736) (derived105431 p h) (derived105712 p h) (derived91930 p h) (derived96398 p h)

theorem derived112368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3399) ∨ (¬ p 3379) :=
  ElevenRUP.step112368 (p 2922) (p 2934) (p 3379) (p 3399) (h 6549) (derived96899 p h)

theorem derived112370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3038) ∨ (¬ p 4281) :=
  ElevenRUP.step112370 (p 2922) (p 2934) (p 3038) (p 4281) (h 23033) (derived96899 p h)

theorem derived112371 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (p 3687) ∨ (¬ p 3541) :=
  ElevenRUP.step112371 (p 2922) (p 2934) (p 3541) (p 3687) (h 6633) (derived96899 p h)

theorem derived112372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3527) ∨ (¬ p 2573) ∨ (p 2264) ∨ (p 2493) :=
  ElevenRUP.step112372 (p 2264) (p 2493) (p 2573) (p 2922) (p 2934) (p 3527) (derived76247 p h) (derived96899 p h)

theorem derived112373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3631) ∨ (p 2406) ∨ (p 2417) :=
  ElevenRUP.step112373 (p 2406) (p 2417) (p 2922) (p 2934) (p 3631) (p 4646) (derived105534 p h) (derived76248 p h) (derived96899 p h)

theorem derived112376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3527) ∨ (p 2406) ∨ (p 2911) :=
  ElevenRUP.step112376 (p 2406) (p 2911) (p 2922) (p 2934) (p 3527) (p 4646) (derived105534 p h) (derived76254 p h) (derived96899 p h)

theorem derived112378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3527) ∨ (p 2437) ∨ (p 2911) :=
  ElevenRUP.step112378 (p 2437) (p 2911) (p 2922) (p 2934) (p 3527) (p 4814) (derived105440 p h) (derived76260 p h) (derived96899 p h)

theorem derived112384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3527) ∨ (p 2177) ∨ (p 2406) ∨ (¬ p 2230) :=
  ElevenRUP.step112384 (p 2177) (p 2230) (p 2406) (p 2922) (p 2934) (p 3527) (derived87450 p h) (derived96899 p h)

theorem derived112390 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3631) ∨ (¬ p 4279) ∨ (p 2437) ∨ (p 3516) :=
  ElevenRUP.step112390 (p 2437) (p 2922) (p 2934) (p 3516) (p 3631) (p 4279) (p 4814) (derived105440 p h) (derived76263 p h) (derived96899 p h)

theorem derived112397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 5660) ∨ (¬ p 4075) ∨ (¬ p 4204) ∨ (p 2406) ∨ (¬ p 2187) :=
  ElevenRUP.step112397 (p 2187) (p 2406) (p 2922) (p 2934) (p 4075) (p 4204) (p 5660) (derived97705 p h) (derived96899 p h)

theorem derived112402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 4031) ∨ (¬ p 3527) ∨ (p 2341) ∨ (p 2493) ∨ (¬ p 4984) :=
  ElevenRUP.step112402 (p 2341) (p 2493) (p 2922) (p 2934) (p 3527) (p 4031) (p 4715) (p 4984) (derived105423 p h) (derived76269 p h) (derived96899 p h)

theorem derived112407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 2641) ∨ (¬ p 3631) ∨ (¬ p 3093) ∨ (¬ p 5206) ∨ (¬ p 4281) ∨ (p 3516) :=
  ElevenRUP.step112407 (p 2641) (p 2922) (p 2934) (p 3093) (p 3516) (p 3631) (p 4281) (p 5206) (derived108894 p h) (derived96899 p h)

theorem derived112410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3631) ∨ (¬ p 4984) ∨ (¬ p 4031) ∨ (p 3516) ∨ (¬ p 3590) ∨ (p 3422) :=
  ElevenRUP.step112410 (p 2922) (p 2934) (p 3422) (p 3516) (p 3590) (p 3631) (p 4031) (p 4715) (p 4984) (derived105423 p h) (derived76246 p h) (derived96899 p h)

theorem derived112412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3527) ∨ (p 2911) ∨ (p 2870) ∨ (¬ p 2860) ∨ (p 2156) ∨ (¬ p 3379) :=
  ElevenRUP.step112412 (p 2156) (p 2860) (p 2870) (p 2911) (p 2922) (p 2934) (p 3379) (p 3527) (p 4277) (derived105380 p h) (derived86676 p h) (derived96899 p h)

theorem derived112413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3631) ∨ (¬ p 2143) ∨ (p 2493) ∨ (p 3516) ∨ (¬ p 4984) ∨ (¬ p 3695) :=
  ElevenRUP.step112413 (p 2143) (p 2493) (p 2922) (p 2934) (p 3516) (p 3631) (p 3695) (p 4715) (p 4984) (derived105423 p h) (derived91212 p h) (derived96899 p h)

theorem derived112415 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 3461) ∨ (¬ p 3680) :=
  ElevenRUP.step112415 (p 3125) (p 3461) (p 3680) (p 4033) (derived102086 p h) (derived92027 p h)

theorem derived112416 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 4032) ∨ (¬ p 3323) ∨ (¬ p 2156) :=
  ElevenRUP.step112416 (p 2156) (p 3125) (p 3323) (p 4032) (p 4033) (derived76699 p h) (derived92027 p h)

theorem derived112423 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 2192) ∨ (p 2972) ∨ (p 2563) ∨ (p 3461) :=
  ElevenRUP.step112423 (p 2192) (p 2563) (p 2972) (p 3125) (p 3461) (p 4033) (derived76449 p h) (derived92027 p h)

theorem derived112424 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3564) ∨ (¬ p 4032) ∨ (¬ p 2156) :=
  ElevenRUP.step112424 (p 2156) (p 3125) (p 3564) (p 4032) (p 4033) (p 4718) (derived105425 p h) (derived51446 p h) (derived92027 p h)

theorem derived112425 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2284) ∨ (¬ p 2156) ∨ (p 3461) ∨ (¬ p 4032) :=
  ElevenRUP.step112425 (p 2156) (p 2284) (p 3125) (p 3461) (p 4032) (p 4033) (derived76706 p h) (derived92027 p h)

theorem derived112426 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2563) ∨ (¬ p 4032) ∨ (¬ p 2156) ∨ (p 3461) :=
  ElevenRUP.step112426 (p 2156) (p 2563) (p 3125) (p 3461) (p 4032) (p 4033) (derived76707 p h) (derived92027 p h)

theorem derived112428 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3564) ∨ (p 2553) ∨ (p 3115) ∨ (¬ p 2284) :=
  ElevenRUP.step112428 (p 2284) (p 2553) (p 3115) (p 3125) (p 3564) (p 4033) (derived79512 p h) (derived92027 p h)

theorem derived112429 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2982) ∨ (¬ p 3266) ∨ (p 3461) ∨ (¬ p 2563) :=
  ElevenRUP.step112429 (p 2563) (p 2982) (p 3125) (p 3266) (p 3461) (p 4033) (derived82468 p h) (derived92027 p h)

theorem derived112430 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 3115) ∨ (¬ p 2284) ∨ (p 3461) ∨ (p 2860) :=
  ElevenRUP.step112430 (p 2284) (p 2860) (p 3115) (p 3125) (p 3461) (p 4033) (derived83294 p h) (derived92027 p h)

theorem derived112432 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 3461) ∨ (¬ p 2860) ∨ (p 3105) ∨ (p 2156) :=
  ElevenRUP.step112432 (p 2156) (p 2860) (p 3105) (p 3125) (p 3461) (p 4033) (derived84531 p h) (derived92027 p h)

theorem derived112433 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2982) ∨ (p 3461) ∨ (p 2156) ∨ (¬ p 2563) :=
  ElevenRUP.step112433 (p 2156) (p 2563) (p 2982) (p 3125) (p 3461) (p 4033) (derived85487 p h) (derived92027 p h)

theorem derived112437 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 3115) ∨ (¬ p 2274) ∨ (¬ p 2284) ∨ (¬ p 4620) :=
  ElevenRUP.step112437 (p 2274) (p 2284) (p 3115) (p 3125) (p 4033) (p 4620) (derived93055 p h) (derived92027 p h)

theorem derived112438 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3461) ∨ (¬ p 3737) ∨ (¬ p 4032) ∨ (¬ p 2156) :=
  ElevenRUP.step112438 (p 2156) (p 3125) (p 3461) (p 3737) (p 4032) (p 4033) (derived107876 p h) (derived92027 p h)

theorem derived112440 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 2192) ∨ (¬ p 3096) ∨ (¬ p 2553) ∨ (p 2972) ∨ (¬ p 4620) :=
  ElevenRUP.step112440 (p 2192) (p 2553) (p 2972) (p 3096) (p 3125) (p 4033) (p 4620) (derived76448 p h) (derived92027 p h)

theorem derived112442 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3564) ∨ (¬ p 2284) ∨ (p 3105) ∨ (¬ p 5051) ∨ (p 2352) :=
  ElevenRUP.step112442 (p 2284) (p 2352) (p 3105) (p 3125) (p 3564) (p 4033) (p 5051) (derived84591 p h) (derived92027 p h)

theorem derived112445 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 3115) ∨ (¬ p 3483) ∨ (¬ p 2563) ∨ (¬ p 4241) ∨ (¬ p 4401) :=
  ElevenRUP.step112445 (p 2563) (p 3115) (p 3125) (p 3483) (p 4033) (p 4241) (p 4401) (derived93054 p h) (derived92027 p h)

theorem derived112446 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3918) ∨ (p 2982) ∨ (p 2122) ∨ (¬ p 3319) ∨ (¬ p 2563) :=
  ElevenRUP.step112446 (p 2122) (p 2563) (p 2982) (p 3125) (p 3319) (p 3918) (p 4033) (derived95298 p h) (derived92027 p h)

theorem derived112448 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (p 2982) ∨ (¬ p 4620) ∨ (¬ p 2373) ∨ (¬ p 4197) ∨ (¬ p 3696) ∨ (¬ p 2307) :=
  ElevenRUP.step112448 (p 2307) (p 2373) (p 2982) (p 3125) (p 3696) (p 4033) (p 4197) (p 4620) (derived76769 p h) (derived92027 p h)

theorem derived112454 (p : Nat → Prop) (h : Inputs p) :
    (p 3125) ∨ (¬ p 3256) ∨ (¬ p 3506) ∨ (p 3105) ∨ (¬ p 3166) ∨ (¬ p 2860) ∨ (p 3266) ∨ (¬ p 2136) ∨ (p 2156) :=
  ElevenRUP.step112454 (p 2136) (p 2156) (p 2860) (p 3105) (p 3125) (p 3166) (p 3256) (p 3266) (p 3506) (p 4033) (derived110984 p h) (derived92027 p h)

theorem derived112462 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3083) ∨ (¬ p 3343) :=
  ElevenRUP.step112462 (p 2528) (p 3083) (p 3343) (p 4045) (derived79484 p h) (derived98809 p h)

theorem derived112463 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3192) ∨ (p 3875) :=
  ElevenRUP.step112463 (p 2528) (p 3192) (p 3875) (p 4045) (h 19347) (derived98809 p h)

theorem derived112464 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3193) ∨ (¬ p 2509) :=
  ElevenRUP.step112464 (p 2509) (p 2528) (p 3193) (p 4045) (h 6010) (derived98809 p h)

theorem derived112465 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 4635) ∨ (¬ p 4186) :=
  ElevenRUP.step112465 (p 2528) (p 4045) (p 4186) (p 4635) (h 19728) (derived98809 p h)

theorem derived112466 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 2470) ∨ (¬ p 3355) :=
  ElevenRUP.step112466 (p 2470) (p 2528) (p 3355) (p 4045) (h 30133) (derived98809 p h)

theorem derived112468 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3333) ∨ (p 3641) :=
  ElevenRUP.step112468 (p 2528) (p 3333) (p 3641) (p 4045) (derived95597 p h) (derived98809 p h)

theorem derived112469 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 4440) ∨ (¬ p 4404) ∨ (¬ p 2459) :=
  ElevenRUP.step112469 (p 2459) (p 2528) (p 4045) (p 4404) (p 4440) (h 16875) (derived98809 p h)

theorem derived112470 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 4440) ∨ (¬ p 2088) ∨ (¬ p 2475) :=
  ElevenRUP.step112470 (p 2088) (p 2475) (p 2528) (p 4045) (p 4440) (h 6892) (derived98809 p h)

theorem derived112474 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 3343) ∨ (¬ p 2630) ∨ (¬ p 2737) ∨ (¬ p 2608) :=
  ElevenRUP.step112474 (p 2528) (p 2608) (p 2630) (p 2737) (p 3343) (p 4045) (derived46100 p h) (derived98809 p h)

theorem derived112477 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3276) ∨ (¬ p 3266) ∨ (¬ p 2459) :=
  ElevenRUP.step112477 (p 2459) (p 2528) (p 3266) (p 3276) (p 4045) (p 4420) (derived105707 p h) (derived99594 p h) (derived98809 p h)

theorem derived112483 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 2363) ∨ (¬ p 3461) ∨ (¬ p 2459) ∨ (p 3276) :=
  ElevenRUP.step112483 (p 2363) (p 2459) (p 2528) (p 3276) (p 3461) (p 4045) (derived111674 p h) (derived98809 p h)

theorem derived112485 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3193) ∨ (¬ p 4157) ∨ (p 2493) ∨ (p 2187) :=
  ElevenRUP.step112485 (p 2187) (p 2493) (p 2528) (p 3193) (p 4045) (p 4157) (p 4718) (derived105425 p h) (derived81722 p h) (derived98809 p h)

theorem derived112496 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (p 3156) ∨ (¬ p 3367) ∨ (p 3051) ∨ (¬ p 2901) ∨ (¬ p 2608) ∨ (¬ p 3333) :=
  ElevenRUP.step112496 (p 2528) (p 2608) (p 2901) (p 3051) (p 3156) (p 3333) (p 3367) (p 4045) (p 4158) (derived106187 p h) (derived92846 p h) (derived98809 p h)

theorem derived112498 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2727) ∨ (¬ p 2241) ∨ (¬ p 4119) ∨ (p 3051) ∨ (p 3146) ∨ (¬ p 2459) ∨ (¬ p 3343) :=
  ElevenRUP.step112498 (p 2241) (p 2459) (p 2528) (p 2727) (p 3051) (p 3146) (p 3343) (p 4045) (p 4119) (p 4420) (derived105707 p h) (derived92837 p h) (derived98809 p h)

theorem derived112509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5092) ∨ (¬ p 6008) ∨ (¬ p 3212) :=
  ElevenRUP.step112509 (p 3212) (p 4209) (p 5092) (p 6008) (derived111318 p h) (h 8575)

theorem derived112510 (p : Nat → Prop) (h : Inputs p) :
    (p 6008) ∨ (¬ p 4207) ∨ (p 5092) ∨ (¬ p 3212) :=
  ElevenRUP.step112510 (p 3212) (p 4207) (p 4209) (p 5092) (p 6008) (derived108402 p h) (h 13040)

theorem derived112511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3005) ∨ (¬ p 3136) :=
  ElevenRUP.step112511 (p 3005) (p 3136) (p 3156) (p 4237) (derived84347 p h) (derived100888 p h)

theorem derived112512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3166) ∨ (¬ p 2946) :=
  ElevenRUP.step112512 (p 2946) (p 3156) (p 3166) (p 4237) (h 6810) (derived100888 p h)

theorem derived112513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 4121) ∨ (¬ p 3413) :=
  ElevenRUP.step112513 (p 3156) (p 3413) (p 4121) (p 4237) (h 6795) (derived100888 p h)

theorem derived112514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3189) ∨ (¬ p 2992) :=
  ElevenRUP.step112514 (p 2992) (p 3156) (p 3189) (p 4237) (derived85922 p h) (derived100888 p h)

theorem derived112520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 4009) ∨ (¬ p 5568) ∨ (p 2220) :=
  ElevenRUP.step112520 (p 2220) (p 2954) (p 3156) (p 4009) (p 4237) (p 5568) (derived106494 p h) (derived76622 p h) (derived100888 p h)

theorem derived112522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3146) ∨ (¬ p 4904) ∨ (p 2901) ∨ (¬ p 3256) :=
  ElevenRUP.step112522 (p 2901) (p 3146) (p 3156) (p 3256) (p 4237) (p 4904) (derived78209 p h) (derived100888 p h)

theorem derived112523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2373) ∨ (p 3146) ∨ (¬ p 3256) :=
  ElevenRUP.step112523 (p 2373) (p 3146) (p 3156) (p 3256) (p 4237) (p 4705) (derived106238 p h) (derived78922 p h) (derived100888 p h)

theorem derived112524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2619) ∨ (p 3146) ∨ (¬ p 3256) :=
  ElevenRUP.step112524 (p 2619) (p 3146) (p 3156) (p 3256) (p 4237) (p 4906) (derived105632 p h) (derived84729 p h) (derived100888 p h)

theorem derived112525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3256) ∨ (p 3146) ∨ (p 2284) :=
  ElevenRUP.step112525 (p 2284) (p 3146) (p 3156) (p 3256) (p 4237) (p 4509) (derived105392 p h) (derived84956 p h) (derived100888 p h)

theorem derived112527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2220) ∨ (p 3146) ∨ (¬ p 3256) :=
  ElevenRUP.step112527 (p 2220) (p 2954) (p 3146) (p 3156) (p 3256) (p 4237) (derived106494 p h) (derived92458 p h) (derived100888 p h)

theorem derived112528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3189) ∨ (p 3073) ∨ (¬ p 3256) ∨ (¬ p 2946) :=
  ElevenRUP.step112528 (p 2946) (p 3073) (p 3156) (p 3189) (p 3256) (p 4237) (derived110243 p h) (derived100888 p h)

theorem derived112529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 2619) ∨ (¬ p 4009) ∨ (¬ p 5612) ∨ (p 2284) :=
  ElevenRUP.step112529 (p 2284) (p 2619) (p 3156) (p 4009) (p 4237) (p 5612) (derived111868 p h) (derived100888 p h)

theorem derived112536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3256) ∨ (p 3146) ∨ (¬ p 3988) ∨ (p 2901) :=
  ElevenRUP.step112536 (p 2901) (p 3146) (p 3156) (p 3256) (p 3988) (p 4237) (p 4555) (derived105542 p h) (derived78208 p h) (derived100888 p h)

theorem derived112539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3146) ∨ (¬ p 4119) ∨ (p 2427) ∨ (¬ p 3256) :=
  ElevenRUP.step112539 (p 2427) (p 3146) (p 3156) (p 3256) (p 4119) (p 4237) (p 4705) (derived106238 p h) (derived90898 p h) (derived100888 p h)

theorem derived112548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 3309) ∨ (¬ p 3256) ∨ (p 3146) ∨ (p 3093) ∨ (¬ p 2946) ∨ (p 2177) :=
  ElevenRUP.step112548 (p 2177) (p 2248) (p 2946) (p 3093) (p 3146) (p 3156) (p 3256) (p 3309) (p 4237) (p 4902) (derived105365 p h) (derived105456 p h) (derived75217 p h) (derived100888 p h)

theorem derived112553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (p 2122) ∨ (p 2177) ∨ (p 3146) ∨ (p 2774) ∨ (¬ p 3256) ∨ (¬ p 2253) ∨ (¬ p 2946) :=
  ElevenRUP.step112553 (p 2122) (p 2177) (p 2253) (p 2774) (p 2946) (p 3146) (p 3156) (p 3256) (p 4237) (p 4736) (p 4902) (derived105431 p h) (derived105456 p h) (derived75216 p h) (derived100888 p h)

theorem derived112559 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3146) ∨ (¬ p 3256) :=
  ElevenRUP.step112559 (p 3146) (p 3156) (p 3256) (p 4312) (derived95466 p h) (derived96197 p h)

theorem derived112560 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3166) ∨ (¬ p 2946) ∨ (¬ p 2284) :=
  ElevenRUP.step112560 (p 2284) (p 2946) (p 3156) (p 3166) (p 4312) (derived95465 p h) (derived96197 p h)

theorem derived112563 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3005) ∨ (¬ p 2373) ∨ (¬ p 3136) :=
  ElevenRUP.step112563 (p 2373) (p 3005) (p 3136) (p 3156) (p 4312) (p 4702) (derived106079 p h) (derived84368 p h) (derived96197 p h)

theorem derived112564 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2619) ∨ (p 3189) ∨ (¬ p 2992) ∨ (¬ p 5053) :=
  ElevenRUP.step112564 (p 2619) (p 2992) (p 3156) (p 3189) (p 4312) (p 5053) (derived85947 p h) (derived96197 p h)

theorem derived112565 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3189) ∨ (¬ p 2373) ∨ (¬ p 2992) :=
  ElevenRUP.step112565 (p 2373) (p 2992) (p 3156) (p 3189) (p 4312) (p 4702) (derived106079 p h) (derived85949 p h) (derived96197 p h)

theorem derived112571 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3166) ∨ (¬ p 2166) ∨ (¬ p 2946) :=
  ElevenRUP.step112571 (p 2166) (p 2946) (p 3156) (p 3166) (p 4312) (p 4960) (derived106209 p h) (derived95771 p h) (derived96197 p h)

theorem derived112572 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3005) ∨ (¬ p 2166) ∨ (¬ p 3136) :=
  ElevenRUP.step112572 (p 2166) (p 3005) (p 3136) (p 3156) (p 4312) (p 4960) (derived106209 p h) (derived97652 p h) (derived96197 p h)

theorem derived112573 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3166) ∨ (p 3146) ∨ (¬ p 2946) ∨ (p 2992) :=
  ElevenRUP.step112573 (p 2946) (p 2992) (p 3146) (p 3156) (p 3166) (p 4312) (derived99842 p h) (derived96197 p h)

theorem derived112574 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3005) ∨ (p 2098) ∨ (¬ p 2860) ∨ (¬ p 2132) :=
  ElevenRUP.step112574 (p 2098) (p 2132) (p 2860) (p 3005) (p 3156) (p 4312) (derived110573 p h) (derived96197 p h)

theorem derived112575 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 2264) ∨ (¬ p 2619) ∨ (p 2870) ∨ (p 2911) :=
  ElevenRUP.step112575 (p 2264) (p 2619) (p 2870) (p 2911) (p 3156) (p 4312) (derived112210 p h) (derived96197 p h)

theorem derived112584 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3005) ∨ (¬ p 5568) ∨ (p 2946) ∨ (¬ p 3136) ∨ (¬ p 4236) :=
  ElevenRUP.step112584 (p 2946) (p 3005) (p 3136) (p 3156) (p 4236) (p 4312) (p 5568) (derived101737 p h) (derived96197 p h)

theorem derived112585 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 3146) ∨ (p 3005) ∨ (¬ p 3136) ∨ (¬ p 4236) ∨ (p 2946) :=
  ElevenRUP.step112585 (p 2946) (p 3005) (p 3136) (p 3146) (p 3156) (p 4236) (p 4312) (derived101739 p h) (derived96197 p h)

theorem derived112588 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (¬ p 3979) ∨ (¬ p 5568) ∨ (¬ p 3325) ∨ (¬ p 3323) ∨ (¬ p 4196) :=
  ElevenRUP.step112588 (p 3156) (p 3323) (p 3325) (p 3979) (p 4196) (p 4312) (p 4624) (p 5568) (derived105408 p h) (derived49819 p h) (derived96197 p h)

theorem derived112593 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2352) ∨ (p 2459) ∨ (p 2598) ∨ (p 3422) ∨ (¬ p 3256) ∨ (¬ p 2220) ∨ (¬ p 2139) :=
  ElevenRUP.step112593 (p 2139) (p 2220) (p 2352) (p 2459) (p 2598) (p 3156) (p 3256) (p 3422) (p 4312) (p 4503) (derived106530 p h) (derived75288 p h) (derived96197 p h)

theorem derived112597 (p : Nat → Prop) (h : Inputs p) :
    (p 3156) ∨ (p 2459) ∨ (¬ p 3256) ∨ (¬ p 3905) ∨ (¬ p 3422) ∨ (¬ p 2220) ∨ (p 3641) ∨ (p 2573) ∨ (¬ p 2139) :=
  ElevenRUP.step112597 (p 2139) (p 2220) (p 2459) (p 2573) (p 3156) (p 3256) (p 3422) (p 3641) (p 3905) (p 4312) (derived107647 p h) (derived96197 p h)

theorem derived112607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2284) ∨ (p 2860) :=
  ElevenRUP.step112607 (p 2284) (p 2860) (p 3136) (p 5051) (derived83242 p h) (derived96314 p h)

theorem derived112608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3105) ∨ (¬ p 3115) :=
  ElevenRUP.step112608 (p 3105) (p 3115) (p 3136) (p 5051) (derived84554 p h) (derived96314 p h)

theorem derived112609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2619) ∨ (¬ p 3156) :=
  ElevenRUP.step112609 (p 2619) (p 3136) (p 3156) (p 5051) (derived84772 p h) (derived96314 p h)

theorem derived112610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2901) ∨ (p 2870) :=
  ElevenRUP.step112610 (p 2870) (p 2901) (p 3136) (p 5051) (h 26296) (derived96314 p h)

theorem derived112613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3695) ∨ (¬ p 4241) :=
  ElevenRUP.step112613 (p 3136) (p 3695) (p 4241) (p 5051) (h 22484) (derived96314 p h)

theorem derived112614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 4282) ∨ (¬ p 4243) :=
  ElevenRUP.step112614 (p 3136) (p 4243) (p 4282) (p 5051) (h 16823) (derived96314 p h)

theorem derived112615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2839) ∨ (p 2946) ∨ (p 2737) :=
  ElevenRUP.step112615 (p 2737) (p 2839) (p 2946) (p 3136) (p 5051) (derived83738 p h) (derived96314 p h)

theorem derived112618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2132) ∨ (¬ p 2284) ∨ (p 2696) ∨ (¬ p 2737) :=
  ElevenRUP.step112618 (p 2132) (p 2284) (p 2696) (p 2737) (p 3136) (p 5051) (derived82582 p h) (derived96314 p h)

theorem derived112619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2132) ∨ (p 2992) ∨ (p 2696) :=
  ElevenRUP.step112619 (p 2132) (p 2696) (p 2745) (p 2992) (p 3136) (p 5051) (derived105523 p h) (derived82919 p h) (derived96314 p h)

theorem derived112622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 2619) ∨ (p 2098) ∨ (¬ p 2132) ∨ (¬ p 2166) :=
  ElevenRUP.step112622 (p 2098) (p 2132) (p 2166) (p 2619) (p 3136) (p 5051) (derived110297 p h) (derived96314 p h)

theorem derived112623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 4700) ∨ (¬ p 2839) ∨ (p 2737) ∨ (p 2685) ∨ (¬ p 4650) :=
  ElevenRUP.step112623 (p 2685) (p 2737) (p 2839) (p 3136) (p 4650) (p 4700) (p 5051) (derived83064 p h) (derived96314 p h)

theorem derived112629 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 2132) ∨ (p 2797) ∨ (¬ p 4700) ∨ (p 2696) ∨ (¬ p 4972) :=
  ElevenRUP.step112629 (p 2132) (p 2696) (p 2797) (p 3136) (p 4700) (p 4972) (p 5051) (derived91252 p h) (derived96314 p h)

theorem derived112632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (p 3125) ∨ (¬ p 3564) ∨ (¬ p 2284) ∨ (p 3105) ∨ (p 2352) :=
  ElevenRUP.step112632 (p 2284) (p 2352) (p 3105) (p 3125) (p 3136) (p 3564) (p 5051) (derived112442 p h) (derived96314 p h)

theorem derived112640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3516) ∨ (¬ p 2761) ∨ (p 2619) ∨ (¬ p 2685) ∨ (¬ p 5568) ∨ (¬ p 4066) ∨ (p 2946) ∨ (¬ p 5123) :=
  ElevenRUP.step112640 (p 2619) (p 2685) (p 2761) (p 2946) (p 3136) (p 3516) (p 4066) (p 5051) (p 5123) (p 5568) (derived76627 p h) (derived96314 p h)

theorem derived112647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3979) ∨ (¬ p 2470) ∨ (p 3146) ∨ (p 2619) ∨ (¬ p 2630) ∨ (p 2946) ∨ (¬ p 2656) ∨ (¬ p 4157) :=
  ElevenRUP.step112647 (p 2470) (p 2619) (p 2630) (p 2656) (p 2946) (p 3136) (p 3146) (p 3979) (p 4157) (p 5051) (p 5122) (derived105483 p h) (derived84835 p h) (derived96314 p h)

theorem derived112653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3136) ∨ (¬ p 3564) ∨ (¬ p 3461) ∨ (p 2946) ∨ (p 2870) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 4236) ∨ (¬ p 3519) ∨ (¬ p 5660) :=
  ElevenRUP.step112653 (p 2573) (p 2870) (p 2946) (p 3136) (p 3366) (p 3461) (p 3519) (p 3564) (p 4236) (p 4376) (p 4831) (p 5051) (p 5660) (derived106320 p h) (derived105445 p h) (derived86805 p h) (derived96314 p h)

theorem derived112655 (p : Nat → Prop) (h : Inputs p) :
    (p 3527) ∨ (¬ p 2341) ∨ (¬ p 3543) :=
  ElevenRUP.step112655 (p 2341) (p 3527) (p 3542) (p 3543) (derived112233 p h) (derived93328 p h)

theorem derived112657 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2417) ∨ (p 2911) :=
  ElevenRUP.step112657 (p 2417) (p 2459) (p 2911) (p 3657) (derived75803 p h) (derived96417 p h)

theorem derived112658 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2396) ∨ (p 2177) :=
  ElevenRUP.step112658 (p 2177) (p 2396) (p 2459) (p 3657) (derived75887 p h) (derived96417 p h)

theorem derived112659 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3246) ∨ (p 2881) :=
  ElevenRUP.step112659 (p 2459) (p 2881) (p 3246) (p 3657) (derived78055 p h) (derived96417 p h)

theorem derived112660 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2449) ∨ (p 2264) :=
  ElevenRUP.step112660 (p 2264) (p 2449) (p 2459) (p 3657) (derived82160 p h) (derived96417 p h)

theorem derived112661 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3516) ∨ (p 2341) :=
  ElevenRUP.step112661 (p 2341) (p 2459) (p 3516) (p 3657) (derived86823 p h) (derived96417 p h)

theorem derived112662 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3631) ∨ (p 3527) :=
  ElevenRUP.step112662 (p 2459) (p 3527) (p 3631) (p 3657) (derived89299 p h) (derived96417 p h)

theorem derived112663 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3434) ∨ (p 2717) :=
  ElevenRUP.step112663 (p 2459) (p 2717) (p 3434) (p 3657) (derived89590 p h) (derived96417 p h)

theorem derived112664 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2417) ∨ (¬ p 3658) ∨ (p 2717) :=
  ElevenRUP.step112664 (p 2417) (p 2459) (p 2717) (p 3657) (p 3658) (derived76140 p h) (derived96417 p h)

theorem derived112665 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 4445) ∨ (¬ p 4132) ∨ (¬ p 3146) :=
  ElevenRUP.step112665 (p 2459) (p 3146) (p 3657) (p 4132) (p 4445) (h 6906) (derived96417 p h)

theorem derived112666 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2761) ∨ (¬ p 2528) ∨ (¬ p 3266) :=
  ElevenRUP.step112666 (p 2459) (p 2528) (p 2761) (p 3266) (p 3657) (derived107130 p h) (derived96417 p h)

theorem derived112668 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2417) ∨ (p 2881) ∨ (¬ p 4001) :=
  ElevenRUP.step112668 (p 2417) (p 2459) (p 2881) (p 3657) (p 4001) (derived84962 p h) (derived96417 p h)

theorem derived112671 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2396) ∨ (p 2911) ∨ (¬ p 4710) :=
  ElevenRUP.step112671 (p 2396) (p 2459) (p 2911) (p 3657) (p 4710) (derived93579 p h) (derived96417 p h)

theorem derived112673 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 3527) ∨ (¬ p 3037) ∨ (¬ p 2449) :=
  ElevenRUP.step112673 (p 2449) (p 2459) (p 3037) (p 3527) (p 3657) (derived95856 p h) (derived96417 p h)

theorem derived112676 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3256) ∨ (p 2761) ∨ (¬ p 4041) ∨ (¬ p 3266) :=
  ElevenRUP.step112676 (p 2459) (p 2761) (p 3256) (p 3266) (p 3657) (p 4041) (derived75260 p h) (derived96417 p h)

theorem derived112677 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2241) ∨ (¬ p 2922) ∨ (¬ p 2417) ∨ (¬ p 3379) :=
  ElevenRUP.step112677 (p 2241) (p 2417) (p 2459) (p 2922) (p 3379) (p 3657) (derived80837 p h) (derived96417 p h)

theorem derived112678 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3266) ∨ (p 3201) ∨ (p 2761) ∨ (p 2911) :=
  ElevenRUP.step112678 (p 2459) (p 2761) (p 2911) (p 3201) (p 3266) (p 3657) (derived81898 p h) (derived96417 p h)

theorem derived112679 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2761) ∨ (¬ p 2363) ∨ (¬ p 3266) :=
  ElevenRUP.step112679 (p 2363) (p 2459) (p 2761) (p 3266) (p 3657) (p 4503) (derived106530 p h) (derived81925 p h) (derived96417 p h)

theorem derived112680 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2088) ∨ (p 2761) ∨ (¬ p 3266) ∨ (¬ p 4592) :=
  ElevenRUP.step112680 (p 2088) (p 2459) (p 2761) (p 3266) (p 3657) (p 4592) (derived81926 p h) (derived96417 p h)

theorem derived112681 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2685) ∨ (¬ p 2449) ∨ (p 2630) ∨ (¬ p 2651) :=
  ElevenRUP.step112681 (p 2449) (p 2459) (p 2630) (p 2651) (p 2685) (p 3657) (derived89073 p h) (derived96417 p h)

theorem derived112684 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2088) ∨ (p 2761) ∨ (¬ p 3767) ∨ (¬ p 3146) :=
  ElevenRUP.step112684 (p 2088) (p 2459) (p 2761) (p 3146) (p 3657) (p 3767) (derived109741 p h) (derived96417 p h)

theorem derived112686 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2264) ∨ (¬ p 3246) ∨ (p 3005) ∨ (¬ p 2685) :=
  ElevenRUP.step112686 (p 2264) (p 2459) (p 2685) (p 3005) (p 3246) (p 3657) (derived112120 p h) (derived96417 p h)

theorem derived112688 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3256) ∨ (p 3461) ∨ (¬ p 4041) ∨ (¬ p 3266) ∨ (¬ p 4623) :=
  ElevenRUP.step112688 (p 2459) (p 3256) (p 3266) (p 3461) (p 3657) (p 4041) (p 4623) (derived75261 p h) (derived96417 p h)

theorem derived112689 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 4623) ∨ (¬ p 3266) ∨ (p 3461) ∨ (¬ p 3146) :=
  ElevenRUP.step112689 (p 2459) (p 3146) (p 3266) (p 3461) (p 3657) (p 4623) (p 4905) (derived105995 p h) (derived78791 p h) (derived96417 p h)

theorem derived112692 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2341) ∨ (¬ p 4984) ∨ (p 2761) ∨ (¬ p 3266) ∨ (¬ p 2957) ∨ (p 2992) :=
  ElevenRUP.step112692 (p 2341) (p 2459) (p 2761) (p 2957) (p 2992) (p 3266) (p 3657) (p 4984) (derived95680 p h) (derived96417 p h)

theorem derived112697 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2417) ∨ (p 3005) ∨ (p 3256) ∨ (¬ p 2437) ∨ (¬ p 3146) ∨ (¬ p 2651) :=
  ElevenRUP.step112697 (p 2417) (p 2437) (p 2459) (p 2651) (p 3005) (p 3146) (p 3256) (p 3657) (p 4790) (p 4905) (derived106424 p h) (derived105995 p h) (derived98066 p h) (derived96417 p h)

theorem derived112698 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 3434) ∨ (¬ p 3941) ∨ (p 3425) ∨ (p 3073) ∨ (¬ p 3379) ∨ (¬ p 2753) ∨ (p 3449) :=
  ElevenRUP.step112698 (p 2459) (p 2753) (p 3073) (p 3379) (p 3425) (p 3434) (p 3449) (p 3657) (p 3941) (p 5122) (derived105483 p h) (derived99065 p h) (derived96417 p h)

theorem derived112699 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 2417) ∨ (p 3193) ∨ (p 3609) ∨ (p 2922) ∨ (¬ p 3389) ∨ (¬ p 2363) ∨ (p 2098) ∨ (¬ p 4079) :=
  ElevenRUP.step112699 (p 2098) (p 2363) (p 2417) (p 2459) (p 2922) (p 3193) (p 3389) (p 3609) (p 3657) (p 4079) (derived111726 p h) (derived96417 p h)

theorem derived112705 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 3146) ∨ (¬ p 2246) ∨ (¬ p 3988) ∨ (¬ p 2363) ∨ (¬ p 2437) ∨ (¬ p 2417) ∨ (¬ p 3366) ∨ (¬ p 2651) ∨ (p 2156) ∨ (¬ p 2136) :=
  ElevenRUP.step112705 (p 2136) (p 2156) (p 2246) (p 2363) (p 2417) (p 2437) (p 2459) (p 2651) (p 2744) (p 3146) (p 3366) (p 3657) (p 3988) (p 4503) (derived106503 p h) (derived106530 p h) (derived85543 p h) (derived96417 p h)

theorem derived112711 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2363) ∨ (¬ p 3322) ∨ (¬ p 2088) :=
  ElevenRUP.step112711 (p 2088) (p 2363) (p 2383) (p 3322) (p 4170) (derived111657 p h) (derived93717 p h)

theorem derived112713 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2528) ∨ (¬ p 3573) ∨ (¬ p 2088) ∨ (¬ p 2553) :=
  ElevenRUP.step112713 (p 2088) (p 2383) (p 2528) (p 2553) (p 3573) (p 4170) (derived78431 p h) (derived93717 p h)

theorem derived112714 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 3256) ∨ (¬ p 2295) ∨ (¬ p 2088) ∨ (¬ p 4196) :=
  ElevenRUP.step112714 (p 2088) (p 2295) (p 2383) (p 3256) (p 4170) (p 4196) (derived79331 p h) (derived93717 p h)

theorem derived112721 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2819) ∨ (p 3609) ∨ (¬ p 2122) ∨ (¬ p 2088) :=
  ElevenRUP.step112721 (p 2088) (p 2122) (p 2383) (p 2819) (p 3609) (p 4170) (derived111544 p h) (derived93717 p h)

theorem derived112723 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2819) ∨ (p 3083) ∨ (¬ p 3016) ∨ (¬ p 2481) :=
  ElevenRUP.step112723 (p 2383) (p 2481) (p 2819) (p 3016) (p 3083) (p 4170) (p 5225) (derived105495 p h) (derived76927 p h) (derived93717 p h)

theorem derived112731 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2619) ∨ (¬ p 4115) ∨ (¬ p 2352) ∨ (¬ p 2860) :=
  ElevenRUP.step112731 (p 2352) (p 2383) (p 2619) (p 2860) (p 4115) (p 4170) (p 4718) (derived105425 p h) (derived84821 p h) (derived93717 p h)

theorem derived112732 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 2819) ∨ (p 2122) ∨ (¬ p 4403) ∨ (p 2911) :=
  ElevenRUP.step112732 (p 2122) (p 2383) (p 2819) (p 2911) (p 4170) (p 4276) (p 4403) (derived105516 p h) (derived86177 p h) (derived93717 p h)

theorem derived112735 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (¬ p 3998) ∨ (¬ p 2187) ∨ (¬ p 2553) ∨ (p 4149) ∨ (¬ p 3573) :=
  ElevenRUP.step112735 (p 2187) (p 2383) (p 2553) (p 3573) (p 3998) (p 4149) (p 4170) (derived89957 p h) (derived93717 p h)

theorem derived112740 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 3189) ∨ (¬ p 2641) ∨ (¬ p 3177) ∨ (¬ p 2352) :=
  ElevenRUP.step112740 (p 2352) (p 2383) (p 2641) (p 3177) (p 3189) (p 4170) (p 4973) (derived105835 p h) (derived100538 p h) (derived93717 p h)

theorem derived112745 (p : Nat → Prop) (h : Inputs p) :
    (p 2383) ∨ (p 2819) ∨ (¬ p 2187) ∨ (¬ p 2088) ∨ (p 3609) ∨ (¬ p 4889) :=
  ElevenRUP.step112745 (p 2088) (p 2187) (p 2383) (p 2819) (p 3609) (p 4170) (p 4889) (derived111552 p h) (derived93717 p h)

theorem derived112757 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2761) ∨ (p 3680) :=
  ElevenRUP.step112757 (p 2761) (p 3246) (p 3680) (p 4135) (h 35461) (derived96169 p h)

theorem derived112760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2427) ∨ (p 3631) ∨ (¬ p 2982) :=
  ElevenRUP.step112760 (p 2427) (p 2982) (p 3246) (p 3631) (p 4135) (derived107224 p h) (derived96169 p h)

theorem derived112763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (p 2870) ∨ (¬ p 3105) :=
  ElevenRUP.step112763 (p 2870) (p 2881) (p 3105) (p 3246) (p 4135) (p 4668) (derived105414 p h) (derived86692 p h) (derived96169 p h)

theorem derived112764 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2891) ∨ (p 2881) ∨ (¬ p 2972) :=
  ElevenRUP.step112764 (p 2881) (p 2891) (p 2972) (p 3246) (p 4135) (p 4668) (derived105414 p h) (derived92690 p h) (derived96169 p h)

theorem derived112765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3212) ∨ (p 3051) ∨ (p 2881) :=
  ElevenRUP.step112765 (p 2881) (p 3051) (p 3212) (p 3246) (p 4135) (p 4668) (derived105414 p h) (derived92814 p h) (derived96169 p h)

theorem derived112766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3212) ∨ (¬ p 2761) ∨ (p 3051) ∨ (¬ p 2870) :=
  ElevenRUP.step112766 (p 2761) (p 2870) (p 3051) (p 3212) (p 3246) (p 4135) (derived92854 p h) (derived96169 p h)

theorem derived112770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2891) ∨ (p 2417) ∨ (¬ p 2972) :=
  ElevenRUP.step112770 (p 2417) (p 2891) (p 2972) (p 3246) (p 4135) (p 4277) (derived105380 p h) (derived97716 p h) (derived96169 p h)

theorem derived112771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2881) ∨ (¬ p 2982) ∨ (p 2427) :=
  ElevenRUP.step112771 (p 2427) (p 2881) (p 2982) (p 3246) (p 4135) (p 4668) (derived105414 p h) (derived99288 p h) (derived96169 p h)

theorem derived112772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3212) ∨ (¬ p 2761) ∨ (p 3051) ∨ (¬ p 2901) :=
  ElevenRUP.step112772 (p 2761) (p 2901) (p 3051) (p 3212) (p 3246) (p 4135) (derived99858 p h) (derived96169 p h)

theorem derived112773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2417) ∨ (¬ p 3212) ∨ (p 3051) :=
  ElevenRUP.step112773 (p 2417) (p 3051) (p 3212) (p 3246) (p 4135) (p 4277) (derived105380 p h) (derived100099 p h) (derived96169 p h)

theorem derived112774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2901) ∨ (p 2417) ∨ (¬ p 3115) :=
  ElevenRUP.step112774 (p 2417) (p 2901) (p 3115) (p 3246) (p 4135) (p 4277) (derived105380 p h) (derived100100 p h) (derived96169 p h)

theorem derived112775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2427) ∨ (p 2449) ∨ (¬ p 2982) :=
  ElevenRUP.step112775 (p 2427) (p 2449) (p 2982) (p 3246) (p 4135) (p 4280) (derived105599 p h) (derived100143 p h) (derived96169 p h)

theorem derived112776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2870) ∨ (p 2449) ∨ (¬ p 3105) :=
  ElevenRUP.step112776 (p 2449) (p 2870) (p 3105) (p 3246) (p 4135) (p 4280) (derived105599 p h) (derived100177 p h) (derived96169 p h)

theorem derived112778 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2396) ∨ (¬ p 3212) ∨ (p 3051) :=
  ElevenRUP.step112778 (p 2396) (p 3051) (p 3212) (p 3246) (p 4135) (p 4559) (derived105701 p h) (derived100933 p h) (derived96169 p h)

theorem derived112785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 3051) ∨ (¬ p 2427) ∨ (¬ p 2761) ∨ (¬ p 2972) ∨ (¬ p 3645) :=
  ElevenRUP.step112785 (p 2427) (p 2761) (p 2972) (p 3051) (p 3246) (p 3645) (p 4135) (derived92783 p h) (derived96169 p h)

theorem derived112788 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (p 2891) ∨ (p 3516) ∨ (¬ p 2972) ∨ (¬ p 4155) :=
  ElevenRUP.step112788 (p 2891) (p 2972) (p 3246) (p 3516) (p 4135) (p 4155) (p 4280) (derived105599 p h) (derived97714 p h) (derived96169 p h)

theorem derived112791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 2761) ∨ (p 2427) ∨ (¬ p 3051) ∨ (¬ p 4399) ∨ (¬ p 2982) :=
  ElevenRUP.step112791 (p 2427) (p 2761) (p 2982) (p 3051) (p 3246) (p 4135) (p 4399) (derived99907 p h) (derived96169 p h)

theorem derived112792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3576) ∨ (p 2901) ∨ (¬ p 4895) ∨ (p 3631) ∨ (¬ p 3115) :=
  ElevenRUP.step112792 (p 2901) (p 3115) (p 3246) (p 3576) (p 3631) (p 4135) (p 4895) (derived101826 p h) (derived96169 p h)

theorem derived112804 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3246) ∨ (¬ p 3051) ∨ (¬ p 3950) ∨ (p 2901) ∨ (p 2528) ∨ (¬ p 2958) ∨ (p 3379) ∨ (¬ p 2509) ∨ (¬ p 3115) :=
  ElevenRUP.step112804 (p 2248) (p 2509) (p 2528) (p 2901) (p 2958) (p 3051) (p 3115) (p 3246) (p 3379) (p 3950) (p 4135) (derived105365 p h) (derived78187 p h) (derived96169 p h)

theorem derived112809 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3166) ∨ (¬ p 2331) :=
  ElevenRUP.step112809 (p 2331) (p 2668) (p 3166) (p 4341) (h 17797) (derived96399 p h)

theorem derived112810 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3189) ∨ (¬ p 2641) :=
  ElevenRUP.step112810 (p 2641) (p 2668) (p 3189) (p 4341) (derived86094 p h) (derived96399 p h)

theorem derived112811 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2797) ∨ (p 3005) :=
  ElevenRUP.step112811 (p 2668) (p 2797) (p 3005) (p 4341) (derived87123 p h) (derived96399 p h)

theorem derived112812 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2363) ∨ (p 2187) ∨ (¬ p 3256) :=
  ElevenRUP.step112812 (p 2187) (p 2363) (p 2668) (p 3256) (p 4341) (derived75258 p h) (derived96399 p h)

theorem derived112814 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3189) ∨ (¬ p 2246) ∨ (¬ p 2331) :=
  ElevenRUP.step112814 (p 2246) (p 2331) (p 2668) (p 3189) (p 4341) (h 36789) (derived96399 p h)

theorem derived112822 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2363) ∨ (¬ p 3256) ∨ (p 2352) :=
  ElevenRUP.step112822 (p 2352) (p 2363) (p 2668) (p 3256) (p 4341) (p 4976) (derived105465 p h) (derived79154 p h) (derived96399 p h)

theorem derived112824 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3256) ∨ (p 2363) ∨ (¬ p 2797) ∨ (¬ p 2737) :=
  ElevenRUP.step112824 (p 2363) (p 2668) (p 2737) (p 2797) (p 3256) (p 4341) (derived92238 p h) (derived96399 p h)

theorem derived112826 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2363) ∨ (p 2819) ∨ (¬ p 3256) :=
  ElevenRUP.step112826 (p 2363) (p 2668) (p 2819) (p 3256) (p 4341) (p 4843) (derived105449 p h) (derived93110 p h) (derived96399 p h)

theorem derived112827 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2641) ∨ (¬ p 3170) ∨ (¬ p 3256) ∨ (p 2088) :=
  ElevenRUP.step112827 (p 2088) (p 2249) (p 2641) (p 2668) (p 3170) (p 3256) (p 4341) (derived106513 p h) (derived75277 p h) (derived96399 p h)

theorem derived112829 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2553) ∨ (p 2363) ∨ (¬ p 3955) ∨ (¬ p 3256) :=
  ElevenRUP.step112829 (p 2363) (p 2553) (p 2668) (p 3256) (p 3955) (p 4341) (p 4976) (derived105465 p h) (derived75295 p h) (derived96399 p h)

theorem derived112841 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 3527) ∨ (p 3073) ∨ (¬ p 3256) ∨ (¬ p 2440) ∨ (¬ p 3019) ∨ (¬ p 2933) :=
  ElevenRUP.step112841 (p 2440) (p 2668) (p 2933) (p 3019) (p 3073) (p 3256) (p 3527) (p 4341) (derived112263 p h) (derived96399 p h)

theorem derived112844 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2331) ∨ (p 2210) ∨ (p 2363) ∨ (p 2881) ∨ (¬ p 3256) ∨ (p 2891) :=
  ElevenRUP.step112844 (p 2210) (p 2248) (p 2331) (p 2363) (p 2668) (p 2881) (p 2891) (p 3256) (p 4133) (p 4341) (derived105365 p h) (derived105712 p h) (derived75524 p h) (derived96399 p h)

theorem derived112845 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3256) ∨ (p 2406) ∨ (p 3379) ∨ (p 2363) ∨ (¬ p 2331) ∨ (p 2373) :=
  ElevenRUP.step112845 (p 2248) (p 2331) (p 2363) (p 2373) (p 2406) (p 2668) (p 3256) (p 3379) (p 4134) (p 4341) (derived105365 p h) (derived105379 p h) (derived79823 p h) (derived96399 p h)

theorem derived112847 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2717) ∨ (p 2608) ∨ (p 2363) ∨ (¬ p 3256) ∨ (p 2707) ∨ (¬ p 2331) :=
  ElevenRUP.step112847 (p 2248) (p 2331) (p 2363) (p 2608) (p 2668) (p 2707) (p 2717) (p 3256) (p 4133) (p 4341) (derived105365 p h) (derived105712 p h) (derived88260 p h) (derived96399 p h)

theorem derived112848 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (p 2363) ∨ (p 2210) ∨ (¬ p 2331) ∨ (¬ p 3379) ∨ (¬ p 3256) ∨ (p 2166) ∨ (¬ p 2246) ∨ (¬ p 2749) :=
  ElevenRUP.step112848 (p 2166) (p 2210) (p 2246) (p 2331) (p 2363) (p 2668) (p 2749) (p 3256) (p 3379) (p 4134) (p 4341) (derived105379 p h) (derived76066 p h) (derived96399 p h)

theorem derived112850 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (p 3527) ∨ (p 2363) ∨ (p 3399) ∨ (¬ p 2608) ∨ (¬ p 3256) :=
  ElevenRUP.step112850 (p 2246) (p 2331) (p 2363) (p 2608) (p 2668) (p 2744) (p 3256) (p 3399) (p 3527) (p 4133) (p 4341) (derived106503 p h) (derived105712 p h) (derived82385 p h) (derived96399 p h)

theorem derived112857 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3358) ∨ (p 3389) ∨ (¬ p 3256) ∨ (¬ p 3201) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 3905) ∨ (¬ p 5160) ∨ (p 2363) ∨ (¬ p 2331) :=
  ElevenRUP.step112857 (p 2246) (p 2331) (p 2363) (p 2668) (p 2744) (p 3201) (p 3256) (p 3358) (p 3366) (p 3389) (p 3905) (p 4341) (p 4384) (p 5160) (derived106503 p h) (derived106167 p h) (derived77203 p h) (derived96399 p h)

theorem derived112860 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (p 2470) ∨ (p 2630) :=
  ElevenRUP.step112860 (p 2470) (p 2630) (p 3005) (p 3083) (p 4346) (derived107192 p h) (derived91251 p h)

theorem derived112864 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3189) ∨ (¬ p 2528) ∨ (p 2727) ∨ (¬ p 2651) :=
  ElevenRUP.step112864 (p 2528) (p 2651) (p 2727) (p 3083) (p 3189) (p 4346) (derived91892 p h) (derived91251 p h)

theorem derived112865 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 3016) ∨ (¬ p 3189) ∨ (¬ p 4598) ∨ (p 2727) :=
  ElevenRUP.step112865 (p 2727) (p 3016) (p 3083) (p 3189) (p 4346) (p 4598) (derived91954 p h) (derived91251 p h)

theorem derived112866 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3189) ∨ (p 3641) ∨ (p 2727) :=
  ElevenRUP.step112866 (p 2727) (p 3083) (p 3189) (p 3641) (p 4346) (p 4750) (derived105433 p h) (derived91957 p h) (derived91251 p h)

theorem derived112867 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3189) ∨ (p 2470) ∨ (¬ p 2230) ∨ (p 2727) :=
  ElevenRUP.step112867 (p 2230) (p 2470) (p 2727) (p 3083) (p 3189) (p 4346) (derived91978 p h) (derived91251 p h)

theorem derived112870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (¬ p 2509) ∨ (p 2630) :=
  ElevenRUP.step112870 (p 2509) (p 2630) (p 3005) (p 3083) (p 4346) (p 4811) (derived105633 p h) (derived93983 p h) (derived91251 p h)

theorem derived112871 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 2630) ∨ (p 2651) ∨ (¬ p 3166) :=
  ElevenRUP.step112871 (p 2528) (p 2630) (p 2651) (p 3083) (p 3166) (p 4346) (derived98092 p h) (derived91251 p h)

theorem derived112872 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3166) ∨ (¬ p 2509) ∨ (p 2651) :=
  ElevenRUP.step112872 (p 2509) (p 2651) (p 3083) (p 3166) (p 4346) (p 4811) (derived105633 p h) (derived98161 p h) (derived91251 p h)

theorem derived112874 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (¬ p 2528) ∨ (p 3146) ∨ (p 2630) :=
  ElevenRUP.step112874 (p 2528) (p 2630) (p 3005) (p 3083) (p 3146) (p 4346) (derived100600 p h) (derived91251 p h)

theorem derived112877 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (¬ p 4607) ∨ (p 2630) ∨ (p 2406) :=
  ElevenRUP.step112877 (p 2406) (p 2630) (p 3005) (p 3083) (p 4346) (p 4607) (p 4811) (derived105633 p h) (derived93962 p h) (derived91251 p h)

theorem derived112881 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 3189) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 2630) :=
  ElevenRUP.step112881 (p 2252) (p 2528) (p 2630) (p 2651) (p 3083) (p 3189) (p 4346) (derived98093 p h) (derived91251 p h)

theorem derived112884 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (¬ p 2440) ∨ (p 2727) ∨ (¬ p 4610) ∨ (¬ p 2246) ∨ (¬ p 3361) :=
  ElevenRUP.step112884 (p 2246) (p 2440) (p 2727) (p 3005) (p 3083) (p 3361) (p 4346) (p 4610) (derived88528 p h) (derived91251 p h)

theorem derived112886 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2901) ∨ (¬ p 3988) ∨ (p 2992) ∨ (¬ p 3189) ∨ (¬ p 2531) :=
  ElevenRUP.step112886 (p 2531) (p 2901) (p 2992) (p 3083) (p 3189) (p 3988) (p 4346) (p 4555) (derived105542 p h) (derived91942 p h) (derived91251 p h)

theorem derived112890 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3005) ∨ (¬ p 3573) ∨ (p 2651) ∨ (¬ p 2553) ∨ (¬ p 2727) ∨ (¬ p 3361) :=
  ElevenRUP.step112890 (p 2553) (p 2651) (p 2727) (p 3005) (p 3083) (p 3361) (p 3573) (p 4346) (derived94672 p h) (derived91251 p h)

theorem derived112902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 2331) ∨ (¬ p 4607) ∨ (¬ p 2819) ∨ (¬ p 2307) ∨ (¬ p 3146) ∨ (p 3256) ∨ (p 2122) ∨ (¬ p 2655) ∨ (p 2230) :=
  ElevenRUP.step112902 (p 2122) (p 2230) (p 2307) (p 2331) (p 2655) (p 2819) (p 3083) (p 3146) (p 3256) (p 4346) (p 4607) (derived107805 p h) (derived91251 p h)

theorem derived112909 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (p 3256) ∨ (¬ p 2252) ∨ (¬ p 3146) ∨ (¬ p 2122) ∨ (¬ p 2829) ∨ (p 2230) ∨ (¬ p 2655) ∨ (¬ p 2177) ∨ (¬ p 4607) :=
  ElevenRUP.step112909 (p 2122) (p 2177) (p 2230) (p 2252) (p 2655) (p 2750) (p 2829) (p 3083) (p 3146) (p 3256) (p 4346) (p 4607) (p 4905) (derived106345 p h) (derived105995 p h) (derived101026 p h) (derived91251 p h)

theorem derived112910 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3848) ∨ (¬ p 3189) ∨ (¬ p 5107) ∨ (¬ p 2459) :=
  ElevenRUP.step112910 (p 2264) (p 2459) (p 3189) (p 3848) (p 4550) (p 5107) (derived53610 p h) (derived102508 p h)

theorem derived112911 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 2396) ∨ (p 3256) ∨ (p 2177) ∨ (¬ p 4443) :=
  ElevenRUP.step112911 (p 2177) (p 2264) (p 2396) (p 3256) (p 4443) (p 4550) (derived94926 p h) (derived102508 p h)

theorem derived112912 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 5107) ∨ (¬ p 3189) ∨ (¬ p 4132) ∨ (¬ p 3146) ∨ (¬ p 3848) :=
  ElevenRUP.step112912 (p 2264) (p 3146) (p 3189) (p 3848) (p 4132) (p 4550) (p 5107) (derived60266 p h) (derived102508 p h)

theorem derived112922 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 2274) ∨ (¬ p 3189) ∨ (p 2177) ∨ (¬ p 2253) ∨ (p 2156) ∨ (¬ p 2651) ∨ (p 2727) :=
  ElevenRUP.step112922 (p 2156) (p 2177) (p 2253) (p 2264) (p 2274) (p 2651) (p 2727) (p 3189) (p 4550) (derived91898 p h) (derived102508 p h)

theorem derived112923 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (p 2553) ∨ (p 2573) ∨ (¬ p 2608) ∨ (¬ p 2737) ∨ (p 2177) :=
  ElevenRUP.step112923 (p 2177) (p 2264) (p 2553) (p 2573) (p 2608) (p 2737) (p 3005) (p 4550) (p 5193) (derived105488 p h) (derived93990 p h) (derived102508 p h)

theorem derived112924 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3309) ∨ (p 2177) ∨ (¬ p 2946) ∨ (p 3093) ∨ (p 3136) ∨ (¬ p 3005) :=
  ElevenRUP.step112924 (p 2177) (p 2248) (p 2264) (p 2946) (p 3005) (p 3093) (p 3136) (p 3309) (p 4550) (derived105365 p h) (derived93995 p h) (derived102508 p h)

theorem derived112925 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (p 2881) ∨ (¬ p 2737) ∨ (p 2427) ∨ (¬ p 2608) ∨ (p 2230) :=
  ElevenRUP.step112925 (p 2230) (p 2264) (p 2427) (p 2608) (p 2737) (p 2881) (p 3005) (p 4550) (p 5193) (derived105488 p h) (derived94020 p h) (derived102508 p h)

theorem derived112930 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 2553) ∨ (¬ p 3073) ∨ (p 2573) ∨ (p 3256) ∨ (¬ p 3449) ∨ (p 2396) ∨ (¬ p 3945) :=
  ElevenRUP.step112930 (p 2264) (p 2396) (p 2553) (p 2573) (p 3073) (p 3256) (p 3449) (p 3945) (p 4550) (p 5193) (derived105488 p h) (derived80164 p h) (derived102508 p h)

theorem derived112933 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3189) ∨ (¬ p 2331) ∨ (p 2641) ∨ (p 2870) ∨ (¬ p 2253) ∨ (p 2132) ∨ (p 2881) :=
  ElevenRUP.step112933 (p 2132) (p 2253) (p 2264) (p 2331) (p 2641) (p 2870) (p 2881) (p 3189) (p 4550) (p 4736) (derived105431 p h) (derived86704 p h) (derived102508 p h)

theorem derived112936 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3189) ∨ (¬ p 2459) ∨ (p 3146) ∨ (p 2220) ∨ (¬ p 2241) ∨ (¬ p 3645) ∨ (p 2608) :=
  ElevenRUP.step112936 (p 2220) (p 2241) (p 2264) (p 2459) (p 2608) (p 3146) (p 3189) (p 3645) (p 4550) (p 4877) (derived105451 p h) (derived91979 p h) (derived102508 p h)

theorem derived112937 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3189) ∨ (p 3146) ∨ (¬ p 2651) ∨ (p 2727) ∨ (¬ p 2459) ∨ (p 3051) ∨ (¬ p 2253) ∨ (¬ p 4119) :=
  ElevenRUP.step112937 (p 2253) (p 2264) (p 2459) (p 2651) (p 2727) (p 3051) (p 3146) (p 3189) (p 4119) (p 4550) (derived91994 p h) (derived102508 p h)

theorem derived112940 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (p 2220) ∨ (¬ p 2459) ∨ (p 3146) ∨ (¬ p 2145) ∨ (¬ p 4117) ∨ (¬ p 2651) ∨ (p 2630) :=
  ElevenRUP.step112940 (p 2145) (p 2220) (p 2264) (p 2459) (p 2630) (p 2651) (p 3005) (p 3146) (p 4117) (p 4550) (derived93968 p h) (derived102508 p h)

theorem derived112941 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (¬ p 2145) ∨ (p 2274) ∨ (p 2156) ∨ (p 2630) ∨ (¬ p 2651) ∨ (p 2177) ∨ (¬ p 4117) :=
  ElevenRUP.step112941 (p 2145) (p 2156) (p 2177) (p 2264) (p 2274) (p 2630) (p 2651) (p 3005) (p 4117) (p 4550) (derived93981 p h) (derived102508 p h)

theorem derived112942 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (¬ p 2459) ∨ (¬ p 2331) ∨ (p 2470) ∨ (p 2528) ∨ (p 2797) ∨ (¬ p 4117) :=
  ElevenRUP.step112942 (p 2264) (p 2331) (p 2459) (p 2470) (p 2528) (p 2797) (p 3005) (p 4117) (p 4550) (p 4729) (derived105429 p h) (derived93988 p h) (derived102508 p h)

theorem derived112943 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (¬ p 2246) ∨ (p 3527) ∨ (¬ p 2749) ∨ (p 3136) ∨ (¬ p 2946) ∨ (¬ p 3379) ∨ (p 3399) :=
  ElevenRUP.step112943 (p 2246) (p 2264) (p 2749) (p 2946) (p 3005) (p 3136) (p 3379) (p 3399) (p 3527) (p 4550) (derived93994 p h) (derived102508 p h)

theorem derived112944 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 3005) ∨ (p 2881) ∨ (p 2427) ∨ (¬ p 2331) ∨ (p 2797) ∨ (¬ p 4117) ∨ (p 2230) :=
  ElevenRUP.step112944 (p 2230) (p 2264) (p 2331) (p 2427) (p 2797) (p 2881) (p 3005) (p 4117) (p 4550) (p 4729) (derived105429 p h) (derived94003 p h) (derived102508 p h)

theorem derived112946 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 2891) ∨ (p 2881) ∨ (p 2210) ∨ (¬ p 2331) ∨ (p 2797) ∨ (¬ p 3005) ∨ (¬ p 4117) :=
  ElevenRUP.step112946 (p 2210) (p 2264) (p 2331) (p 2797) (p 2881) (p 2891) (p 3005) (p 4117) (p 4550) (p 4733) (derived105430 p h) (derived99273 p h) (derived102508 p h)

theorem derived112955 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 4373) ∨ (p 2427) ∨ (p 2881) ∨ (¬ p 3347) ∨ (p 3256) ∨ (¬ p 2753) ∨ (¬ p 3609) ∨ (¬ p 2696) ∨ (p 2230) :=
  ElevenRUP.step112955 (p 2230) (p 2264) (p 2427) (p 2696) (p 2753) (p 2881) (p 3256) (p 3347) (p 3609) (p 4373) (p 4550) (derived94935 p h) (derived102508 p h)

theorem derived112960 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (p 3246) ∨ (¬ p 3005) ∨ (¬ p 3945) ∨ (¬ p 2331) ∨ (p 2797) ∨ (p 2982) ∨ (p 3051) ∨ (¬ p 4117) ∨ (¬ p 3904) ∨ (¬ p 2427) :=
  ElevenRUP.step112960 (p 2264) (p 2331) (p 2427) (p 2797) (p 2982) (p 3005) (p 3051) (p 3246) (p 3904) (p 3945) (p 4117) (p 4550) (derived112321 p h) (derived102508 p h)

theorem derived112961 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (p 3125) ∨ (¬ p 3743) :=
  ElevenRUP.step112961 (p 3125) (p 3654) (p 3743) (p 4036) (derived110147 p h) (derived96244 p h)

theorem derived112962 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 2578) ∨ (p 3564) :=
  ElevenRUP.step112962 (p 2578) (p 3564) (p 3654) (p 4036) (derived110148 p h) (derived96244 p h)

theorem derived112964 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3654) ∨ (¬ p 4190) ∨ (p 3286) ∨ (¬ p 3987) :=
  ElevenRUP.step112964 (p 3286) (p 3654) (p 3987) (p 4036) (p 4190) (derived110150 p h) (derived96244 p h)

theorem derived112968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 5160) ∨ (¬ p 2396) ∨ (¬ p 2274) ∨ (p 2608) ∨ (p 3367) ∨ (¬ p 4521) ∨ (¬ p 2156) :=
  ElevenRUP.step112968 (p 2156) (p 2274) (p 2396) (p 2417) (p 2608) (p 3367) (p 4521) (p 4641) (p 5160) (derived75763 p h) (derived96427 p h)

theorem derived112974 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2156) ∨ (p 2696) ∨ (¬ p 2396) ∨ (¬ p 2274) ∨ (p 2630) ∨ (¬ p 2139) ∨ (p 3343) :=
  ElevenRUP.step112974 (p 2139) (p 2156) (p 2274) (p 2396) (p 2417) (p 2630) (p 2696) (p 3343) (p 4641) (derived82870 p h) (derived96427 p h)

theorem derived112975 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2396) ∨ (p 2470) ∨ (¬ p 2774) ∨ (¬ p 2122) ∨ (¬ p 3083) ∨ (p 3343) :=
  ElevenRUP.step112975 (p 2122) (p 2396) (p 2417) (p 2470) (p 2774) (p 3083) (p 3343) (p 4641) (p 4729) (derived105429 p h) (derived89503 p h) (derived96427 p h)

theorem derived112976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2470) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3083) ∨ (p 3343) ∨ (¬ p 3246) :=
  ElevenRUP.step112976 (p 2210) (p 2417) (p 2470) (p 2891) (p 3083) (p 3246) (p 3343) (p 4641) (p 5193) (derived105488 p h) (derived89510 p h) (derived96427 p h)

theorem derived112979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 5160) ∨ (¬ p 2274) ∨ (¬ p 2156) ∨ (p 2470) ∨ (¬ p 3641) ∨ (¬ p 3905) ∨ (¬ p 2139) ∨ (¬ p 2396) :=
  ElevenRUP.step112979 (p 2139) (p 2156) (p 2274) (p 2396) (p 2417) (p 2470) (p 3641) (p 3905) (p 4641) (p 5160) (derived77388 p h) (derived96427 p h)

theorem derived112982 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2177) ∨ (p 2696) ∨ (¬ p 2396) ∨ (¬ p 5257) ∨ (p 3136) ∨ (¬ p 2341) ∨ (p 3343) ∨ (¬ p 3413) :=
  ElevenRUP.step112982 (p 2177) (p 2341) (p 2396) (p 2417) (p 2696) (p 3136) (p 3343) (p 3413) (p 4641) (p 5257) (derived82865 p h) (derived96427 p h)

theorem derived112987 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2449) ∨ (p 3670) ∨ (p 3367) ∨ (¬ p 2696) ∨ (¬ p 3276) ∨ (p 2996) ∨ (¬ p 2742) ∨ (¬ p 5158) :=
  ElevenRUP.step112987 (p 2417) (p 2449) (p 2696) (p 2742) (p 2996) (p 3276) (p 3367) (p 3670) (p 4641) (p 5158) (derived94248 p h) (derived96427 p h)

theorem derived112988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 5160) ∨ (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3654) ∨ (¬ p 2696) ∨ (p 2598) ∨ (¬ p 2779) ∨ (¬ p 3985) :=
  ElevenRUP.step112988 (p 2417) (p 2598) (p 2696) (p 2761) (p 2779) (p 3461) (p 3654) (p 3985) (p 4641) (p 5160) (derived95706 p h) (derived96427 p h)

theorem derived112989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3193) ∨ (¬ p 2396) ∨ (p 3379) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 2753) ∨ (¬ p 2241) :=
  ElevenRUP.step112989 (p 2122) (p 2241) (p 2396) (p 2417) (p 2750) (p 2753) (p 2774) (p 3193) (p 3379) (p 4641) (derived106345 p h) (derived97629 p h) (derived96427 p h)

theorem derived112990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3343) ∨ (¬ p 5284) ∨ (¬ p 2156) ∨ (p 2651) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 3276) ∨ (¬ p 4236) :=
  ElevenRUP.step112990 (p 2156) (p 2274) (p 2396) (p 2417) (p 2651) (p 3276) (p 3343) (p 4236) (p 4641) (p 5284) (derived109950 p h) (derived96427 p h)

theorem derived112992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3631) ∨ (¬ p 3641) ∨ (¬ p 3399) ∨ (p 2241) ∨ (p 2470) ∨ (¬ p 3366) ∨ (¬ p 3905) ∨ (¬ p 5160) :=
  ElevenRUP.step112992 (p 2241) (p 2417) (p 2470) (p 2744) (p 3366) (p 3399) (p 3631) (p 3641) (p 3905) (p 4641) (p 5160) (derived106503 p h) (derived77358 p h) (derived96427 p h)

theorem derived112994 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2396) ∨ (p 3670) ∨ (p 3367) ∨ (p 2996) ∨ (¬ p 2696) ∨ (¬ p 3276) ∨ (¬ p 2742) ∨ (¬ p 3552) ∨ (¬ p 5158) :=
  ElevenRUP.step112994 (p 2396) (p 2417) (p 2696) (p 2742) (p 2996) (p 3276) (p 3367) (p 3552) (p 3670) (p 4641) (p 5158) (derived82092 p h) (derived96427 p h)

theorem derived113010 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 3343) ∨ (¬ p 2396) ∨ (p 3755) ∨ (¬ p 2274) ∨ (¬ p 2156) ∨ (¬ p 3370) ∨ (¬ p 2252) ∨ (¬ p 2741) ∨ (p 2651) ∨ (¬ p 2630) :=
  ElevenRUP.step113010 (p 2156) (p 2252) (p 2274) (p 2396) (p 2417) (p 2630) (p 2651) (p 2741) (p 3343) (p 3370) (p 3755) (p 4641) (derived109765 p h) (derived96427 p h)

theorem derived113014 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (p 2761) ∨ (¬ p 5160) ∨ (¬ p 3422) ∨ (¬ p 3680) ∨ (¬ p 3212) ∨ (¬ p 3347) ∨ (p 2573) ∨ (¬ p 3370) ∨ (¬ p 4365) ∨ (¬ p 4257) :=
  ElevenRUP.step113014 (p 2417) (p 2573) (p 2744) (p 2761) (p 3212) (p 3347) (p 3370) (p 3422) (p 3680) (p 4257) (p 4365) (p 4641) (p 5160) (derived106503 p h) (derived92347 p h) (derived96427 p h)

theorem derived113016 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3680) ∨ (p 2761) ∨ (¬ p 3016) ∨ (p 3343) ∨ (¬ p 2753) ∨ (¬ p 3212) ∨ (¬ p 2655) ∨ (¬ p 2144) ∨ (¬ p 2252) ∨ (p 2573) :=
  ElevenRUP.step113016 (p 2144) (p 2252) (p 2417) (p 2573) (p 2655) (p 2750) (p 2753) (p 2761) (p 3016) (p 3212) (p 3343) (p 3680) (p 4641) (derived106345 p h) (derived101856 p h) (derived96427 p h)

theorem derived113021 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (¬ p 4132) ∨ (¬ p 3146) :=
  ElevenRUP.step113021 (p 2459) (p 3146) (p 4132) (p 4445) (derived112665 p h) (derived96416 p h)

theorem derived113023 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4683) ∨ (¬ p 5866) ∨ (¬ p 4370) ∨ (¬ p 2509) :=
  ElevenRUP.step113023 (p 2509) (p 3453) (p 4370) (p 4683) (p 5866) (derived109516 p h) (h 7548)

theorem derived113024 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 5012) ∨ (¬ p 4043) :=
  ElevenRUP.step113024 (p 2373) (p 2531) (p 4043) (p 5012) (h 34739) (derived101940 p h)

theorem derived113026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2470) ∨ (p 2220) ∨ (¬ p 3904) :=
  ElevenRUP.step113026 (p 2220) (p 2373) (p 2470) (p 2531) (p 3904) (derived89146 p h) (derived101940 p h)

theorem derived113029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3641) ∨ (p 2220) ∨ (p 2850) :=
  ElevenRUP.step113029 (p 2220) (p 2373) (p 2531) (p 2850) (p 3641) (p 4533) (derived105394 p h) (derived77294 p h) (derived101940 p h)

theorem derived113030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2563) ∨ (¬ p 3641) ∨ (p 2850) :=
  ElevenRUP.step113030 (p 2373) (p 2531) (p 2563) (p 2850) (p 3641) (p 4509) (derived105392 p h) (derived77310 p h) (derived101940 p h)

theorem derived113031 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2470) ∨ (¬ p 4904) ∨ (p 2427) ∨ (p 2230) :=
  ElevenRUP.step113031 (p 2230) (p 2373) (p 2427) (p 2470) (p 2531) (p 4904) (derived77467 p h) (derived101940 p h)

theorem derived113032 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2470) ∨ (p 2563) ∨ (p 2230) :=
  ElevenRUP.step113032 (p 2230) (p 2373) (p 2470) (p 2531) (p 2563) (p 4509) (derived105392 p h) (derived77469 p h) (derived101940 p h)

theorem derived113033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2406) ∨ (p 2230) ∨ (¬ p 3146) ∨ (¬ p 2470) :=
  ElevenRUP.step113033 (p 2230) (p 2373) (p 2406) (p 2470) (p 2531) (p 3146) (derived77472 p h) (derived101940 p h)

theorem derived113034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2470) ∨ (¬ p 2850) ∨ (p 2230) ∨ (¬ p 3146) :=
  ElevenRUP.step113034 (p 2230) (p 2373) (p 2470) (p 2531) (p 2850) (p 3146) (derived77545 p h) (derived101940 p h)

theorem derived113035 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2470) ∨ (¬ p 3146) ∨ (p 2230) ∨ (p 2440) :=
  ElevenRUP.step113035 (p 2230) (p 2373) (p 2440) (p 2470) (p 2531) (p 3146) (derived78870 p h) (derived101940 p h)

theorem derived113038 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 2230) ∨ (p 2406) ∨ (¬ p 2518) :=
  ElevenRUP.step113038 (p 2230) (p 2373) (p 2406) (p 2518) (p 2531) (p 3146) (derived81426 p h) (derived101940 p h)

theorem derived113039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2518) ∨ (p 2220) ∨ (p 2406) :=
  ElevenRUP.step113039 (p 2220) (p 2373) (p 2406) (p 2518) (p 2531) (p 4533) (derived105394 p h) (derived81478 p h) (derived101940 p h)

theorem derived113040 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3083) ∨ (¬ p 2440) ∨ (p 2619) :=
  ElevenRUP.step113040 (p 2373) (p 2440) (p 2531) (p 2619) (p 3083) (p 4882) (derived105453 p h) (derived84771 p h) (derived101940 p h)

theorem derived113044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 6116) ∨ (¬ p 5567) ∨ (¬ p 3083) ∨ (¬ p 2440) :=
  ElevenRUP.step113044 (p 2373) (p 2440) (p 2531) (p 3083) (p 5567) (p 6116) (derived110808 p h) (derived101940 p h)

theorem derived113048 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3875) ∨ (p 3156) ∨ (¬ p 3201) ∨ (p 2850) :=
  ElevenRUP.step113048 (p 2373) (p 2531) (p 2850) (p 3156) (p 3201) (p 3875) (p 4702) (derived106079 p h) (derived77084 p h) (derived101940 p h)

theorem derived113053 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 4440) ∨ (¬ p 2518) ∨ (¬ p 3193) ∨ (¬ p 2363) :=
  ElevenRUP.step113053 (p 2363) (p 2373) (p 2518) (p 2531) (p 3193) (p 4433) (p 4440) (derived106150 p h) (derived41312 p h) (derived101940 p h)

theorem derived113057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3083) ∨ (p 2901) ∨ (¬ p 3988) ∨ (p 2992) ∨ (¬ p 3189) :=
  ElevenRUP.step113057 (p 2373) (p 2531) (p 2901) (p 2992) (p 3083) (p 3189) (p 3988) (derived112886 p h) (derived101940 p h)

theorem derived113064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 3309) ∨ (p 2177) ∨ (¬ p 2230) ∨ (p 2850) ∨ (p 3093) ∨ (¬ p 3641) :=
  ElevenRUP.step113064 (p 2177) (p 2230) (p 2373) (p 2531) (p 2850) (p 3093) (p 3309) (p 3641) (p 4902) (p 5190) (derived105456 p h) (derived105487 p h) (derived77311 p h) (derived101940 p h)

theorem derived113068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3791) ∨ (¬ p 2774) ∨ (p 2220) ∨ (¬ p 2122) ∨ (p 2528) ∨ (p 3266) ∨ (¬ p 2145) :=
  ElevenRUP.step113068 (p 2122) (p 2145) (p 2220) (p 2373) (p 2528) (p 2531) (p 2774) (p 3266) (p 3791) (p 4826) (derived105444 p h) (derived92530 p h) (derived101940 p h)

theorem derived113070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (p 2761) ∨ (¬ p 3506) ∨ (¬ p 3286) ∨ (p 3379) ∨ (p 2166) ∨ (p 2528) ∨ (¬ p 4202) ∨ (¬ p 3950) :=
  ElevenRUP.step113070 (p 2166) (p 2248) (p 2373) (p 2528) (p 2531) (p 2761) (p 3286) (p 3379) (p 3506) (p 3950) (p 4202) (derived105365 p h) (derived76087 p h) (derived101940 p h)

theorem derived113071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2518) ∨ (p 2797) ∨ (p 2406) ∨ (¬ p 4079) ∨ (¬ p 2230) ∨ (p 2696) ∨ (p 2668) :=
  ElevenRUP.step113071 (p 2230) (p 2373) (p 2406) (p 2518) (p 2531) (p 2668) (p 2696) (p 2797) (p 4079) (p 4433) (p 4736) (derived105431 p h) (derived106150 p h) (derived81362 p h) (derived101940 p h)

theorem derived113072 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 5580) ∨ (¬ p 3146) ∨ (p 2668) ∨ (¬ p 2470) ∨ (¬ p 3136) ∨ (¬ p 2951) ∨ (¬ p 3904) ∨ (p 2331) :=
  ElevenRUP.step113072 (p 2331) (p 2373) (p 2470) (p 2531) (p 2668) (p 2951) (p 3136) (p 3146) (p 3904) (p 5118) (p 5580) (derived105482 p h) (derived84898 p h) (derived101940 p h)

theorem derived113081 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2373) ∨ (¬ p 2982) :=
  ElevenRUP.step113081 (p 2373) (p 2982) (p 3146) (p 4335) (derived78951 p h) (derived100454 p h)

theorem derived113082 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3156) ∨ (¬ p 3115) :=
  ElevenRUP.step113082 (p 3115) (p 3146) (p 3156) (p 4335) (h 17494) (derived100454 p h)

theorem derived113083 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2166) ∨ (¬ p 2972) :=
  ElevenRUP.step113083 (p 2166) (p 2972) (p 3146) (p 4335) (h 6871) (derived100454 p h)

theorem derived113084 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2619) ∨ (¬ p 3105) :=
  ElevenRUP.step113084 (p 2619) (p 3105) (p 3146) (p 4335) (h 6858) (derived100454 p h)

theorem derived113085 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2220) ∨ (¬ p 3212) :=
  ElevenRUP.step113085 (p 2220) (p 3146) (p 3212) (p 4335) (derived92494 p h) (derived100454 p h)

theorem derived113087 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2166) ∨ (¬ p 4282) ∨ (¬ p 3115) :=
  ElevenRUP.step113087 (p 2166) (p 3115) (p 3146) (p 4282) (p 4335) (derived76073 p h) (derived100454 p h)

theorem derived113094 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3609) ∨ (¬ p 3266) ∨ (¬ p 4322) ∨ (¬ p 4746) :=
  ElevenRUP.step113094 (p 3146) (p 3266) (p 3609) (p 4322) (p 4335) (p 4746) (derived49501 p h) (derived100454 p h)

theorem derived113095 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3266) ∨ (¬ p 4322) ∨ (¬ p 2459) :=
  ElevenRUP.step113095 (p 2459) (p 3146) (p 3266) (p 4322) (p 4335) (p 4902) (derived105456 p h) (derived57865 p h) (derived100454 p h)

theorem derived113096 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3266) ∨ (¬ p 2363) ∨ (¬ p 4322) :=
  ElevenRUP.step113096 (p 2363) (p 3146) (p 3266) (p 4322) (p 4335) (p 4433) (derived106150 p h) (derived41793 p h) (derived100454 p h)

theorem derived113097 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3379) ∨ (p 2166) ∨ (¬ p 2406) ∨ (¬ p 2982) :=
  ElevenRUP.step113097 (p 2166) (p 2406) (p 2982) (p 3146) (p 3379) (p 4335) (derived76064 p h) (derived100454 p h)

theorem derived113103 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2972) ∨ (¬ p 3266) ∨ (¬ p 2363) ∨ (p 3707) :=
  ElevenRUP.step113103 (p 2363) (p 2972) (p 3146) (p 3266) (p 3707) (p 4335) (derived110507 p h) (derived100454 p h)

theorem derived113105 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3193) ∨ (p 2619) ∨ (p 2406) ∨ (¬ p 4952) :=
  ElevenRUP.step113105 (p 2406) (p 2619) (p 3146) (p 3193) (p 4335) (p 4882) (p 4952) (derived105453 p h) (derived81685 p h) (derived100454 p h)

theorem derived113106 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2284) ∨ (p 2860) ∨ (p 2373) ∨ (¬ p 3105) :=
  ElevenRUP.step113106 (p 2284) (p 2373) (p 2860) (p 3105) (p 3146) (p 4335) (p 4705) (derived106238 p h) (derived83244 p h) (derived100454 p h)

theorem derived113107 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 4042) ∨ (p 2177) ∨ (p 2901) ∨ (¬ p 3115) :=
  ElevenRUP.step113107 (p 2177) (p 2901) (p 3115) (p 3146) (p 4042) (p 4335) (p 4559) (derived105701 p h) (derived83373 p h) (derived100454 p h)

theorem derived113117 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2396) ∨ (¬ p 3506) ∨ (¬ p 4656) ∨ (¬ p 4119) ∨ (¬ p 4322) :=
  ElevenRUP.step113117 (p 2396) (p 3146) (p 3506) (p 4119) (p 4322) (p 4335) (p 4556) (p 4656) (derived105399 p h) (derived58079 p h) (derived100454 p h)

theorem derived113118 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2220) ∨ (¬ p 2241) ∨ (¬ p 3343) ∨ (¬ p 2727) ∨ (¬ p 3266) ∨ (¬ p 4322) ∨ (¬ p 4332) :=
  ElevenRUP.step113118 (p 2220) (p 2241) (p 2727) (p 3146) (p 3266) (p 3343) (p 4322) (p 4332) (p 4335) (derived75850 p h) (derived100454 p h)

theorem derived113124 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 3256) ∨ (p 3166) ∨ (¬ p 2363) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 3105) :=
  ElevenRUP.step113124 (p 2254) (p 2363) (p 2608) (p 2839) (p 3105) (p 3146) (p 3166) (p 3256) (p 4335) (p 4433) (derived105366 p h) (derived106150 p h) (derived100989 p h) (derived100454 p h)

theorem derived113125 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 3266) ∨ (¬ p 2145) ∨ (p 2220) ∨ (¬ p 4322) ∨ (¬ p 3343) ∨ (¬ p 3362) ∨ (p 2437) ∨ (¬ p 3389) ∨ (¬ p 4332) :=
  ElevenRUP.step113125 (p 2145) (p 2220) (p 2437) (p 3146) (p 3266) (p 3343) (p 3362) (p 3389) (p 4322) (p 4332) (p 4335) (derived75835 p h) (derived100454 p h)

theorem derived113130 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 2922) ∨ (¬ p 2850) ∨ (p 2946) ∨ (p 3156) ∨ (p 3201) ∨ (¬ p 3266) ∨ (¬ p 2252) ∨ (¬ p 3541) ∨ (¬ p 4322) :=
  ElevenRUP.step113130 (p 2252) (p 2750) (p 2850) (p 2922) (p 2946) (p 3146) (p 3156) (p 3201) (p 3266) (p 3541) (p 4322) (p 4335) (derived106345 p h) (derived87881 p h) (derived100454 p h)

theorem derived113132 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 4322) ∨ (¬ p 3016) ∨ (¬ p 2651) ∨ (p 2220) ∨ (¬ p 3564) ∨ (¬ p 2246) ∨ (¬ p 3266) ∨ (¬ p 2749) ∨ (¬ p 3645) :=
  ElevenRUP.step113132 (p 2220) (p 2246) (p 2651) (p 2749) (p 3016) (p 3146) (p 3266) (p 3564) (p 3645) (p 4322) (p 4330) (p 4335) (p 4877) (derived106329 p h) (derived105451 p h) (derived83388 p h) (derived100454 p h)

theorem derived113133 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (¬ p 4322) ∨ (¬ p 3519) ∨ (p 3016) ∨ (p 2220) ∨ (¬ p 3266) ∨ (¬ p 3366) ∨ (¬ p 3343) ∨ (¬ p 2136) ∨ (¬ p 2573) ∨ (¬ p 4332) :=
  ElevenRUP.step113133 (p 2136) (p 2220) (p 2573) (p 3016) (p 3146) (p 3266) (p 3343) (p 3366) (p 3519) (p 4322) (p 4332) (p 4335) (p 4376) (derived106320 p h) (derived95121 p h) (derived100454 p h)

theorem derived113138 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2274) ∨ (¬ p 2122) :=
  ElevenRUP.step113138 (p 2122) (p 2274) (p 2860) (p 4428) (derived77772 p h) (derived95791 p h)

theorem derived113139 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2819) ∨ (p 2187) :=
  ElevenRUP.step113139 (p 2187) (p 2819) (p 2860) (p 4428) (derived86175 p h) (derived95791 p h)

theorem derived113140 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 3125) ∨ (¬ p 3483) :=
  ElevenRUP.step113140 (p 2860) (p 3125) (p 3483) (p 4428) (derived90207 p h) (derived95791 p h)

theorem derived113142 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2156) ∨ (p 2829) ∨ (¬ p 2839) :=
  ElevenRUP.step113142 (p 2156) (p 2829) (p 2839) (p 2860) (p 4428) (derived83683 p h) (derived95791 p h)

theorem derived113145 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2619) ∨ (¬ p 2839) ∨ (p 2829) :=
  ElevenRUP.step113145 (p 2619) (p 2829) (p 2839) (p 2860) (p 4428) (p 4509) (derived105392 p h) (derived83652 p h) (derived95791 p h)

theorem derived113146 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2829) ∨ (¬ p 2839) ∨ (¬ p 2870) :=
  ElevenRUP.step113146 (p 2829) (p 2839) (p 2860) (p 2870) (p 4428) (p 4558) (derived105400 p h) (derived83656 p h) (derived95791 p h)

theorem derived113147 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2829) ∨ (¬ p 2563) ∨ (¬ p 2839) :=
  ElevenRUP.step113147 (p 2563) (p 2829) (p 2839) (p 2860) (p 4428) (p 4882) (derived105453 p h) (derived83684 p h) (derived95791 p h)

theorem derived113148 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2284) ∨ (¬ p 2839) ∨ (p 2829) :=
  ElevenRUP.step113148 (p 2284) (p 2829) (p 2839) (p 2860) (p 4428) (p 4906) (derived105632 p h) (derived83714 p h) (derived95791 p h)

theorem derived113149 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2284) ∨ (¬ p 2132) ∨ (p 2774) :=
  ElevenRUP.step113149 (p 2132) (p 2284) (p 2774) (p 2860) (p 4428) (p 4906) (derived105632 p h) (derived86305 p h) (derived95791 p h)

theorem derived113150 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2192) ∨ (p 2774) ∨ (¬ p 2132) :=
  ElevenRUP.step113150 (p 2132) (p 2192) (p 2774) (p 2860) (p 4428) (p 4878) (derived105452 p h) (derived86314 p h) (derived95791 p h)

theorem derived113151 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 3367) ∨ (¬ p 2563) ∨ (p 2774) ∨ (¬ p 2598) :=
  ElevenRUP.step113151 (p 2563) (p 2598) (p 2774) (p 2860) (p 3367) (p 4428) (derived86356 p h) (derived95791 p h)

theorem derived113153 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3105) ∨ (¬ p 2132) ∨ (p 2774) :=
  ElevenRUP.step113153 (p 2132) (p 2774) (p 2860) (p 3105) (p 4428) (p 5046) (derived105472 p h) (derived86406 p h) (derived95791 p h)

theorem derived113154 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2132) ∨ (p 2774) ∨ (¬ p 2870) :=
  ElevenRUP.step113154 (p 2132) (p 2774) (p 2860) (p 2870) (p 4428) (p 4558) (derived105400 p h) (derived86431 p h) (derived95791 p h)

theorem derived113158 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2274) ∨ (¬ p 2132) ∨ (p 2774) ∨ (p 2839) :=
  ElevenRUP.step113158 (p 2132) (p 2274) (p 2774) (p 2839) (p 2860) (p 4428) (derived90694 p h) (derived95791 p h)

theorem derived113159 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2132) ∨ (p 2187) ∨ (p 2839) ∨ (p 2774) :=
  ElevenRUP.step113159 (p 2132) (p 2187) (p 2774) (p 2839) (p 2860) (p 4428) (derived90695 p h) (derived95791 p h)

theorem derived113160 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2122) ∨ (¬ p 3425) ∨ (¬ p 2132) ∨ (¬ p 2284) :=
  ElevenRUP.step113160 (p 2122) (p 2132) (p 2284) (p 2860) (p 3425) (p 4428) (derived111332 p h) (derived95791 p h)

theorem derived113161 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2891) ∨ (p 2774) ∨ (¬ p 4418) ∨ (¬ p 2132) :=
  ElevenRUP.step113161 (p 2132) (p 2774) (p 2860) (p 2891) (p 4418) (p 4428) (p 4558) (derived105400 p h) (derived80770 p h) (derived95791 p h)

theorem derived113168 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2166) ∨ (p 3093) ∨ (¬ p 2210) ∨ (¬ p 3918) :=
  ElevenRUP.step113168 (p 2166) (p 2210) (p 2860) (p 3093) (p 3918) (p 4428) (p 4509) (derived105392 p h) (derived91239 p h) (derived95791 p h)

theorem derived113171 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2122) ∨ (¬ p 3434) ∨ (p 2417) ∨ (¬ p 2441) ∨ (¬ p 2373) :=
  ElevenRUP.step113171 (p 2122) (p 2373) (p 2417) (p 2441) (p 2860) (p 3434) (p 4428) (derived111342 p h) (derived95791 p h)

theorem derived113172 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2122) ∨ (¬ p 3434) ∨ (¬ p 3156) ∨ (p 2449) ∨ (¬ p 4386) :=
  ElevenRUP.step113172 (p 2122) (p 2449) (p 2860) (p 3156) (p 3434) (p 4386) (p 4428) (derived111343 p h) (derived95791 p h)

theorem derived113174 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2819) ∨ (¬ p 2901) ∨ (p 2383) ∨ (¬ p 2957) ∨ (¬ p 4198) :=
  ElevenRUP.step113174 (p 2383) (p 2819) (p 2860) (p 2901) (p 2957) (p 4198) (p 4428) (p 4558) (derived105400 p h) (derived86259 p h) (derived95791 p h)

theorem derived113177 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2210) ∨ (¬ p 2373) ∨ (¬ p 4210) ∨ (¬ p 3918) ∨ (p 3093) :=
  ElevenRUP.step113177 (p 2210) (p 2373) (p 2860) (p 3093) (p 3918) (p 4210) (p 4428) (p 4509) (derived105392 p h) (derived91243 p h) (derived95791 p h)

theorem derived113186 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 3564) ∨ (p 3125) ∨ (¬ p 2819) ∨ (p 2383) ∨ (p 2437) ∨ (¬ p 3389) ∨ (¬ p 3343) ∨ (¬ p 2663) ∨ (¬ p 4198) ∨ (¬ p 2136) :=
  ElevenRUP.step113186 (p 2136) (p 2383) (p 2437) (p 2663) (p 2819) (p 2860) (p 3125) (p 3343) (p 3389) (p 3564) (p 4198) (p 4428) (derived110053 p h) (derived95791 p h)

theorem derived113197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2696) ∨ (p 2598) :=
  ElevenRUP.step113197 (p 2598) (p 2630) (p 2696) (p 3475) (derived82947 p h) (derived96403 p h)

theorem derived113198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2737) ∨ (p 3367) :=
  ElevenRUP.step113198 (p 2630) (p 2737) (p 3367) (p 3475) (derived82950 p h) (derived96403 p h)

theorem derived113199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 4313) ∨ (¬ p 3582) :=
  ElevenRUP.step113199 (p 2630) (p 3475) (p 3582) (p 4313) (h 34296) (derived96403 p h)

theorem derived113200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2651) ∨ (p 2437) ∨ (¬ p 3201) :=
  ElevenRUP.step113200 (p 2437) (p 2630) (p 2651) (p 3201) (p 3475) (derived75113 p h) (derived96403 p h)

theorem derived113201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2651) ∨ (¬ p 2440) ∨ (¬ p 2850) :=
  ElevenRUP.step113201 (p 2440) (p 2630) (p 2651) (p 2850) (p 3475) (derived82946 p h) (derived96403 p h)

theorem derived113202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2911) ∨ (¬ p 2437) ∨ (p 3016) ∨ (¬ p 3422) :=
  ElevenRUP.step113202 (p 2437) (p 2630) (p 2911) (p 3016) (p 3422) (p 3475) (derived77624 p h) (derived96403 p h)

theorem derived113203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2901) ∨ (¬ p 2870) ∨ (¬ p 3582) ∨ (p 2946) :=
  ElevenRUP.step113203 (p 2630) (p 2870) (p 2901) (p 2946) (p 3475) (p 3582) (derived81605 p h) (derived96403 p h)

theorem derived113205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2651) ∨ (¬ p 3487) ∨ (p 2493) ∨ (¬ p 3422) :=
  ElevenRUP.step113205 (p 2493) (p 2630) (p 2651) (p 3422) (p 3475) (p 3487) (derived82953 p h) (derived96403 p h)

theorem derived113206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2437) ∨ (p 2651) ∨ (¬ p 3920) ∨ (¬ p 3422) :=
  ElevenRUP.step113206 (p 2437) (p 2630) (p 2651) (p 3422) (p 3475) (p 3920) (derived82954 p h) (derived96403 p h)

theorem derived113209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2573) ∨ (p 3136) ∨ (¬ p 2662) ∨ (¬ p 3422) :=
  ElevenRUP.step113209 (p 2573) (p 2630) (p 2662) (p 3136) (p 3422) (p 3475) (derived82967 p h) (derived96403 p h)

theorem derived113210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 3136) ∨ (p 3389) ∨ (¬ p 2662) ∨ (¬ p 3201) :=
  ElevenRUP.step113210 (p 2630) (p 2662) (p 3136) (p 3201) (p 3389) (p 3475) (derived82970 p h) (derived96403 p h)

theorem derived113211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2685) ∨ (¬ p 3759) ∨ (¬ p 5201) ∨ (¬ p 4155) :=
  ElevenRUP.step113211 (p 2630) (p 2685) (p 3475) (p 3759) (p 4155) (p 5201) (derived82972 p h) (derived96403 p h)

theorem derived113212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 3343) ∨ (p 2797) ∨ (¬ p 3333) ∨ (¬ p 4972) :=
  ElevenRUP.step113212 (p 2630) (p 2797) (p 3333) (p 3343) (p 3475) (p 4972) (derived82974 p h) (derived96403 p h)

theorem derived113215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2662) ∨ (p 2797) ∨ (¬ p 2850) ∨ (p 2230) :=
  ElevenRUP.step113215 (p 2230) (p 2630) (p 2662) (p 2797) (p 2850) (p 3475) (derived107290 p h) (derived96403 p h)

theorem derived113220 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2727) ∨ (¬ p 2662) ∨ (¬ p 3201) ∨ (p 3389) :=
  ElevenRUP.step113220 (p 2630) (p 2662) (p 2727) (p 2745) (p 3201) (p 3389) (p 3475) (derived105523 p h) (derived77186 p h) (derived96403 p h)

theorem derived113221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3641) ∨ (p 2470) ∨ (¬ p 2662) ∨ (p 2727) :=
  ElevenRUP.step113221 (p 2470) (p 2630) (p 2662) (p 2727) (p 2745) (p 3475) (p 3641) (derived105523 p h) (derived77308 p h) (derived96403 p h)

theorem derived113222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2573) ∨ (¬ p 2132) ∨ (¬ p 3422) ∨ (¬ p 3905) :=
  ElevenRUP.step113222 (p 2132) (p 2573) (p 2630) (p 3422) (p 3475) (p 3905) (p 5052) (derived105473 p h) (derived77594 p h) (derived96403 p h)

theorem derived113223 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2573) ∨ (p 2727) ∨ (¬ p 3422) ∨ (¬ p 2662) :=
  ElevenRUP.step113223 (p 2573) (p 2630) (p 2662) (p 2727) (p 2745) (p 3422) (p 3475) (derived105523 p h) (derived77648 p h) (derived96403 p h)

theorem derived113225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2774) ∨ (¬ p 3905) ∨ (¬ p 4845) ∨ (p 2230) ∨ (¬ p 2850) :=
  ElevenRUP.step113225 (p 2230) (p 2630) (p 2774) (p 2850) (p 3475) (p 3905) (p 4845) (derived82958 p h) (derived96403 p h)

theorem derived113227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2406) ∨ (¬ p 2829) ∨ (¬ p 4257) ∨ (¬ p 4845) ∨ (¬ p 2850) :=
  ElevenRUP.step113227 (p 2406) (p 2630) (p 2829) (p 2850) (p 3475) (p 4257) (p 4845) (derived82965 p h) (derived96403 p h)

theorem derived113229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2509) ∨ (¬ p 2839) ∨ (¬ p 3641) ∨ (¬ p 4257) :=
  ElevenRUP.step113229 (p 2509) (p 2630) (p 2839) (p 3475) (p 3641) (p 4257) (p 5052) (derived105473 p h) (derived50098 p h) (derived96403 p h)

theorem derived113230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2922) ∨ (¬ p 2839) ∨ (¬ p 4257) ∨ (¬ p 3201) :=
  ElevenRUP.step113230 (p 2630) (p 2839) (p 2922) (p 3201) (p 3475) (p 4257) (p 5052) (derived105473 p h) (derived83829 p h) (derived96403 p h)

theorem derived113231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2685) ∨ (¬ p 4650) ∨ (p 2230) ∨ (¬ p 2662) ∨ (¬ p 2850) :=
  ElevenRUP.step113231 (p 2230) (p 2630) (p 2662) (p 2685) (p 2850) (p 3475) (p 4650) (derived87712 p h) (derived96403 p h)

theorem derived113234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2662) ∨ (¬ p 2850) ∨ (p 2230) ∨ (p 2727) :=
  ElevenRUP.step113234 (p 2230) (p 2630) (p 2662) (p 2727) (p 2745) (p 2850) (p 3475) (derived105523 p h) (derived87809 p h) (derived96403 p h)

theorem derived113235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3156) ∨ (¬ p 3212) ∨ (p 3115) ∨ (¬ p 4109) ∨ (¬ p 2850) :=
  ElevenRUP.step113235 (p 2630) (p 2850) (p 3115) (p 3156) (p 3212) (p 3475) (p 4109) (derived87817 p h) (derived96403 p h)

theorem derived113241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2573) ∨ (¬ p 3759) ∨ (¬ p 2839) ∨ (p 2493) ∨ (¬ p 4257) :=
  ElevenRUP.step113241 (p 2493) (p 2573) (p 2630) (p 2839) (p 3475) (p 3759) (p 4257) (p 5052) (derived105473 p h) (derived83828 p h) (derived96403 p h)

theorem derived113253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (p 2707) ∨ (p 3083) ∨ (¬ p 2132) ∨ (¬ p 2470) ∨ (¬ p 3759) ∨ (p 3434) ∨ (¬ p 3343) ∨ (p 3366) :=
  ElevenRUP.step113253 (p 2132) (p 2470) (p 2630) (p 2707) (p 3083) (p 3343) (p 3366) (p 3434) (p 3475) (p 3759) (p 4638) (p 5052) (derived105473 p h) (derived105409 p h) (derived88320 p h) (derived96403 p h)

theorem derived113255 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 3063) ∨ (p 2187) :=
  ElevenRUP.step113255 (p 2187) (p 2192) (p 3063) (p 3957) (derived83449 p h) (derived96469 p h)

theorem derived113256 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 3309) ∨ (p 2274) :=
  ElevenRUP.step113256 (p 2192) (p 2274) (p 3309) (p 3957) (h 33487) (derived96469 p h)

theorem derived113257 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 4756) ∨ (p 2274) :=
  ElevenRUP.step113257 (p 2192) (p 2274) (p 3957) (p 4756) (derived91548 p h) (derived96469 p h)

theorem derived113258 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 2507) :=
  ElevenRUP.step113258 (p 2192) (p 2507) (p 3957) (p 3958) (derived105378 p h) (h 5871) (derived96469 p h)

theorem derived113259 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 3093) ∨ (¬ p 2563) ∨ (¬ p 2210) :=
  ElevenRUP.step113259 (p 2192) (p 2210) (p 2563) (p 3093) (p 3957) (derived107120 p h) (derived96469 p h)

theorem derived113261 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 4210) ∨ (¬ p 2563) ∨ (p 4338) :=
  ElevenRUP.step113261 (p 2192) (p 2563) (p 3957) (p 4210) (p 4338) (h 21659) (derived96469 p h)

theorem derived113262 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 4210) ∨ (¬ p 2563) ∨ (¬ p 4512) :=
  ElevenRUP.step113262 (p 2192) (p 2563) (p 3957) (p 4210) (p 4512) (h 18288) (derived96469 p h)

theorem derived113263 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2284) ∨ (¬ p 4512) ∨ (¬ p 4282) :=
  ElevenRUP.step113263 (p 2192) (p 2284) (p 3957) (p 4282) (p 4512) (h 38297) (derived96469 p h)

theorem derived113265 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2156) ∨ (¬ p 4512) ∨ (¬ p 3370) :=
  ElevenRUP.step113265 (p 2156) (p 2192) (p 3370) (p 3957) (p 4512) (h 14928) (derived96469 p h)

theorem derived113267 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 2177) ∨ (p 2274) ∨ (p 3093) ∨ (¬ p 2210) :=
  ElevenRUP.step113267 (p 2177) (p 2192) (p 2210) (p 2274) (p 3093) (p 3957) (derived80351 p h) (derived96469 p h)

theorem derived113268 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2210) ∨ (p 3093) ∨ (¬ p 2860) :=
  ElevenRUP.step113268 (p 2192) (p 2210) (p 2860) (p 3093) (p 3957) (p 4875) (derived106227 p h) (derived80380 p h) (derived96469 p h)

theorem derived113269 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2210) ∨ (¬ p 4957) ∨ (¬ p 2284) ∨ (p 3093) :=
  ElevenRUP.step113269 (p 2192) (p 2210) (p 2284) (p 3093) (p 3957) (p 4957) (derived80383 p h) (derived96469 p h)

theorem derived113270 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 3461) ∨ (p 3125) ∨ (¬ p 2210) ∨ (p 3093) :=
  ElevenRUP.step113270 (p 2192) (p 2210) (p 3093) (p 3125) (p 3461) (p 3957) (derived80389 p h) (derived96469 p h)

theorem derived113271 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2210) ∨ (¬ p 2891) ∨ (p 3093) :=
  ElevenRUP.step113271 (p 2192) (p 2210) (p 2891) (p 3093) (p 3957) (p 4558) (derived105400 p h) (derived80393 p h) (derived96469 p h)

theorem derived113273 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 3309) ∨ (p 2220) ∨ (¬ p 2156) ∨ (¬ p 4506) :=
  ElevenRUP.step113273 (p 2156) (p 2192) (p 2220) (p 3309) (p 3957) (p 4506) (derived91556 p h) (derived96469 p h)

theorem derived113274 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 3319) ∨ (¬ p 3917) ∨ (¬ p 2156) ∨ (¬ p 2819) :=
  ElevenRUP.step113274 (p 2156) (p 2192) (p 2819) (p 3319) (p 3917) (p 3957) (derived53091 p h) (derived96469 p h)

theorem derived113285 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2156) ∨ (¬ p 4512) ∨ (p 2427) ∨ (¬ p 2891) :=
  ElevenRUP.step113285 (p 2156) (p 2192) (p 2427) (p 2891) (p 3957) (p 4512) (p 4539) (derived105395 p h) (derived91549 p h) (derived96469 p h)

theorem derived113286 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (p 2274) ∨ (¬ p 3830) ∨ (¬ p 5152) ∨ (p 3093) :=
  ElevenRUP.step113286 (p 2192) (p 2274) (p 3093) (p 3830) (p 3957) (p 4624) (p 5152) (derived105408 p h) (derived91550 p h) (derived96469 p h)

theorem derived113289 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2210) ∨ (¬ p 3156) ∨ (p 3093) ∨ (¬ p 4282) :=
  ElevenRUP.step113289 (p 2192) (p 2210) (p 3093) (p 3156) (p 3957) (p 4282) (p 4509) (derived105392 p h) (derived91559 p h) (derived96469 p h)

theorem derived113290 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 3063) ∨ (p 2274) ∨ (¬ p 2778) ∨ (¬ p 2132) ∨ (p 2383) :=
  ElevenRUP.step113290 (p 2132) (p 2192) (p 2274) (p 2383) (p 2778) (p 3063) (p 3957) (derived91560 p h) (derived96469 p h)

theorem derived113294 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2667) ∨ (¬ p 3136) ∨ (p 2797) ∨ (¬ p 2563) ∨ (¬ p 5016) :=
  ElevenRUP.step113294 (p 2192) (p 2563) (p 2667) (p 2797) (p 3136) (p 3957) (p 4702) (p 5016) (derived106079 p h) (derived84345 p h) (derived96469 p h)

theorem derived113309 (p : Nat → Prop) (h : Inputs p) :
    (p 2192) ∨ (¬ p 2992) ∨ (p 2363) ∨ (p 2911) ∨ (¬ p 2210) ∨ (p 2187) ∨ (p 3093) ∨ (¬ p 2264) ∨ (¬ p 2246) ∨ (¬ p 3580) ∨ (¬ p 2651) :=
  ElevenRUP.step113309 (p 2187) (p 2192) (p 2210) (p 2246) (p 2264) (p 2363) (p 2651) (p 2911) (p 2992) (p 3093) (p 3580) (p 3957) (derived110028 p h) (derived96469 p h)

theorem derived113317 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2829) ∨ (p 2839) :=
  ElevenRUP.step113317 (p 2829) (p 2839) (p 2860) (p 4193) (derived99681 p h) (derived95792 p h)

theorem derived113318 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2774) ∨ (p 2132) :=
  ElevenRUP.step113318 (p 2132) (p 2774) (p 2860) (p 4193) (derived99731 p h) (derived95792 p h)

theorem derived113321 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2829) ∨ (p 2132) ∨ (¬ p 3366) :=
  ElevenRUP.step113321 (p 2132) (p 2829) (p 2860) (p 3366) (p 4193) (derived99733 p h) (derived95792 p h)

theorem derived113325 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2619) ∨ (p 2122) ∨ (¬ p 2274) :=
  ElevenRUP.step113325 (p 2122) (p 2274) (p 2619) (p 2860) (p 4193) (p 4509) (derived105392 p h) (derived84877 p h) (derived95792 p h)

theorem derived113326 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2608) ∨ (p 2839) ∨ (¬ p 2553) ∨ (p 2122) :=
  ElevenRUP.step113326 (p 2122) (p 2553) (p 2608) (p 2839) (p 2860) (p 4193) (derived84879 p h) (derived95792 p h)

theorem derived113330 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 4869) ∨ (¬ p 3309) ∨ (p 2122) ∨ (p 2132) :=
  ElevenRUP.step113330 (p 2122) (p 2132) (p 2860) (p 3309) (p 4193) (p 4869) (derived92030 p h) (derived95792 p h)

theorem derived113333 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2274) ∨ (¬ p 2696) ∨ (p 2122) ∨ (p 2132) :=
  ElevenRUP.step113333 (p 2122) (p 2132) (p 2274) (p 2696) (p 2860) (p 4193) (derived97870 p h) (derived95792 p h)

theorem derived113334 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3917) ∨ (p 2187) ∨ (¬ p 3125) ∨ (p 2839) :=
  ElevenRUP.step113334 (p 2187) (p 2839) (p 2860) (p 3125) (p 3917) (p 4193) (derived99680 p h) (derived95792 p h)

theorem derived113335 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2274) ∨ (¬ p 2187) ∨ (p 2819) ∨ (p 2839) :=
  ElevenRUP.step113335 (p 2187) (p 2274) (p 2819) (p 2839) (p 2860) (p 4193) (derived99687 p h) (derived95792 p h)

theorem derived113336 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2274) ∨ (p 2132) ∨ (¬ p 2187) ∨ (p 2819) :=
  ElevenRUP.step113336 (p 2132) (p 2187) (p 2274) (p 2819) (p 2860) (p 4193) (derived99730 p h) (derived95792 p h)

theorem derived113337 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2819) ∨ (¬ p 2187) ∨ (¬ p 2870) :=
  ElevenRUP.step113337 (p 2187) (p 2819) (p 2860) (p 2870) (p 4193) (p 4558) (derived105400 p h) (derived100831 p h) (derived95792 p h)

theorem derived113340 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 4435) ∨ (¬ p 4329) ∨ (¬ p 3093) ∨ (¬ p 2619) :=
  ElevenRUP.step113340 (p 2619) (p 2860) (p 3093) (p 4193) (p 4329) (p 4435) (derived111302 p h) (derived95792 p h)

theorem derived113344 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3745) ∨ (¬ p 2295) ∨ (p 2122) ∨ (¬ p 3105) :=
  ElevenRUP.step113344 (p 2122) (p 2295) (p 2860) (p 3105) (p 3745) (p 4193) (p 5046) (derived105472 p h) (derived84880 p h) (derived95792 p h)

theorem derived113345 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2122) ∨ (¬ p 2553) ∨ (p 2972) ∨ (¬ p 3212) ∨ (¬ p 2137) :=
  ElevenRUP.step113345 (p 2122) (p 2137) (p 2553) (p 2860) (p 2972) (p 3212) (p 4193) (derived84887 p h) (derived95792 p h)

theorem derived113347 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 2707) ∨ (¬ p 2829) ∨ (¬ p 2901) ∨ (¬ p 4169) :=
  ElevenRUP.step113347 (p 2707) (p 2829) (p 2860) (p 2901) (p 4169) (p 4193) (p 4906) (derived105632 p h) (derived88276 p h) (derived95792 p h)

theorem derived113352 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3917) ∨ (¬ p 3745) ∨ (¬ p 3323) ∨ (¬ p 2870) :=
  ElevenRUP.step113352 (p 2860) (p 2870) (p 3323) (p 3745) (p 3917) (p 4193) (p 4558) (derived105400 p h) (derived59844 p h) (derived95792 p h)

theorem derived113353 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (p 6119) ∨ (¬ p 3717) ∨ (¬ p 2307) ∨ (¬ p 3743) ∨ (p 2122) :=
  ElevenRUP.step113353 (p 2122) (p 2307) (p 2860) (p 3717) (p 3743) (p 4193) (p 6119) (derived109215 p h) (derived95792 p h)

theorem derived113357 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 2383) ∨ (p 2819) ∨ (¬ p 2311) ∨ (¬ p 2427) ∨ (¬ p 3691) :=
  ElevenRUP.step113357 (p 2311) (p 2383) (p 2427) (p 2819) (p 2860) (p 3691) (p 4193) (p 4882) (derived105453 p h) (derived87593 p h) (derived95792 p h)

theorem derived113370 (p : Nat → Prop) (h : Inputs p) :
    (p 2860) ∨ (¬ p 3917) ∨ (¬ p 3370) ∨ (p 2417) ∨ (p 2437) ∨ (¬ p 2619) ∨ (¬ p 3125) ∨ (¬ p 3371) ∨ (¬ p 2252) ∨ (p 2651) ∨ (¬ p 2156) :=
  ElevenRUP.step113370 (p 2156) (p 2252) (p 2417) (p 2437) (p 2619) (p 2651) (p 2750) (p 2860) (p 3125) (p 3370) (p 3371) (p 3917) (p 4193) (derived106345 p h) (derived100813 p h) (derived95792 p h)

theorem derived113371 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 2761) ∨ (¬ p 3461) :=
  ElevenRUP.step113371 (p 2396) (p 2761) (p 3461) (p 4396) (derived94461 p h) (derived102221 p h)

theorem derived113372 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 4397) ∨ (¬ p 4395) :=
  ElevenRUP.step113372 (p 2396) (p 4395) (p 4396) (p 4397) (h 6735) (derived102221 p h)

theorem derived113375 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3246) ∨ (p 3125) ∨ (¬ p 3872) :=
  ElevenRUP.step113375 (p 2396) (p 3125) (p 3246) (p 3872) (p 4396) (derived78101 p h) (derived102221 p h)

theorem derived113376 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3246) ∨ (p 3564) ∨ (¬ p 2553) :=
  ElevenRUP.step113376 (p 2396) (p 2553) (p 3246) (p 3564) (p 4396) (p 4559) (derived105701 p h) (derived77030 p h) (derived102221 p h)

theorem derived113379 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 3323) ∨ (¬ p 3246) ∨ (¬ p 2295) :=
  ElevenRUP.step113379 (p 2295) (p 2396) (p 3246) (p 3323) (p 4396) (p 4559) (derived105701 p h) (derived79319 p h) (derived102221 p h)

theorem derived113380 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3516) ∨ (p 3323) ∨ (¬ p 2295) :=
  ElevenRUP.step113380 (p 2295) (p 2321) (p 2396) (p 3323) (p 3516) (p 4396) (derived105369 p h) (derived79320 p h) (derived102221 p h)

theorem derived113381 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 3323) ∨ (¬ p 2417) ∨ (¬ p 2295) :=
  ElevenRUP.step113381 (p 2295) (p 2396) (p 2417) (p 3323) (p 4396) (p 4712) (derived105422 p h) (derived79322 p h) (derived102221 p h)

theorem derived113383 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3246) ∨ (p 3319) ∨ (¬ p 3309) :=
  ElevenRUP.step113383 (p 2396) (p 3246) (p 3309) (p 3319) (p 4396) (p 4559) (derived105701 p h) (derived85330 p h) (derived102221 p h)

theorem derived113384 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2417) ∨ (p 3125) ∨ (¬ p 2274) :=
  ElevenRUP.step113384 (p 2274) (p 2396) (p 2417) (p 3125) (p 4396) (p 4712) (derived105422 p h) (derived93214 p h) (derived102221 p h)

theorem derived113385 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 3309) ∨ (¬ p 2307) ∨ (p 2761) ∨ (p 3654) :=
  ElevenRUP.step113385 (p 2307) (p 2396) (p 2761) (p 3309) (p 3654) (p 4396) (derived94458 p h) (derived102221 p h)

theorem derived113395 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 4777) ∨ (¬ p 3434) ∨ (¬ p 2274) ∨ (p 3125) ∨ (p 2264) :=
  ElevenRUP.step113395 (p 2264) (p 2274) (p 2396) (p 3125) (p 3434) (p 4396) (p 4777) (derived89641 p h) (derived102221 p h)

theorem derived113397 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2417) ∨ (p 3319) ∨ (¬ p 2295) ∨ (¬ p 3922) :=
  ElevenRUP.step113397 (p 2295) (p 2396) (p 2417) (p 3319) (p 3922) (p 4396) (p 4712) (derived105422 p h) (derived93591 p h) (derived102221 p h)

theorem derived113399 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3246) ∨ (¬ p 3922) ∨ (p 3319) ∨ (¬ p 2295) :=
  ElevenRUP.step113399 (p 2295) (p 2396) (p 3246) (p 3319) (p 3922) (p 4396) (p 4559) (derived105701 p h) (derived94463 p h) (derived102221 p h)

theorem derived113403 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3631) ∨ (p 3527) ∨ (¬ p 2341) ∨ (¬ p 4025) :=
  ElevenRUP.step113403 (p 2321) (p 2341) (p 2396) (p 3527) (p 3631) (p 4025) (p 4396) (derived105369 p h) (derived102018 p h) (derived102221 p h)

theorem derived113409 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3434) ∨ (p 3564) ∨ (¬ p 2274) ∨ (¬ p 4203) ∨ (¬ p 4777) :=
  ElevenRUP.step113409 (p 2274) (p 2396) (p 3434) (p 3564) (p 4203) (p 4361) (p 4396) (p 4777) (derived105382 p h) (derived94470 p h) (derived102221 p h)

theorem derived113414 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2761) ∨ (¬ p 3931) ∨ (p 2427) ∨ (p 2996) ∨ (p 3125) ∨ (¬ p 3872) ∨ (p 2230) ∨ (¬ p 2241) :=
  ElevenRUP.step113414 (p 2230) (p 2241) (p 2396) (p 2427) (p 2761) (p 2996) (p 3125) (p 3872) (p 3931) (p 4396) (derived108323 p h) (derived102221 p h)

theorem derived113419 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (p 3319) ∨ (¬ p 2246) ∨ (p 3093) ∨ (¬ p 3286) ∨ (p 3266) ∨ (¬ p 3506) ∨ (¬ p 2608) :=
  ElevenRUP.step113419 (p 2246) (p 2396) (p 2608) (p 2744) (p 3093) (p 3266) (p 3286) (p 3319) (p 3506) (p 4396) (p 4669) (derived106503 p h) (derived105415 p h) (derived94464 p h) (derived102221 p h)

theorem derived113421 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3516) ∨ (p 3755) ∨ (p 2946) ∨ (p 3266) ∨ (¬ p 3461) ∨ (¬ p 3136) ∨ (¬ p 4236) ∨ (¬ p 2319) ∨ (¬ p 2781) :=
  ElevenRUP.step113421 (p 2319) (p 2396) (p 2781) (p 2946) (p 3136) (p 3266) (p 3461) (p 3516) (p 3755) (p 4236) (p 4396) (p 5113) (derived105481 p h) (derived101744 p h) (derived102221 p h)

theorem derived113425 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3506) ∨ (¬ p 3286) ∨ (p 2307) ∨ (p 3266) ∨ (¬ p 3366) ∨ (¬ p 2122) ∨ (¬ p 2246) ∨ (¬ p 3917) ∨ (¬ p 2778) :=
  ElevenRUP.step113425 (p 2122) (p 2246) (p 2307) (p 2396) (p 2744) (p 2778) (p 3266) (p 3286) (p 3366) (p 3506) (p 3917) (p 4396) (p 4669) (derived106503 p h) (derived105415 p h) (derived94475 p h) (derived102221 p h)

theorem derived113429 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 3631) ∨ (p 3527) ∨ (¬ p 2341) :=
  ElevenRUP.step113429 (p 2341) (p 2396) (p 3527) (p 3631) (p 4025) (derived113403 p h) (derived91157 p h)

theorem derived113430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 4895) :=
  ElevenRUP.step113430 (p 3201) (p 3658) (p 4277) (p 4895) (derived105380 p h) (h 31070) (derived96302 p h)

theorem derived113431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2417) ∨ (p 3434) :=
  ElevenRUP.step113431 (p 2417) (p 3201) (p 3434) (p 3658) (h 26481) (derived96302 p h)

theorem derived113432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2717) ∨ (¬ p 2911) :=
  ElevenRUP.step113432 (p 2717) (p 2911) (p 3201) (p 3658) (derived76141 p h) (derived96302 p h)

theorem derived113433 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 4344) ∨ (¬ p 3569) :=
  ElevenRUP.step113433 (p 3201) (p 3569) (p 3658) (p 4344) (h 33661) (derived96302 p h)

theorem derived113435 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 3425) ∨ (p 3389) ∨ (¬ p 3905) :=
  ElevenRUP.step113435 (p 3201) (p 3389) (p 3425) (p 3658) (p 3905) (derived76131 p h) (derived96302 p h)

theorem derived113436 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2717) ∨ (¬ p 2177) ∨ (¬ p 4710) :=
  ElevenRUP.step113436 (p 2177) (p 2717) (p 3201) (p 3658) (p 4710) (derived76145 p h) (derived96302 p h)

theorem derived113437 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2707) ∨ (p 3389) ∨ (p 3367) :=
  ElevenRUP.step113437 (p 2707) (p 3201) (p 3367) (p 3389) (p 3658) (derived76159 p h) (derived96302 p h)

theorem derived113439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2459) ∨ (¬ p 2417) ∨ (p 2717) :=
  ElevenRUP.step113439 (p 2417) (p 2459) (p 2717) (p 3201) (p 3658) (derived112664 p h) (derived96302 p h)

theorem derived113440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2707) ∨ (p 2850) ∨ (p 3367) :=
  ElevenRUP.step113440 (p 2707) (p 2850) (p 3201) (p 3367) (p 3658) (p 4646) (derived105534 p h) (derived76132 p h) (derived96302 p h)

theorem derived113441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2396) ∨ (¬ p 2573) ∨ (p 3389) ∨ (p 3434) :=
  ElevenRUP.step113441 (p 2396) (p 2573) (p 3201) (p 3389) (p 3434) (p 3658) (derived76136 p h) (derived96302 p h)

theorem derived113442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 3425) ∨ (p 2437) ∨ (p 2598) :=
  ElevenRUP.step113442 (p 2437) (p 2598) (p 3201) (p 3425) (p 3658) (p 4753) (derived105514 p h) (derived76147 p h) (derived96302 p h)

theorem derived113443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2922) ∨ (p 3425) ∨ (p 2598) :=
  ElevenRUP.step113443 (p 2598) (p 2922) (p 3201) (p 3425) (p 3658) (p 5214) (derived105492 p h) (derived76152 p h) (derived96302 p h)

theorem derived113446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2707) ∨ (p 2437) ∨ (p 3367) :=
  ElevenRUP.step113446 (p 2437) (p 2707) (p 3201) (p 3367) (p 3658) (p 4753) (derived105514 p h) (derived76158 p h) (derived96302 p h)

theorem derived113448 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2707) ∨ (¬ p 2417) ∨ (p 3367) ∨ (¬ p 2598) :=
  ElevenRUP.step113448 (p 2417) (p 2598) (p 2707) (p 3201) (p 3367) (p 3658) (derived99632 p h) (derived96302 p h)

theorem derived113449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2417) ∨ (¬ p 2707) ∨ (¬ p 5160) ∨ (p 3367) :=
  ElevenRUP.step113449 (p 2417) (p 2707) (p 3201) (p 3367) (p 3658) (p 5160) (derived108312 p h) (derived96302 p h)

theorem derived113451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2717) ∨ (p 2922) ∨ (¬ p 2098) ∨ (p 2598) :=
  ElevenRUP.step113451 (p 2098) (p 2598) (p 2717) (p 2922) (p 3201) (p 3658) (derived111785 p h) (derived96302 p h)

theorem derived113452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2761) ∨ (p 3425) ∨ (¬ p 2417) ∨ (p 3367) ∨ (¬ p 2753) :=
  ElevenRUP.step113452 (p 2417) (p 2753) (p 2761) (p 3201) (p 3367) (p 3425) (p 3658) (derived75613 p h) (derived96302 p h)

theorem derived113455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3246) ∨ (¬ p 2441) ∨ (¬ p 2563) ∨ (p 3434) :=
  ElevenRUP.step113455 (p 2441) (p 2563) (p 3201) (p 3246) (p 3434) (p 3658) (p 4555) (derived105542 p h) (derived76156 p h) (derived96302 p h)

theorem derived113456 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 3425) ∨ (p 2437) ∨ (¬ p 2753) ∨ (p 3367) :=
  ElevenRUP.step113456 (p 2437) (p 2753) (p 3201) (p 3367) (p 3425) (p 3658) (p 4753) (derived105514 p h) (derived76157 p h) (derived96302 p h)

theorem derived113459 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3363) ∨ (¬ p 2707) ∨ (p 3367) ∨ (p 2230) :=
  ElevenRUP.step113459 (p 2230) (p 2707) (p 3201) (p 3363) (p 3367) (p 3658) (p 4646) (derived105534 p h) (derived81186 p h) (derived96302 p h)

theorem derived113460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2707) ∨ (¬ p 2911) ∨ (p 3367) ∨ (¬ p 2598) ∨ (¬ p 3589) :=
  ElevenRUP.step113460 (p 2598) (p 2707) (p 2911) (p 3201) (p 3367) (p 3589) (p 3658) (derived81767 p h) (derived96302 p h)

theorem derived113462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 2396) ∨ (¬ p 3581) ∨ (p 3434) ∨ (¬ p 2274) :=
  ElevenRUP.step113462 (p 2274) (p 2396) (p 3201) (p 3434) (p 3581) (p 3658) (p 3958) (derived105378 p h) (derived91299 p h) (derived96302 p h)

theorem derived113463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 2922) ∨ (¬ p 2807) ∨ (p 2651) ∨ (¬ p 4777) :=
  ElevenRUP.step113463 (p 2651) (p 2807) (p 2922) (p 3201) (p 3658) (p 4777) (p 4811) (derived105633 p h) (derived95751 p h) (derived96302 p h)

theorem derived113467 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3580) ∨ (p 3389) ∨ (¬ p 2449) ∨ (p 3434) ∨ (¬ p 3347) :=
  ElevenRUP.step113467 (p 2449) (p 3201) (p 3347) (p 3389) (p 3434) (p 3580) (p 3658) (p 4811) (derived105633 p h) (derived76138 p h) (derived96302 p h)

theorem derived113469 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (p 3425) ∨ (¬ p 2440) ∨ (¬ p 4030) ∨ (¬ p 4116) ∨ (p 2598) :=
  ElevenRUP.step113469 (p 2440) (p 2598) (p 3201) (p 3425) (p 3658) (p 4030) (p 4116) (p 4646) (derived105534 p h) (derived76151 p h) (derived96302 p h)

theorem derived113484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3868) ∨ (p 3425) ∨ (p 3256) ∨ (p 3166) ∨ (p 2598) ∨ (¬ p 3361) ∨ (p 3266) :=
  ElevenRUP.step113484 (p 2598) (p 3166) (p 3201) (p 3256) (p 3266) (p 3361) (p 3425) (p 3658) (p 3868) (p 4749) (p 4826) (derived105432 p h) (derived105444 p h) (derived97228 p h) (derived96302 p h)

theorem derived113489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 4842) :=
  ElevenRUP.step113489 (p 2860) (p 3985) (p 4842) (derived67310 p h) (derived102203 p h)

theorem derived113490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2132) ∨ (p 2774) :=
  ElevenRUP.step113490 (p 2132) (p 2774) (p 2860) (p 3985) (derived81314 p h) (derived102203 p h)

theorem derived113491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 4375) ∨ (¬ p 3582) :=
  ElevenRUP.step113491 (p 2860) (p 3582) (p 3985) (p 4375) (h 29171) (derived102203 p h)

theorem derived113492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2839) ∨ (p 2829) :=
  ElevenRUP.step113492 (p 2829) (p 2839) (p 2860) (p 3985) (h 29861) (derived102203 p h)

theorem derived113493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 4744) ∨ (¬ p 4861) :=
  ElevenRUP.step113493 (p 2860) (p 3985) (p 4744) (p 4861) (h 38989) (derived102203 p h)

theorem derived113494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2122) ∨ (p 3587) :=
  ElevenRUP.step113494 (p 2122) (p 2860) (p 3587) (p 3985) (derived111321 p h) (derived102203 p h)

theorem derived113495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2753) ∨ (p 2829) ∨ (¬ p 2132) :=
  ElevenRUP.step113495 (p 2132) (p 2753) (p 2829) (p 2860) (p 3985) (derived90696 p h) (derived102203 p h)

theorem derived113497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2819) ∨ (p 2187) ∨ (¬ p 2132) ∨ (p 2696) :=
  ElevenRUP.step113497 (p 2132) (p 2187) (p 2696) (p 2819) (p 2860) (p 3985) (derived82918 p h) (derived102203 p h)

theorem derived113498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2819) ∨ (p 2187) ∨ (¬ p 2608) ∨ (¬ p 2839) :=
  ElevenRUP.step113498 (p 2187) (p 2608) (p 2819) (p 2839) (p 2860) (p 3985) (derived83628 p h) (derived102203 p h)

theorem derived113500 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3483) ∨ (¬ p 2839) ∨ (p 3367) ∨ (p 3125) :=
  ElevenRUP.step113500 (p 2839) (p 2860) (p 3125) (p 3367) (p 3483) (p 3985) (derived83685 p h) (derived102203 p h)

theorem derived113501 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2177) ∨ (p 2737) ∨ (¬ p 2839) ∨ (¬ p 2122) :=
  ElevenRUP.step113501 (p 2122) (p 2177) (p 2737) (p 2839) (p 2860) (p 3985) (derived83843 p h) (derived102203 p h)

theorem derived113504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2274) ∨ (¬ p 2122) ∨ (p 2156) :=
  ElevenRUP.step113504 (p 2122) (p 2140) (p 2156) (p 2274) (p 2860) (p 3985) (derived105364 p h) (derived85480 p h) (derived102203 p h)

theorem derived113507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2819) ∨ (p 2870) ∨ (p 2187) :=
  ElevenRUP.step113507 (p 2187) (p 2819) (p 2860) (p 2870) (p 3985) (p 4555) (derived105542 p h) (derived86737 p h) (derived102203 p h)

theorem derived113510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2284) ∨ (p 3125) ∨ (¬ p 3483) ∨ (¬ p 5053) :=
  ElevenRUP.step113510 (p 2284) (p 2860) (p 3125) (p 3483) (p 3985) (p 5053) (derived91258 p h) (derived102203 p h)

theorem derived113517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2819) ∨ (p 2192) ∨ (p 2383) ∨ (¬ p 4356) :=
  ElevenRUP.step113517 (p 2192) (p 2383) (p 2819) (p 2860) (p 3985) (p 4356) (p 4875) (derived106227 p h) (derived86277 p h) (derived102203 p h)

theorem derived113518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2573) ∨ (p 3564) ∨ (¬ p 3483) ∨ (¬ p 3905) ∨ (p 2870) :=
  ElevenRUP.step113518 (p 2573) (p 2860) (p 2870) (p 3483) (p 3564) (p 3905) (p 3985) (derived86820 p h) (derived102203 p h)

theorem derived113522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2284) ∨ (¬ p 4356) ∨ (¬ p 5053) ∨ (¬ p 2122) ∨ (p 2307) :=
  ElevenRUP.step113522 (p 2122) (p 2284) (p 2307) (p 2860) (p 3985) (p 4356) (p 5053) (derived90355 p h) (derived102203 p h)

theorem derived113523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2274) ∨ (¬ p 2122) ∨ (¬ p 2143) ∨ (¬ p 4032) :=
  ElevenRUP.step113523 (p 2122) (p 2143) (p 2274) (p 2860) (p 3985) (p 4032) (p 5043) (derived105471 p h) (derived90401 p h) (derived102203 p h)

theorem derived113535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2102) ∨ (¬ p 4313) ∨ (p 2088) ∨ (¬ p 3073) ∨ (¬ p 3918) ∨ (¬ p 4317) ∨ (p 3425) :=
  ElevenRUP.step113535 (p 2088) (p 2102) (p 2860) (p 3073) (p 3425) (p 3918) (p 3985) (p 4313) (p 4317) (derived107571 p h) (derived102203 p h)

theorem derived113539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 3073) ∨ (p 3449) ∨ (¬ p 3950) ∨ (¬ p 2132) ∨ (¬ p 3379) ∨ (¬ p 2122) ∨ (¬ p 2753) ∨ (¬ p 2396) :=
  ElevenRUP.step113539 (p 2122) (p 2132) (p 2396) (p 2753) (p 2860) (p 3073) (p 3379) (p 3449) (p 3950) (p 3985) (derived90810 p h) (derived102203 p h)

theorem derived113540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3564) ∨ (¬ p 2696) ∨ (p 2274) ∨ (p 2598) ∨ (¬ p 3125) ∨ (¬ p 5160) ∨ (¬ p 2779) ∨ (¬ p 2307) :=
  ElevenRUP.step113540 (p 2274) (p 2307) (p 2598) (p 2696) (p 2779) (p 2860) (p 3125) (p 3564) (p 3985) (p 5160) (derived109846 p h) (derived102203 p h)

theorem derived113541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 2417) ∨ (¬ p 5160) ∨ (p 2761) ∨ (¬ p 3461) ∨ (¬ p 3654) ∨ (¬ p 2696) ∨ (p 2598) ∨ (¬ p 2779) :=
  ElevenRUP.step113541 (p 2417) (p 2598) (p 2696) (p 2761) (p 2779) (p 2860) (p 3461) (p 3654) (p 3985) (p 5160) (derived112988 p h) (derived102203 p h)

theorem derived113545 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (p 2470) ∨ (¬ p 2122) ∨ (p 2274) ∨ (p 3016) ∨ (¬ p 2132) ∨ (¬ p 3083) ∨ (¬ p 3589) :=
  ElevenRUP.step113545 (p 2122) (p 2132) (p 2274) (p 2470) (p 2860) (p 3016) (p 3083) (p 3589) (p 3985) (p 4718) (p 5193) (derived105425 p h) (derived105488 p h) (derived90406 p h) (derived102203 p h)

theorem derived113547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3276) ∨ (¬ p 3945) ∨ (p 3266) ∨ (p 2829) ∨ (¬ p 2341) ∨ (p 3105) ∨ (p 2608) ∨ (¬ p 4636) ∨ (¬ p 5059) :=
  ElevenRUP.step113547 (p 2341) (p 2608) (p 2829) (p 2860) (p 3105) (p 3266) (p 3276) (p 3945) (p 3985) (p 4636) (p 5059) (p 5207) (derived105491 p h) (derived84537 p h) (derived102203 p h)

theorem derived113549 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2927) ∨ (¬ p 4106) :=
  ElevenRUP.step113549 (p 2707) (p 2927) (p 4106) (p 4424) (h 29557) (derived96390 p h)

theorem derived113550 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3527) ∨ (p 2717) :=
  ElevenRUP.step113550 (p 2707) (p 2717) (p 3527) (p 4424) (derived93490 p h) (derived96390 p h)

theorem derived113551 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3631) ∨ (p 3434) :=
  ElevenRUP.step113551 (p 2707) (p 3434) (p 3631) (p 4424) (derived93500 p h) (derived96390 p h)

theorem derived113557 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3527) ∨ (p 3434) ∨ (¬ p 3945) :=
  ElevenRUP.step113557 (p 2707) (p 3434) (p 3527) (p 3945) (p 4424) (h 27819) (derived96390 p h)

theorem derived113560 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 2132) ∨ (p 2901) ∨ (¬ p 3571) :=
  ElevenRUP.step113560 (p 2132) (p 2707) (p 2901) (p 3425) (p 3571) (p 4424) (derived107323 p h) (derived96390 p h)

theorem derived113561 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 2264) ∨ (p 2696) ∨ (¬ p 3527) :=
  ElevenRUP.step113561 (p 2264) (p 2696) (p 2707) (p 3425) (p 3527) (p 4424) (derived93475 p h) (derived96390 p h)

theorem derived113563 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2717) ∨ (p 3399) ∨ (p 2459) ∨ (¬ p 2608) :=
  ElevenRUP.step113563 (p 2459) (p 2608) (p 2707) (p 2717) (p 3399) (p 4424) (derived93488 p h) (derived96390 p h)

theorem derived113564 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3201) ∨ (¬ p 2608) ∨ (p 3399) ∨ (¬ p 3367) :=
  ElevenRUP.step113564 (p 2608) (p 2707) (p 3201) (p 3367) (p 3399) (p 4424) (derived107875 p h) (derived96390 p h)

theorem derived113568 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 4400) ∨ (p 3425) ∨ (p 2774) ∨ (¬ p 2737) ∨ (¬ p 4842) :=
  ElevenRUP.step113568 (p 2707) (p 2737) (p 2774) (p 3425) (p 4400) (p 4424) (p 4842) (derived86404 p h) (derived96390 p h)

theorem derived113569 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 4400) ∨ (p 3425) ∨ (¬ p 2737) ∨ (p 2598) :=
  ElevenRUP.step113569 (p 2598) (p 2707) (p 2737) (p 3425) (p 4400) (p 4424) (p 4749) (derived105432 p h) (derived90138 p h) (derived96390 p h)

theorem derived113581 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (p 2427) ∨ (p 3367) ∨ (p 2177) ∨ (p 2850) ∨ (¬ p 3527) :=
  ElevenRUP.step113581 (p 2122) (p 2177) (p 2427) (p 2707) (p 2774) (p 2850) (p 3367) (p 3527) (p 4424) (derived111351 p h) (derived96390 p h)

theorem derived113584 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3363) ∨ (p 2427) ∨ (p 2177) ∨ (p 3367) ∨ (¬ p 3527) ∨ (p 3425) ∨ (p 2230) :=
  ElevenRUP.step113584 (p 2177) (p 2230) (p 2427) (p 2707) (p 3363) (p 3367) (p 3425) (p 3527) (p 4424) (p 4559) (derived105701 p h) (derived75593 p h) (derived96390 p h)

theorem derived113585 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2881) ∨ (p 2331) ∨ (p 2737) ∨ (p 2295) ∨ (p 3425) ∨ (¬ p 3361) ∨ (¬ p 3527) :=
  ElevenRUP.step113585 (p 2295) (p 2331) (p 2707) (p 2737) (p 2881) (p 3361) (p 3425) (p 3527) (p 4424) (p 4556) (derived105399 p h) (derived85066 p h) (derived96390 p h)

theorem derived113587 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 3527) ∨ (¬ p 2143) ∨ (p 2911) ∨ (p 2156) ∨ (p 2274) ∨ (p 3425) ∨ (p 2839) :=
  ElevenRUP.step113587 (p 2143) (p 2156) (p 2274) (p 2707) (p 2839) (p 2911) (p 3425) (p 3527) (p 4276) (p 4424) (derived105516 p h) (derived85138 p h) (derived96390 p h)

theorem derived113588 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2437) ∨ (¬ p 3527) ∨ (p 2651) ∨ (p 2737) ∨ (p 2177) ∨ (¬ p 3361) ∨ (p 3425) :=
  ElevenRUP.step113588 (p 2177) (p 2437) (p 2651) (p 2707) (p 2737) (p 3361) (p 3425) (p 3527) (p 4424) (p 4712) (derived105422 p h) (derived93479 p h) (derived96390 p h)

theorem derived113590 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3425) ∨ (p 3367) ∨ (¬ p 3527) ∨ (p 3564) ∨ (¬ p 2459) ∨ (¬ p 3363) ∨ (p 2573) :=
  ElevenRUP.step113590 (p 2459) (p 2573) (p 2707) (p 3363) (p 3367) (p 3425) (p 3527) (p 3564) (p 4424) (p 4604) (derived106293 p h) (derived93481 p h) (derived96390 p h)

theorem derived113591 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3323) ∨ (¬ p 2459) ∨ (p 2331) ∨ (p 2737) ∨ (¬ p 3527) ∨ (p 3425) ∨ (¬ p 3361) :=
  ElevenRUP.step113591 (p 2331) (p 2459) (p 2707) (p 2737) (p 3323) (p 3361) (p 3425) (p 3527) (p 4424) (p 4604) (derived106293 p h) (derived93493 p h) (derived96390 p h)

theorem derived113592 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3434) ∨ (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 2363) ∨ (¬ p 2608) ∨ (p 3399) ∨ (¬ p 3519) :=
  ElevenRUP.step113592 (p 2352) (p 2363) (p 2573) (p 2608) (p 2707) (p 3399) (p 3434) (p 3519) (p 4376) (p 4424) (p 4669) (derived106320 p h) (derived105415 p h) (derived76816 p h) (derived96390 p h)

theorem derived113596 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2668) ∨ (p 3399) ∨ (p 3434) ∨ (¬ p 2363) ∨ (¬ p 2608) :=
  ElevenRUP.step113596 (p 2246) (p 2331) (p 2363) (p 2608) (p 2668) (p 2707) (p 2744) (p 3399) (p 3434) (p 4424) (p 4669) (derived106503 p h) (derived105415 p h) (derived93476 p h) (derived96390 p h)

theorem derived113599 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2573) ∨ (¬ p 3519) ∨ (¬ p 2396) ∨ (¬ p 2608) ∨ (¬ p 2553) ∨ (p 2717) ∨ (p 3399) :=
  ElevenRUP.step113599 (p 2396) (p 2553) (p 2573) (p 2608) (p 2707) (p 2717) (p 3399) (p 3519) (p 4376) (p 4424) (p 4668) (derived105414 p h) (derived106320 p h) (derived93498 p h) (derived96390 p h)

theorem derived113602 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 2573) ∨ (¬ p 3343) ∨ (p 3016) ∨ (p 3399) ∨ (p 3434) ∨ (¬ p 2663) ∨ (¬ p 2246) ∨ (¬ p 2608) :=
  ElevenRUP.step113602 (p 2246) (p 2573) (p 2608) (p 2663) (p 2707) (p 2744) (p 3016) (p 3343) (p 3399) (p 3434) (p 4424) (p 4638) (derived106503 p h) (derived105409 p h) (derived93495 p h) (derived96390 p h)

theorem derived113603 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (¬ p 4777) ∨ (p 3399) ∨ (¬ p 2427) ∨ (p 2264) ∨ (¬ p 3246) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 2230) :=
  ElevenRUP.step113603 (p 2230) (p 2264) (p 2427) (p 2608) (p 2707) (p 3246) (p 3399) (p 3519) (p 4376) (p 4424) (p 4668) (p 4777) (derived105414 p h) (derived106320 p h) (derived95755 p h) (derived96390 p h)

theorem derived113608 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3319) ∨ (¬ p 3917) :=
  ElevenRUP.step113608 (p 2829) (p 3319) (p 3917) (p 3918) (h 5807) (derived96376 p h)

theorem derived113609 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3309) ∨ (p 2122) :=
  ElevenRUP.step113609 (p 2122) (p 2829) (p 3309) (p 3918) (h 6880) (derived96376 p h)

theorem derived113611 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 4329) ∨ (p 4435) :=
  ElevenRUP.step113611 (p 2829) (p 3918) (p 4329) (p 4435) (h 31405) (derived96376 p h)

theorem derived113612 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2774) ∨ (p 3093) ∨ (¬ p 3589) :=
  ElevenRUP.step113612 (p 2774) (p 2829) (p 3093) (p 3589) (p 3918) (derived81777 p h) (derived96376 p h)

theorem derived113614 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 3367) ∨ (¬ p 2608) ∨ (p 3093) :=
  ElevenRUP.step113614 (p 2608) (p 2829) (p 3093) (p 3367) (p 3918) (p 5221) (derived105796 p h) (derived93394 p h) (derived96376 p h)

end ElevenLogic
