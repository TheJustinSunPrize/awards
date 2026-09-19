import SunPrize.Certificate.Derived022
import SunPrize.Certificate.Logic023
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived65213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3591) ∨ (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 3923) ∨ (¬ p 4433) :=
  ElevenRUP.step65213 (p 2027) (p 2098) (p 2241) (p 2750) (p 2753) (p 3591) (p 3609) (p 3692) (p 3923) (p 4433) (derived40810 p h) (h 40726)

theorem derived65214 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3591) ∨ (¬ p 3641) ∨ (¬ p 4026) ∨ (¬ p 4604) :=
  ElevenRUP.step65214 (p 2027) (p 2241) (p 2528) (p 2598) (p 2750) (p 2753) (p 3591) (p 3641) (p 4026) (p 4604) (derived40810 p h) (h 40728)

theorem derived65215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3105) ∨ (¬ p 3680) ∨ (¬ p 4366) ∨ (¬ p 4442) ∨ (¬ p 4831) :=
  ElevenRUP.step65215 (p 2027) (p 2132) (p 2241) (p 2750) (p 2753) (p 3105) (p 3680) (p 4366) (p 4442) (p 4831) (derived40810 p h) (h 40729)

theorem derived65216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2284) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3641) ∨ (¬ p 3646) ∨ (¬ p 4033) ∨ (¬ p 4208) ∨ (¬ p 4604) :=
  ElevenRUP.step65216 (p 2027) (p 2145) (p 2284) (p 2528) (p 2598) (p 3641) (p 3646) (p 4033) (p 4208) (p 4604) (derived40810 p h) (h 40730)

theorem derived65217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3644) ∨ (¬ p 4403) ∨ (¬ p 4443) ∨ (¬ p 5118) ∨ (¬ p 5590) :=
  ElevenRUP.step65217 (p 2027) (p 2417) (p 3644) (p 4403) (p 4443) (p 5118) (p 5590) (derived40810 p h) (h 40731)

theorem derived65219 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 3097) ∨ (¬ p 3553) ∨ (¬ p 3631) ∨ (¬ p 4107) :=
  ElevenRUP.step65219 (p 1990) (p 2027) (p 2633) (p 3032) (p 3097) (p 3553) (p 3631) (p 4107) (h 2150) (derived40810 p h) (derived40879 p h) (h 40734)

theorem derived65221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2252) ∨ (¬ p 2459) ∨ (¬ p 2750) ∨ (¬ p 3172) ∨ (¬ p 3519) ∨ (¬ p 3541) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 4118) ∨ (¬ p 4420) :=
  ElevenRUP.step65221 (p 2027) (p 2230) (p 2252) (p 2459) (p 2750) (p 3172) (p 3519) (p 3541) (p 3641) (p 3684) (p 4118) (p 4420) (derived40810 p h) (h 40738)

theorem derived65222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 3324) ∨ (¬ p 3519) ∨ (¬ p 3541) ∨ (¬ p 3591) ∨ (¬ p 3641) ∨ (¬ p 3684) ∨ (¬ p 4319) ∨ (¬ p 4596) :=
  ElevenRUP.step65222 (p 2027) (p 2230) (p 2241) (p 2750) (p 3324) (p 3519) (p 3541) (p 3591) (p 3641) (p 3684) (p 4319) (p 4596) (derived40810 p h) (h 40739)

theorem derived65225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 2476) ∨ (¬ p 4434) :=
  ElevenRUP.step65225 (p 2027) (p 2230) (p 2373) (p 2476) (p 4434) (derived40810 p h) (h 40742)

theorem derived65227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3548) ∨ (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 5206) :=
  ElevenRUP.step65227 (p 1977) (p 2027) (p 2241) (p 2633) (p 3548) (p 3631) (p 3821) (p 5206) (h 2137) (derived40810 p h) (derived40879 p h) (h 40744)

theorem derived65228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2373) ∨ (¬ p 3551) ∨ (¬ p 4210) ∨ (¬ p 4902) ∨ (¬ p 5206) :=
  ElevenRUP.step65228 (p 2027) (p 2210) (p 2373) (p 3551) (p 4210) (p 4902) (p 5206) (derived40810 p h) (h 40745)

theorem derived65229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3516) ∨ (¬ p 3551) ∨ (¬ p 3692) ∨ (¬ p 4443) ∨ (¬ p 4902) :=
  ElevenRUP.step65229 (p 2027) (p 3516) (p 3551) (p 3692) (p 4443) (p 4902) (derived40810 p h) (h 40746)

theorem derived65230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2504) ∨ (¬ p 2750) ∨ (¬ p 3093) ∨ (¬ p 3414) ∨ (¬ p 3888) ∨ (¬ p 3947) ∨ (¬ p 3954) ∨ (¬ p 4381) ∨ (¬ p 5250) :=
  ElevenRUP.step65230 (p 2027) (p 2252) (p 2504) (p 2750) (p 3093) (p 3414) (p 3888) (p 3947) (p 3954) (p 4381) (p 5250) (derived40810 p h) (h 40747)

theorem derived65231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2252) ∨ (¬ p 2459) ∨ (¬ p 2750) ∨ (¬ p 3172) ∨ (¬ p 3954) ∨ (¬ p 4118) ∨ (¬ p 4902) :=
  ElevenRUP.step65231 (p 2027) (p 2166) (p 2210) (p 2252) (p 2459) (p 2750) (p 3172) (p 3954) (p 4118) (p 4902) (derived40810 p h) (h 40748)

theorem derived65233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2963) ∨ (¬ p 3266) ∨ (¬ p 3568) ∨ (¬ p 3609) ∨ (¬ p 4260) ∨ (¬ p 4789) ∨ (¬ p 4831) :=
  ElevenRUP.step65233 (p 2027) (p 2098) (p 2963) (p 3266) (p 3568) (p 3609) (p 4260) (p 4789) (p 4831) (derived40810 p h) (h 40750)

theorem derived65234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3097) ∨ (¬ p 3619) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3670) ∨ (¬ p 4107) ∨ (¬ p 4444) ∨ (¬ p 4669) ∨ (¬ p 4877) :=
  ElevenRUP.step65234 (p 2027) (p 2753) (p 3097) (p 3619) (p 3645) (p 3646) (p 3670) (p 4107) (p 4444) (p 4669) (p 4877) (derived40810 p h) (h 40751)

theorem derived65235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2963) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3568) ∨ (¬ p 3874) ∨ (¬ p 4107) ∨ (¬ p 4638) ∨ (¬ p 4789) :=
  ElevenRUP.step65235 (p 2027) (p 2470) (p 2963) (p 3333) (p 3362) (p 3568) (p 3874) (p 4107) (p 4638) (p 4789) (derived40810 p h) (h 40752)

theorem derived65236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3548) ∨ (¬ p 3631) ∨ (¬ p 4444) :=
  ElevenRUP.step65236 (p 1982) (p 2027) (p 2633) (p 2761) (p 3548) (p 3631) (p 4444) (h 2142) (derived40810 p h) (derived40879 p h) (h 40753)

theorem derived65240 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3516) ∨ (¬ p 4322) ∨ (¬ p 4402) ∨ (¬ p 4990) :=
  ElevenRUP.step65240 (p 2027) (p 2761) (p 3516) (p 4322) (p 4402) (p 4990) (derived40810 p h) (h 40757)

theorem derived65241 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3570) ∨ (¬ p 3646) ∨ (¬ p 4320) :=
  ElevenRUP.step65241 (p 1978) (p 2027) (p 2284) (p 2633) (p 3570) (p 3646) (p 4320) (h 2138) (derived40810 p h) (derived40879 p h) (h 40758)

theorem derived65242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2284) ∨ (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 3471) ∨ (¬ p 3646) ∨ (¬ p 4208) ∨ (¬ p 5059) :=
  ElevenRUP.step65242 (p 2027) (p 2145) (p 2284) (p 2459) (p 2717) (p 3471) (p 3646) (p 4208) (p 5059) (derived40810 p h) (h 40762)

theorem derived65243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3292) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3461) ∨ (¬ p 3876) ∨ (¬ p 4789) ∨ (¬ p 5284) ∨ (¬ p 5322) :=
  ElevenRUP.step65243 (p 2027) (p 3292) (p 3333) (p 3362) (p 3389) (p 3461) (p 3876) (p 4789) (p 5284) (p 5322) (derived40810 p h) (h 40763)

theorem derived65244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2963) ∨ (¬ p 3471) ∨ (¬ p 3941) ∨ (¬ p 4037) ∨ (¬ p 4191) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step65244 (p 2027) (p 2717) (p 2963) (p 3471) (p 3941) (p 4037) (p 4191) (p 4789) (p 5119) (derived40810 p h) (h 40764)

theorem derived65246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2573) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3548) ∨ (¬ p 3584) ∨ (¬ p 4366) ∨ (¬ p 4451) ∨ (¬ p 4668) :=
  ElevenRUP.step65246 (p 2027) (p 2241) (p 2573) (p 2750) (p 2753) (p 3333) (p 3362) (p 3548) (p 3584) (p 4366) (p 4451) (p 4668) (derived40810 p h) (h 40766)

theorem derived65247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2363) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3555) ∨ (¬ p 4363) ∨ (¬ p 5059) :=
  ElevenRUP.step65247 (p 2027) (p 2241) (p 2363) (p 2750) (p 2753) (p 2774) (p 2819) (p 3555) (p 4363) (p 5059) (derived40810 p h) (h 40767)

theorem derived65248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3362) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4444) ∨ (¬ p 4669) :=
  ElevenRUP.step65248 (p 2027) (p 2241) (p 2750) (p 2753) (p 3276) (p 3355) (p 3362) (p 3817) (p 4366) (p 4444) (p 4669) (derived40810 p h) (h 40768)

theorem derived65249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3707) ∨ (¬ p 3923) ∨ (¬ p 4025) ∨ (¬ p 4191) ∨ (¬ p 4501) ∨ (¬ p 5153) :=
  ElevenRUP.step65249 (p 2027) (p 3707) (p 3923) (p 4025) (p 4191) (p 4501) (p 5153) (derived40810 p h) (h 40769)

theorem derived65253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2476) ∨ (¬ p 2518) ∨ (¬ p 2750) ∨ (¬ p 3541) ∨ (¬ p 4108) :=
  ElevenRUP.step65253 (p 2027) (p 2241) (p 2476) (p 2518) (p 2750) (p 3541) (p 4108) (derived40810 p h) (h 40774)

theorem derived65255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2952) ∨ (¬ p 3690) ∨ (¬ p 4320) ∨ (¬ p 4669) ∨ (¬ p 4789) :=
  ElevenRUP.step65255 (p 2027) (p 2363) (p 2774) (p 2819) (p 2952) (p 3690) (p 4320) (p 4669) (p 4789) (derived40810 p h) (h 40776)

theorem derived65256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 2901) ∨ (¬ p 3556) ∨ (¬ p 3645) ∨ (¬ p 4208) ∨ (¬ p 4877) ∨ (¬ p 5059) :=
  ElevenRUP.step65256 (p 2027) (p 2363) (p 2753) (p 2774) (p 2819) (p 2901) (p 3556) (p 3645) (p 4208) (p 4877) (p 5059) (derived40810 p h) (h 40777)

theorem derived65259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 4320) ∨ (¬ p 4789) ∨ (¬ p 4831) ∨ (¬ p 5660) :=
  ElevenRUP.step65259 (p 2027) (p 2598) (p 2952) (p 3276) (p 3333) (p 4320) (p 4789) (p 4831) (p 5660) (derived40810 p h) (h 40781)

theorem derived65260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2963) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3568) ∨ (¬ p 4260) ∨ (¬ p 4789) ∨ (¬ p 4831) :=
  ElevenRUP.step65260 (p 2027) (p 2598) (p 2963) (p 3276) (p 3333) (p 3568) (p 4260) (p 4789) (p 4831) (derived40810 p h) (h 40782)

theorem derived65262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3449) ∨ (¬ p 3609) ∨ (¬ p 3954) ∨ (¬ p 5315) :=
  ElevenRUP.step65262 (p 2007) (p 2027) (p 2114) (p 2534) (p 3449) (p 3609) (p 3954) (p 5315) (h 2167) (derived40810 p h) (derived40864 p h) (h 40787)

theorem derived65263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2950) ∨ (¬ p 3201) ∨ (¬ p 3646) ∨ (¬ p 3951) ∨ (¬ p 4208) ∨ (¬ p 4789) :=
  ElevenRUP.step65263 (p 2027) (p 2284) (p 2417) (p 2598) (p 2950) (p 3201) (p 3646) (p 3951) (p 4208) (p 4789) (derived40810 p h) (h 40788)

theorem derived65265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3641) ∨ (¬ p 3860) ∨ (¬ p 5118) ∨ (¬ p 5693) :=
  ElevenRUP.step65265 (p 2027) (p 2241) (p 2528) (p 2598) (p 2750) (p 2753) (p 3641) (p 3860) (p 5118) (p 5693) (derived40810 p h) (h 40790)

theorem derived65266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3324) ∨ (¬ p 3461) ∨ (¬ p 4444) :=
  ElevenRUP.step65266 (p 1982) (p 2027) (p 2169) (p 3323) (p 3324) (p 3461) (p 4444) (h 2142) (derived40810 p h) (derived40866 p h) (h 40791)

theorem derived65267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2417) ∨ (¬ p 2750) ∨ (¬ p 2933) ∨ (¬ p 2952) ∨ (¬ p 3399) ∨ (¬ p 3570) ∨ (¬ p 3954) ∨ (¬ p 4320) ∨ (¬ p 4668) :=
  ElevenRUP.step65267 (p 2027) (p 2252) (p 2417) (p 2750) (p 2933) (p 2952) (p 3399) (p 3570) (p 3954) (p 4320) (p 4668) (derived40810 p h) (h 40792)

theorem derived65269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3452) ∨ (¬ p 3574) ∨ (¬ p 3956) ∨ (¬ p 4116) :=
  ElevenRUP.step65269 (p 1977) (p 2027) (p 2169) (p 2241) (p 3452) (p 3574) (p 3956) (p 4116) (h 2137) (derived40810 p h) (derived40866 p h) (h 40794)

theorem derived65270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3555) ∨ (¬ p 4363) ∨ (¬ p 5059) :=
  ElevenRUP.step65270 (p 2027) (p 2241) (p 2459) (p 2717) (p 2750) (p 2753) (p 3471) (p 3555) (p 4363) (p 5059) (derived40810 p h) (h 40799)

theorem derived65271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2241) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3032) ∨ (¬ p 3146) ∨ (¬ p 3947) ∨ (¬ p 4366) ∨ (¬ p 4669) :=
  ElevenRUP.step65271 (p 2027) (p 2132) (p 2241) (p 2619) (p 2750) (p 2753) (p 3032) (p 3146) (p 3947) (p 4366) (p 4669) (derived40810 p h) (h 40800)

theorem derived65274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4425) :=
  ElevenRUP.step65274 (p 1977) (p 2027) (p 2241) (p 2764) (p 3193) (p 3452) (p 4425) (h 2137) (derived40810 p h) (derived40882 p h) (h 40803)

theorem derived65275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2363) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3032) ∨ (¬ p 3947) ∨ (¬ p 4366) ∨ (¬ p 4669) :=
  ElevenRUP.step65275 (p 2027) (p 2241) (p 2363) (p 2750) (p 2753) (p 2774) (p 2819) (p 3032) (p 3947) (p 4366) (p 4669) (derived40810 p h) (h 40804)

theorem derived65277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3229) ∨ (¬ p 3452) ∨ (¬ p 3830) :=
  ElevenRUP.step65277 (p 2027) (p 3193) (p 3229) (p 3452) (p 3830) (derived40810 p h) (h 40806)

theorem derived65290 (p : Nat → Prop) (h : Inputs p) :
    (p 4265) :=
  ElevenRUP.step65290 (p 1874) (p 1880) (p 4265) (h 6438) (h 6439) (h 2042)

theorem derived65291 (p : Nat → Prop) (h : Inputs p) :
    (p 4266) :=
  ElevenRUP.step65291 (p 4265) (p 4266) (derived65290 p h) (h 6456)

theorem derived65292 (p : Nat → Prop) (h : Inputs p) :
    (p 5736) :=
  ElevenRUP.step65292 (p 4266) (p 5736) (derived65291 p h) (h 10665)

theorem derived65293 (p : Nat → Prop) (h : Inputs p) :
    (p 6192) :=
  ElevenRUP.step65293 (p 5736) (p 6192) (derived65292 p h) (h 16420)

theorem derived65294 (p : Nat → Prop) (h : Inputs p) :
    (p 4246) :=
  ElevenRUP.step65294 (p 1862) (p 1868) (p 4246) (h 6380) (h 6381) (h 2029)

theorem derived65295 (p : Nat → Prop) (h : Inputs p) :
    (p 4247) :=
  ElevenRUP.step65295 (p 4246) (p 4247) (derived65294 p h) (h 6398)

theorem derived65296 (p : Nat → Prop) (h : Inputs p) :
    (p 5725) :=
  ElevenRUP.step65296 (p 4247) (p 5725) (derived65295 p h) (h 10540)

theorem derived65297 (p : Nat → Prop) (h : Inputs p) :
    (p 6189) :=
  ElevenRUP.step65297 (p 5725) (p 6189) (derived65296 p h) (h 16045)

theorem derived65298 (p : Nat → Prop) (h : Inputs p) :
    (p 4221) :=
  ElevenRUP.step65298 (p 1850) (p 1856) (p 4221) (h 6331) (h 6332) (h 2016)

theorem derived65299 (p : Nat → Prop) (h : Inputs p) :
    (p 4222) :=
  ElevenRUP.step65299 (p 4221) (p 4222) (derived65298 p h) (h 6349)

theorem derived65300 (p : Nat → Prop) (h : Inputs p) :
    (p 5713) :=
  ElevenRUP.step65300 (p 4222) (p 5713) (derived65299 p h) (h 10444)

theorem derived65301 (p : Nat → Prop) (h : Inputs p) :
    (p 6186) :=
  ElevenRUP.step65301 (p 5713) (p 6186) (derived65300 p h) (h 15780)

theorem derived65306 (p : Nat → Prop) (h : Inputs p) :
    (p 4174) :=
  ElevenRUP.step65306 (p 1826) (p 1832) (p 4174) (h 6238) (h 6239) (h 1990)

theorem derived65307 (p : Nat → Prop) (h : Inputs p) :
    (p 4175) :=
  ElevenRUP.step65307 (p 4174) (p 4175) (derived65306 p h) (h 6256)

theorem derived65308 (p : Nat → Prop) (h : Inputs p) :
    (p 5689) :=
  ElevenRUP.step65308 (p 4175) (p 5689) (derived65307 p h) (h 10237)

theorem derived65309 (p : Nat → Prop) (h : Inputs p) :
    (p 6180) :=
  ElevenRUP.step65309 (p 5689) (p 6180) (derived65308 p h) (h 15275)

theorem derived65310 (p : Nat → Prop) (h : Inputs p) :
    (p 4159) :=
  ElevenRUP.step65310 (p 1814) (p 1820) (p 4159) (h 6209) (h 6210) (h 1977)

theorem derived65311 (p : Nat → Prop) (h : Inputs p) :
    (p 4160) :=
  ElevenRUP.step65311 (p 4159) (p 4160) (derived65310 p h) (h 6227)

theorem derived65312 (p : Nat → Prop) (h : Inputs p) :
    (p 5677) :=
  ElevenRUP.step65312 (p 4160) (p 5677) (derived65311 p h) (h 10201)

theorem derived65313 (p : Nat → Prop) (h : Inputs p) :
    (p 6177) :=
  ElevenRUP.step65313 (p 5677) (p 6177) (derived65312 p h) (h 15166)

theorem derived65314 (p : Nat → Prop) (h : Inputs p) :
    (p 4142) :=
  ElevenRUP.step65314 (p 1802) (p 1808) (p 4142) (h 6179) (h 6180) (h 1964)

theorem derived65315 (p : Nat → Prop) (h : Inputs p) :
    (p 4143) :=
  ElevenRUP.step65315 (p 4142) (p 4143) (derived65314 p h) (h 6197)

theorem derived65316 (p : Nat → Prop) (h : Inputs p) :
    (p 5668) :=
  ElevenRUP.step65316 (p 4143) (p 5668) (derived65315 p h) (h 10168)

theorem derived65317 (p : Nat → Prop) (h : Inputs p) :
    (p 6174) :=
  ElevenRUP.step65317 (p 5668) (p 6174) (derived65316 p h) (h 15095)

theorem derived65318 (p : Nat → Prop) (h : Inputs p) :
    (p 4122) :=
  ElevenRUP.step65318 (p 1790) (p 1796) (p 4122) (h 6152) (h 6153) (h 1951)

theorem derived65319 (p : Nat → Prop) (h : Inputs p) :
    (p 4123) :=
  ElevenRUP.step65319 (p 4122) (p 4123) (derived65318 p h) (h 6170)

theorem derived65320 (p : Nat → Prop) (h : Inputs p) :
    (p 5658) :=
  ElevenRUP.step65320 (p 4123) (p 5658) (derived65319 p h) (h 10132)

theorem derived65321 (p : Nat → Prop) (h : Inputs p) :
    (p 6171) :=
  ElevenRUP.step65321 (p 5658) (p 6171) (derived65320 p h) (h 15015)

theorem derived65322 (p : Nat → Prop) (h : Inputs p) :
    (p 4068) :=
  ElevenRUP.step65322 (p 1766) (p 1772) (p 4068) (h 6053) (h 6054) (h 1925)

theorem derived65323 (p : Nat → Prop) (h : Inputs p) :
    (p 4069) :=
  ElevenRUP.step65323 (p 4068) (p 4069) (derived65322 p h) (h 6071)

theorem derived65324 (p : Nat → Prop) (h : Inputs p) :
    (p 5642) :=
  ElevenRUP.step65324 (p 4069) (p 5642) (derived65323 p h) (h 10014)

theorem derived65325 (p : Nat → Prop) (h : Inputs p) :
    (p 6168) :=
  ElevenRUP.step65325 (p 5642) (p 6168) (derived65324 p h) (h 14764)

theorem derived65326 (p : Nat → Prop) (h : Inputs p) :
    (p 4056) :=
  ElevenRUP.step65326 (p 1754) (p 1760) (p 4056) (h 6031) (h 6032) (h 1912)

theorem derived65327 (p : Nat → Prop) (h : Inputs p) :
    (p 4057) :=
  ElevenRUP.step65327 (p 4056) (p 4057) (derived65326 p h) (h 6049)

theorem derived65328 (p : Nat → Prop) (h : Inputs p) :
    (p 5631) :=
  ElevenRUP.step65328 (p 4057) (p 5631) (derived65327 p h) (h 9987)

theorem derived65329 (p : Nat → Prop) (h : Inputs p) :
    (p 6165) :=
  ElevenRUP.step65329 (p 5631) (p 6165) (derived65328 p h) (h 14732)

theorem derived65330 (p : Nat → Prop) (h : Inputs p) :
    (p 4046) :=
  ElevenRUP.step65330 (p 1742) (p 1748) (p 4046) (h 6011) (h 6012) (h 1899)

theorem derived65331 (p : Nat → Prop) (h : Inputs p) :
    (p 4047) :=
  ElevenRUP.step65331 (p 4046) (p 4047) (derived65330 p h) (h 6029)

theorem derived65332 (p : Nat → Prop) (h : Inputs p) :
    (p 5620) :=
  ElevenRUP.step65332 (p 4047) (p 5620) (derived65331 p h) (h 9970)

theorem derived65333 (p : Nat → Prop) (h : Inputs p) :
    (p 6162) :=
  ElevenRUP.step65333 (p 5620) (p 6162) (derived65332 p h) (h 14713)

theorem derived65334 (p : Nat → Prop) (h : Inputs p) :
    (p 4012) :=
  ElevenRUP.step65334 (p 1730) (p 1736) (p 4012) (h 5968) (h 5969) (h 1886)

theorem derived65335 (p : Nat → Prop) (h : Inputs p) :
    (p 4013) :=
  ElevenRUP.step65335 (p 4012) (p 4013) (derived65334 p h) (h 5986)

theorem derived65336 (p : Nat → Prop) (h : Inputs p) :
    (p 5608) :=
  ElevenRUP.step65336 (p 4013) (p 5608) (derived65335 p h) (h 9894)

theorem derived65338 (p : Nat → Prop) (h : Inputs p) :
    (p 4002) :=
  ElevenRUP.step65338 (p 1718) (p 1724) (p 4002) (h 5948) (h 5949) (h 1873)

theorem derived65339 (p : Nat → Prop) (h : Inputs p) :
    (p 4003) :=
  ElevenRUP.step65339 (p 4002) (p 4003) (derived65338 p h) (h 5966)

theorem derived65340 (p : Nat → Prop) (h : Inputs p) :
    (p 5596) :=
  ElevenRUP.step65340 (p 4003) (p 5596) (derived65339 p h) (h 9877)

theorem derived65342 (p : Nat → Prop) (h : Inputs p) :
    (p 3991) :=
  ElevenRUP.step65342 (p 1706) (p 1712) (p 3991) (h 5925) (h 5926) (h 1860)

theorem derived65343 (p : Nat → Prop) (h : Inputs p) :
    (p 3992) :=
  ElevenRUP.step65343 (p 3991) (p 3992) (derived65342 p h) (h 5943)

theorem derived65344 (p : Nat → Prop) (h : Inputs p) :
    (p 5588) :=
  ElevenRUP.step65344 (p 3992) (p 5588) (derived65343 p h) (h 9851)

theorem derived65345 (p : Nat → Prop) (h : Inputs p) :
    (p 6153) :=
  ElevenRUP.step65345 (p 5588) (p 6153) (derived65344 p h) (h 14487)

theorem derived65346 (p : Nat → Prop) (h : Inputs p) :
    (p 3972) :=
  ElevenRUP.step65346 (p 1694) (p 1700) (p 3972) (h 5893) (h 5894) (h 1847)

theorem derived65347 (p : Nat → Prop) (h : Inputs p) :
    (p 3973) :=
  ElevenRUP.step65347 (p 3972) (p 3973) (derived65346 p h) (h 5911)

theorem derived65348 (p : Nat → Prop) (h : Inputs p) :
    (p 5576) :=
  ElevenRUP.step65348 (p 3973) (p 5576) (derived65347 p h) (h 9821)

theorem derived65349 (p : Nat → Prop) (h : Inputs p) :
    (p 6150) :=
  ElevenRUP.step65349 (p 5576) (p 6150) (derived65348 p h) (h 14423)

theorem derived65350 (p : Nat → Prop) (h : Inputs p) :
    (p 3962) :=
  ElevenRUP.step65350 (p 1682) (p 1688) (p 3962) (h 5873) (h 5874) (h 1834)

theorem derived65351 (p : Nat → Prop) (h : Inputs p) :
    (p 3963) :=
  ElevenRUP.step65351 (p 3962) (p 3963) (derived65350 p h) (h 5891)

theorem derived65352 (p : Nat → Prop) (h : Inputs p) :
    (p 5566) :=
  ElevenRUP.step65352 (p 3963) (p 5566) (derived65351 p h) (h 9804)

theorem derived65353 (p : Nat → Prop) (h : Inputs p) :
    (p 6147) :=
  ElevenRUP.step65353 (p 5566) (p 6147) (derived65352 p h) (h 14405)

theorem derived65354 (p : Nat → Prop) (h : Inputs p) :
    (p 3934) :=
  ElevenRUP.step65354 (p 1670) (p 1676) (p 3934) (h 5835) (h 5836) (h 1821)

theorem derived65355 (p : Nat → Prop) (h : Inputs p) :
    (p 3935) :=
  ElevenRUP.step65355 (p 3934) (p 3935) (derived65354 p h) (h 5853)

theorem derived65356 (p : Nat → Prop) (h : Inputs p) :
    (p 5554) :=
  ElevenRUP.step65356 (p 3935) (p 5554) (derived65355 p h) (h 9734)

theorem derived65357 (p : Nat → Prop) (h : Inputs p) :
    (p 6144) :=
  ElevenRUP.step65357 (p 5554) (p 6144) (derived65356 p h) (h 14279)

theorem derived65358 (p : Nat → Prop) (h : Inputs p) :
    (p 3924) :=
  ElevenRUP.step65358 (p 1658) (p 1664) (p 3924) (h 5815) (h 5816) (h 1808)

theorem derived65359 (p : Nat → Prop) (h : Inputs p) :
    (p 3925) :=
  ElevenRUP.step65359 (p 3924) (p 3925) (derived65358 p h) (h 5833)

theorem derived65360 (p : Nat → Prop) (h : Inputs p) :
    (p 5543) :=
  ElevenRUP.step65360 (p 3925) (p 5543) (derived65359 p h) (h 9716)

theorem derived65362 (p : Nat → Prop) (h : Inputs p) :
    (p 3907) :=
  ElevenRUP.step65362 (p 1646) (p 1652) (p 3907) (h 5787) (h 5788) (h 1795)

theorem derived65363 (p : Nat → Prop) (h : Inputs p) :
    (p 3908) :=
  ElevenRUP.step65363 (p 3907) (p 3908) (derived65362 p h) (h 5805)

theorem derived65364 (p : Nat → Prop) (h : Inputs p) :
    (p 5532) :=
  ElevenRUP.step65364 (p 3908) (p 5532) (derived65363 p h) (h 9674)

theorem derived65365 (p : Nat → Prop) (h : Inputs p) :
    (p 6138) :=
  ElevenRUP.step65365 (p 5532) (p 6138) (derived65364 p h) (h 14180)

theorem derived65366 (p : Nat → Prop) (h : Inputs p) :
    (p 3894) :=
  ElevenRUP.step65366 (p 1634) (p 1640) (p 3894) (h 5764) (h 5765) (h 1782)

theorem derived65367 (p : Nat → Prop) (h : Inputs p) :
    (p 3895) :=
  ElevenRUP.step65367 (p 3894) (p 3895) (derived65366 p h) (h 5782)

theorem derived65368 (p : Nat → Prop) (h : Inputs p) :
    (p 5521) :=
  ElevenRUP.step65368 (p 3895) (p 5521) (derived65367 p h) (h 9652)

theorem derived65369 (p : Nat → Prop) (h : Inputs p) :
    (p 6135) :=
  ElevenRUP.step65369 (p 5521) (p 6135) (derived65368 p h) (h 14145)

theorem derived65370 (p : Nat → Prop) (h : Inputs p) :
    (p 3881) :=
  ElevenRUP.step65370 (p 1622) (p 1628) (p 3881) (h 5741) (h 5742) (h 1769)

theorem derived65371 (p : Nat → Prop) (h : Inputs p) :
    (p 3882) :=
  ElevenRUP.step65371 (p 3881) (p 3882) (derived65370 p h) (h 5759)

theorem derived65372 (p : Nat → Prop) (h : Inputs p) :
    (p 5511) :=
  ElevenRUP.step65372 (p 3882) (p 5511) (derived65371 p h) (h 9635)

theorem derived65374 (p : Nat → Prop) (h : Inputs p) :
    (p 3861) :=
  ElevenRUP.step65374 (p 1610) (p 1616) (p 3861) (h 5708) (h 5709) (h 1756)

theorem derived65375 (p : Nat → Prop) (h : Inputs p) :
    (p 3862) :=
  ElevenRUP.step65375 (p 3861) (p 3862) (derived65374 p h) (h 5726)

theorem derived65376 (p : Nat → Prop) (h : Inputs p) :
    (p 5499) :=
  ElevenRUP.step65376 (p 3862) (p 5499) (derived65375 p h) (h 9596)

theorem derived65377 (p : Nat → Prop) (h : Inputs p) :
    (p 6129) :=
  ElevenRUP.step65377 (p 5499) (p 6129) (derived65376 p h) (h 14047)

theorem derived65378 (p : Nat → Prop) (h : Inputs p) :
    (p 3823) :=
  ElevenRUP.step65378 (p 1586) (p 1592) (p 3823) (h 5637) (h 5638) (h 1730)

theorem derived65379 (p : Nat → Prop) (h : Inputs p) :
    (p 3824) :=
  ElevenRUP.step65379 (p 3823) (p 3824) (derived65378 p h) (h 5655)

theorem derived65380 (p : Nat → Prop) (h : Inputs p) :
    (p 5484) :=
  ElevenRUP.step65380 (p 3824) (p 5484) (derived65379 p h) (h 9546)

theorem derived65381 (p : Nat → Prop) (h : Inputs p) :
    (p 6126) :=
  ElevenRUP.step65381 (p 5484) (p 6126) (derived65380 p h) (h 14020)

theorem derived65382 (p : Nat → Prop) (h : Inputs p) :
    (p 3784) :=
  ElevenRUP.step65382 (p 1562) (p 1568) (p 3784) (h 5563) (h 5564) (h 1704)

theorem derived65383 (p : Nat → Prop) (h : Inputs p) :
    (p 3785) :=
  ElevenRUP.step65383 (p 3784) (p 3785) (derived65382 p h) (h 5581)

theorem derived65384 (p : Nat → Prop) (h : Inputs p) :
    (p 5468) :=
  ElevenRUP.step65384 (p 3785) (p 5468) (derived65383 p h) (h 9494)

theorem derived65385 (p : Nat → Prop) (h : Inputs p) :
    (p 6123) :=
  ElevenRUP.step65385 (p 5468) (p 6123) (derived65384 p h) (h 13971)

theorem derived65386 (p : Nat → Prop) (h : Inputs p) :
    (p 3748) :=
  ElevenRUP.step65386 (p 1538) (p 1544) (p 3748) (h 5488) (h 5489) (h 1678)

theorem derived65387 (p : Nat → Prop) (h : Inputs p) :
    (p 3749) :=
  ElevenRUP.step65387 (p 3748) (p 3749) (derived65386 p h) (h 5506)

theorem derived65388 (p : Nat → Prop) (h : Inputs p) :
    (p 5451) :=
  ElevenRUP.step65388 (p 3749) (p 5451) (derived65387 p h) (h 9437)

theorem derived65389 (p : Nat → Prop) (h : Inputs p) :
    (p 6120) :=
  ElevenRUP.step65389 (p 5451) (p 6120) (derived65388 p h) (h 13928)

theorem derived65390 (p : Nat → Prop) (h : Inputs p) :
    (p 3730) :=
  ElevenRUP.step65390 (p 1526) (p 1532) (p 3730) (h 5462) (h 5463) (h 1665)

theorem derived65391 (p : Nat → Prop) (h : Inputs p) :
    (p 3731) :=
  ElevenRUP.step65391 (p 3730) (p 3731) (derived65390 p h) (h 5480)

theorem derived65392 (p : Nat → Prop) (h : Inputs p) :
    (p 5441) :=
  ElevenRUP.step65392 (p 3731) (p 5441) (derived65391 p h) (h 9405)

theorem derived65393 (p : Nat → Prop) (h : Inputs p) :
    (p 6117) :=
  ElevenRUP.step65393 (p 5441) (p 6117) (derived65392 p h) (h 13896)

theorem derived65394 (p : Nat → Prop) (h : Inputs p) :
    (p 3720) :=
  ElevenRUP.step65394 (p 1514) (p 1520) (p 3720) (h 5442) (h 5443) (h 1652)

theorem derived65395 (p : Nat → Prop) (h : Inputs p) :
    (p 3721) :=
  ElevenRUP.step65395 (p 3720) (p 3721) (derived65394 p h) (h 5460)

theorem derived65396 (p : Nat → Prop) (h : Inputs p) :
    (p 5429) :=
  ElevenRUP.step65396 (p 3721) (p 5429) (derived65395 p h) (h 9387)

theorem derived65398 (p : Nat → Prop) (h : Inputs p) :
    (p 3710) :=
  ElevenRUP.step65398 (p 1502) (p 1508) (p 3710) (h 5422) (h 5423) (h 1639)

theorem derived65399 (p : Nat → Prop) (h : Inputs p) :
    (p 3711) :=
  ElevenRUP.step65399 (p 3710) (p 3711) (derived65398 p h) (h 5440)

theorem derived65400 (p : Nat → Prop) (h : Inputs p) :
    (p 5417) :=
  ElevenRUP.step65400 (p 3711) (p 5417) (derived65399 p h) (h 9369)

theorem derived65401 (p : Nat → Prop) (h : Inputs p) :
    (p 6111) :=
  ElevenRUP.step65401 (p 5417) (p 6111) (derived65400 p h) (h 13862)

theorem derived65402 (p : Nat → Prop) (h : Inputs p) :
    (p 3700) :=
  ElevenRUP.step65402 (p 1490) (p 1496) (p 3700) (h 5402) (h 5403) (h 1626)

theorem derived65403 (p : Nat → Prop) (h : Inputs p) :
    (p 3701) :=
  ElevenRUP.step65403 (p 3700) (p 3701) (derived65402 p h) (h 5420)

theorem derived65404 (p : Nat → Prop) (h : Inputs p) :
    (p 5406) :=
  ElevenRUP.step65404 (p 3701) (p 5406) (derived65403 p h) (h 9352)

theorem derived65405 (p : Nat → Prop) (h : Inputs p) :
    (p 6108) :=
  ElevenRUP.step65405 (p 5406) (p 6108) (derived65404 p h) (h 13841)

theorem derived65406 (p : Nat → Prop) (h : Inputs p) :
    (p 3673) :=
  ElevenRUP.step65406 (p 1478) (p 1484) (p 3673) (h 5370) (h 5371) (h 1613)

theorem derived65407 (p : Nat → Prop) (h : Inputs p) :
    (p 3674) :=
  ElevenRUP.step65407 (p 3673) (p 3674) (derived65406 p h) (h 5388)

theorem derived65408 (p : Nat → Prop) (h : Inputs p) :
    (p 5395) :=
  ElevenRUP.step65408 (p 3674) (p 5395) (derived65407 p h) (h 9321)

theorem derived65409 (p : Nat → Prop) (h : Inputs p) :
    (p 6105) :=
  ElevenRUP.step65409 (p 5395) (p 6105) (derived65408 p h) (h 13797)

theorem derived65410 (p : Nat → Prop) (h : Inputs p) :
    (p 3663) :=
  ElevenRUP.step65410 (p 1466) (p 1472) (p 3663) (h 5350) (h 5351) (h 1600)

theorem derived65411 (p : Nat → Prop) (h : Inputs p) :
    (p 3664) :=
  ElevenRUP.step65411 (p 3663) (p 3664) (derived65410 p h) (h 5368)

theorem derived65412 (p : Nat → Prop) (h : Inputs p) :
    (p 5385) :=
  ElevenRUP.step65412 (p 3664) (p 5385) (derived65411 p h) (h 9304)

theorem derived65413 (p : Nat → Prop) (h : Inputs p) :
    (p 6102) :=
  ElevenRUP.step65413 (p 5385) (p 6102) (derived65412 p h) (h 13779)

theorem derived65414 (p : Nat → Prop) (h : Inputs p) :
    (p 3647) :=
  ElevenRUP.step65414 (p 1454) (p 1460) (p 3647) (h 5324) (h 5325) (h 1587)

theorem derived65415 (p : Nat → Prop) (h : Inputs p) :
    (p 3648) :=
  ElevenRUP.step65415 (p 3647) (p 3648) (derived65414 p h) (h 5342)

theorem derived65416 (p : Nat → Prop) (h : Inputs p) :
    (p 5376) :=
  ElevenRUP.step65416 (p 3648) (p 5376) (derived65415 p h) (h 9268)

theorem derived65417 (p : Nat → Prop) (h : Inputs p) :
    (p 6099) :=
  ElevenRUP.step65417 (p 5376) (p 6099) (derived65416 p h) (h 13743)

theorem derived65418 (p : Nat → Prop) (h : Inputs p) :
    (p 3634) :=
  ElevenRUP.step65418 (p 1442) (p 1448) (p 3634) (h 5302) (h 5303) (h 1574)

theorem derived65419 (p : Nat → Prop) (h : Inputs p) :
    (p 3635) :=
  ElevenRUP.step65419 (p 3634) (p 3635) (derived65418 p h) (h 5320)

theorem derived65420 (p : Nat → Prop) (h : Inputs p) :
    (p 5366) :=
  ElevenRUP.step65420 (p 3635) (p 5366) (derived65419 p h) (h 9248)

theorem derived65421 (p : Nat → Prop) (h : Inputs p) :
    (p 6096) :=
  ElevenRUP.step65421 (p 5366) (p 6096) (derived65420 p h) (h 13712)

theorem derived65422 (p : Nat → Prop) (h : Inputs p) :
    (p 3624) :=
  ElevenRUP.step65422 (p 1430) (p 1436) (p 3624) (h 5282) (h 5283) (h 1561)

theorem derived65423 (p : Nat → Prop) (h : Inputs p) :
    (p 3625) :=
  ElevenRUP.step65423 (p 3624) (p 3625) (derived65422 p h) (h 5300)

theorem derived65424 (p : Nat → Prop) (h : Inputs p) :
    (p 5355) :=
  ElevenRUP.step65424 (p 3625) (p 5355) (derived65423 p h) (h 9224)

theorem derived65425 (p : Nat → Prop) (h : Inputs p) :
    (p 6093) :=
  ElevenRUP.step65425 (p 5355) (p 6093) (derived65424 p h) (h 13682)

theorem derived65426 (p : Nat → Prop) (h : Inputs p) :
    (p 3612) :=
  ElevenRUP.step65426 (p 1418) (p 1424) (p 3612) (h 5258) (h 5259) (h 1548)

theorem derived65427 (p : Nat → Prop) (h : Inputs p) :
    (p 3613) :=
  ElevenRUP.step65427 (p 3612) (p 3613) (derived65426 p h) (h 5276)

theorem derived65428 (p : Nat → Prop) (h : Inputs p) :
    (p 5347) :=
  ElevenRUP.step65428 (p 3613) (p 5347) (derived65427 p h) (h 9205)

theorem derived65430 (p : Nat → Prop) (h : Inputs p) :
    (p 3602) :=
  ElevenRUP.step65430 (p 1406) (p 1412) (p 3602) (h 5238) (h 5239) (h 1535)

theorem derived65431 (p : Nat → Prop) (h : Inputs p) :
    (p 3603) :=
  ElevenRUP.step65431 (p 3602) (p 3603) (derived65430 p h) (h 5256)

theorem derived65432 (p : Nat → Prop) (h : Inputs p) :
    (p 5336) :=
  ElevenRUP.step65432 (p 3603) (p 5336) (derived65431 p h) (h 9188)

theorem derived65433 (p : Nat → Prop) (h : Inputs p) :
    (p 6087) :=
  ElevenRUP.step65433 (p 5336) (p 6087) (derived65432 p h) (h 13647)

theorem derived65434 (p : Nat → Prop) (h : Inputs p) :
    (p 3592) :=
  ElevenRUP.step65434 (p 1394) (p 1400) (p 3592) (h 5218) (h 5219) (h 1522)

theorem derived65435 (p : Nat → Prop) (h : Inputs p) :
    (p 3593) :=
  ElevenRUP.step65435 (p 3592) (p 3593) (derived65434 p h) (h 5236)

theorem derived65436 (p : Nat → Prop) (h : Inputs p) :
    (p 5326) :=
  ElevenRUP.step65436 (p 3593) (p 5326) (derived65435 p h) (h 9171)

theorem derived65437 (p : Nat → Prop) (h : Inputs p) :
    (p 6084) :=
  ElevenRUP.step65437 (p 5326) (p 6084) (derived65436 p h) (h 13630)

theorem derived65438 (p : Nat → Prop) (h : Inputs p) :
    (p 3557) :=
  ElevenRUP.step65438 (p 1382) (p 1388) (p 3557) (h 5175) (h 5176) (h 1509)

theorem derived65439 (p : Nat → Prop) (h : Inputs p) :
    (p 3558) :=
  ElevenRUP.step65439 (p 3557) (p 3558) (derived65438 p h) (h 5193)

theorem derived65440 (p : Nat → Prop) (h : Inputs p) :
    (p 5319) :=
  ElevenRUP.step65440 (p 3558) (p 5319) (derived65439 p h) (h 9115)

theorem derived65441 (p : Nat → Prop) (h : Inputs p) :
    (p 6081) :=
  ElevenRUP.step65441 (p 5319) (p 6081) (derived65440 p h) (h 13558)

theorem derived65442 (p : Nat → Prop) (h : Inputs p) :
    (p 3530) :=
  ElevenRUP.step65442 (p 1370) (p 1376) (p 3530) (h 5142) (h 5143) (h 1496)

theorem derived65443 (p : Nat → Prop) (h : Inputs p) :
    (p 3531) :=
  ElevenRUP.step65443 (p 3530) (p 3531) (derived65442 p h) (h 5160)

theorem derived65444 (p : Nat → Prop) (h : Inputs p) :
    (p 5310) :=
  ElevenRUP.step65444 (p 3531) (p 5310) (derived65443 p h) (h 9074)

theorem derived65445 (p : Nat → Prop) (h : Inputs p) :
    (p 6078) :=
  ElevenRUP.step65445 (p 5310) (p 6078) (derived65444 p h) (h 13518)

theorem derived65446 (p : Nat → Prop) (h : Inputs p) :
    (p 3520) :=
  ElevenRUP.step65446 (p 1358) (p 1364) (p 3520) (h 5122) (h 5123) (h 1483)

theorem derived65447 (p : Nat → Prop) (h : Inputs p) :
    (p 3521) :=
  ElevenRUP.step65447 (p 3520) (p 3521) (derived65446 p h) (h 5140)

theorem derived65448 (p : Nat → Prop) (h : Inputs p) :
    (p 5303) :=
  ElevenRUP.step65448 (p 3521) (p 5303) (derived65447 p h) (h 9051)

theorem derived65449 (p : Nat → Prop) (h : Inputs p) :
    (p 6075) :=
  ElevenRUP.step65449 (p 5303) (p 6075) (derived65448 p h) (h 13499)

theorem derived65450 (p : Nat → Prop) (h : Inputs p) :
    (p 3509) :=
  ElevenRUP.step65450 (p 1346) (p 1352) (p 3509) (h 5101) (h 5102) (h 1470)

theorem derived65451 (p : Nat → Prop) (h : Inputs p) :
    (p 3510) :=
  ElevenRUP.step65451 (p 3509) (p 3510) (derived65450 p h) (h 5119)

theorem derived65452 (p : Nat → Prop) (h : Inputs p) :
    (p 5292) :=
  ElevenRUP.step65452 (p 3510) (p 5292) (derived65451 p h) (h 9032)

theorem derived65453 (p : Nat → Prop) (h : Inputs p) :
    (p 6072) :=
  ElevenRUP.step65453 (p 5292) (p 6072) (derived65452 p h) (h 13481)

theorem derived65454 (p : Nat → Prop) (h : Inputs p) :
    (p 3499) :=
  ElevenRUP.step65454 (p 1334) (p 1340) (p 3499) (h 5081) (h 5082) (h 1457)

theorem derived65455 (p : Nat → Prop) (h : Inputs p) :
    (p 3500) :=
  ElevenRUP.step65455 (p 3499) (p 3500) (derived65454 p h) (h 5099)

theorem derived65456 (p : Nat → Prop) (h : Inputs p) :
    (p 5280) :=
  ElevenRUP.step65456 (p 3500) (p 5280) (derived65455 p h) (h 9015)

theorem derived65457 (p : Nat → Prop) (h : Inputs p) :
    (p 6069) :=
  ElevenRUP.step65457 (p 5280) (p 6069) (derived65456 p h) (h 13463)

theorem derived65458 (p : Nat → Prop) (h : Inputs p) :
    (p 3488) :=
  ElevenRUP.step65458 (p 1322) (p 1328) (p 3488) (h 5057) (h 5058) (h 1444)

theorem derived65459 (p : Nat → Prop) (h : Inputs p) :
    (p 3489) :=
  ElevenRUP.step65459 (p 3488) (p 3489) (derived65458 p h) (h 5075)

theorem derived65460 (p : Nat → Prop) (h : Inputs p) :
    (p 5272) :=
  ElevenRUP.step65460 (p 3489) (p 5272) (derived65459 p h) (h 8994)

theorem derived65461 (p : Nat → Prop) (h : Inputs p) :
    (p 6066) :=
  ElevenRUP.step65461 (p 5272) (p 6066) (derived65460 p h) (h 13438)

theorem derived65462 (p : Nat → Prop) (h : Inputs p) :
    (p 3476) :=
  ElevenRUP.step65462 (p 1310) (p 1316) (p 3476) (h 5035) (h 5036) (h 1431)

theorem derived65463 (p : Nat → Prop) (h : Inputs p) :
    (p 3477) :=
  ElevenRUP.step65463 (p 3476) (p 3477) (derived65462 p h) (h 5053)

theorem derived65464 (p : Nat → Prop) (h : Inputs p) :
    (p 5262) :=
  ElevenRUP.step65464 (p 3477) (p 5262) (derived65463 p h) (h 8975)

theorem derived65465 (p : Nat → Prop) (h : Inputs p) :
    (p 6063) :=
  ElevenRUP.step65465 (p 5262) (p 6063) (derived65464 p h) (h 13408)

theorem derived65466 (p : Nat → Prop) (h : Inputs p) :
    (p 3464) :=
  ElevenRUP.step65466 (p 1298) (p 1304) (p 3464) (h 5010) (h 5011) (h 1418)

theorem derived65467 (p : Nat → Prop) (h : Inputs p) :
    (p 3465) :=
  ElevenRUP.step65467 (p 3464) (p 3465) (derived65466 p h) (h 5028)

theorem derived65468 (p : Nat → Prop) (h : Inputs p) :
    (p 5255) :=
  ElevenRUP.step65468 (p 3465) (p 5255) (derived65467 p h) (h 8958)

theorem derived65469 (p : Nat → Prop) (h : Inputs p) :
    (p 6060) :=
  ElevenRUP.step65469 (p 5255) (p 6060) (derived65468 p h) (h 13388)

theorem derived65470 (p : Nat → Prop) (h : Inputs p) :
    (p 3454) :=
  ElevenRUP.step65470 (p 1286) (p 1292) (p 3454) (h 4990) (h 4991) (h 1405)

theorem derived65471 (p : Nat → Prop) (h : Inputs p) :
    (p 3455) :=
  ElevenRUP.step65471 (p 3454) (p 3455) (derived65470 p h) (h 5008)

theorem derived65472 (p : Nat → Prop) (h : Inputs p) :
    (p 5245) :=
  ElevenRUP.step65472 (p 3455) (p 5245) (derived65471 p h) (h 8941)

theorem derived65473 (p : Nat → Prop) (h : Inputs p) :
    (p 6057) :=
  ElevenRUP.step65473 (p 5245) (p 6057) (derived65472 p h) (h 13368)

theorem derived65474 (p : Nat → Prop) (h : Inputs p) :
    (p 3442) :=
  ElevenRUP.step65474 (p 1274) (p 1280) (p 3442) (h 4969) (h 4970) (h 1392)

theorem derived65475 (p : Nat → Prop) (h : Inputs p) :
    (p 3443) :=
  ElevenRUP.step65475 (p 3442) (p 3443) (derived65474 p h) (h 4987)

theorem derived65476 (p : Nat → Prop) (h : Inputs p) :
    (p 5237) :=
  ElevenRUP.step65476 (p 3443) (p 5237) (derived65475 p h) (h 8924)

theorem derived65477 (p : Nat → Prop) (h : Inputs p) :
    (p 6054) :=
  ElevenRUP.step65477 (p 5237) (p 6054) (derived65476 p h) (h 13347)

theorem derived65478 (p : Nat → Prop) (h : Inputs p) :
    (p 3427) :=
  ElevenRUP.step65478 (p 1262) (p 1268) (p 3427) (h 4944) (h 4945) (h 1379)

theorem derived65479 (p : Nat → Prop) (h : Inputs p) :
    (p 3428) :=
  ElevenRUP.step65479 (p 3427) (p 3428) (derived65478 p h) (h 4962)

theorem derived65480 (p : Nat → Prop) (h : Inputs p) :
    (p 5226) :=
  ElevenRUP.step65480 (p 3428) (p 5226) (derived65479 p h) (h 8906)

theorem derived65481 (p : Nat → Prop) (h : Inputs p) :
    (p 6051) :=
  ElevenRUP.step65481 (p 5226) (p 6051) (derived65480 p h) (h 13325)

theorem derived65482 (p : Nat → Prop) (h : Inputs p) :
    (p 3415) :=
  ElevenRUP.step65482 (p 1250) (p 1256) (p 3415) (h 4922) (h 4923) (h 1366)

theorem derived65483 (p : Nat → Prop) (h : Inputs p) :
    (p 3416) :=
  ElevenRUP.step65483 (p 3415) (p 3416) (derived65482 p h) (h 4940)

theorem derived65484 (p : Nat → Prop) (h : Inputs p) :
    (p 5218) :=
  ElevenRUP.step65484 (p 3416) (p 5218) (derived65483 p h) (h 8886)

theorem derived65485 (p : Nat → Prop) (h : Inputs p) :
    (p 6048) :=
  ElevenRUP.step65485 (p 5218) (p 6048) (derived65484 p h) (h 13305)

theorem derived65486 (p : Nat → Prop) (h : Inputs p) :
    (p 3403) :=
  ElevenRUP.step65486 (p 1238) (p 1244) (p 3403) (h 4900) (h 4901) (h 1353)

theorem derived65487 (p : Nat → Prop) (h : Inputs p) :
    (p 3404) :=
  ElevenRUP.step65487 (p 3403) (p 3404) (derived65486 p h) (h 4918)

theorem derived65488 (p : Nat → Prop) (h : Inputs p) :
    (p 5212) :=
  ElevenRUP.step65488 (p 3404) (p 5212) (derived65487 p h) (h 8866)

theorem derived65489 (p : Nat → Prop) (h : Inputs p) :
    (p 6045) :=
  ElevenRUP.step65489 (p 5212) (p 6045) (derived65488 p h) (h 13287)

theorem derived65490 (p : Nat → Prop) (h : Inputs p) :
    (p 3392) :=
  ElevenRUP.step65490 (p 1226) (p 1232) (p 3392) (h 4879) (h 4880) (h 1340)

theorem derived65491 (p : Nat → Prop) (h : Inputs p) :
    (p 3393) :=
  ElevenRUP.step65491 (p 3392) (p 3393) (derived65490 p h) (h 4897)

theorem derived65492 (p : Nat → Prop) (h : Inputs p) :
    (p 5204) :=
  ElevenRUP.step65492 (p 3393) (p 5204) (derived65491 p h) (h 8846)

theorem derived65493 (p : Nat → Prop) (h : Inputs p) :
    (p 6042) :=
  ElevenRUP.step65493 (p 5204) (p 6042) (derived65492 p h) (h 13268)

theorem derived65494 (p : Nat → Prop) (h : Inputs p) :
    (p 3382) :=
  ElevenRUP.step65494 (p 1214) (p 1220) (p 3382) (h 4859) (h 4860) (h 1327)

theorem derived65495 (p : Nat → Prop) (h : Inputs p) :
    (p 3383) :=
  ElevenRUP.step65495 (p 3382) (p 3383) (derived65494 p h) (h 4877)

theorem derived65496 (p : Nat → Prop) (h : Inputs p) :
    (p 5195) :=
  ElevenRUP.step65496 (p 3383) (p 5195) (derived65495 p h) (h 8829)

theorem derived65497 (p : Nat → Prop) (h : Inputs p) :
    (p 6039) :=
  ElevenRUP.step65497 (p 5195) (p 6039) (derived65496 p h) (h 13251)

theorem derived65498 (p : Nat → Prop) (h : Inputs p) :
    (p 3372) :=
  ElevenRUP.step65498 (p 1202) (p 1208) (p 3372) (h 4839) (h 4840) (h 1314)

theorem derived65499 (p : Nat → Prop) (h : Inputs p) :
    (p 3373) :=
  ElevenRUP.step65499 (p 3372) (p 3373) (derived65498 p h) (h 4857)

theorem derived65500 (p : Nat → Prop) (h : Inputs p) :
    (p 5188) :=
  ElevenRUP.step65500 (p 3373) (p 5188) (derived65499 p h) (h 8812)

theorem derived65501 (p : Nat → Prop) (h : Inputs p) :
    (p 6036) :=
  ElevenRUP.step65501 (p 5188) (p 6036) (derived65500 p h) (h 13233)

theorem derived65502 (p : Nat → Prop) (h : Inputs p) :
    (p 3348) :=
  ElevenRUP.step65502 (p 1190) (p 1196) (p 3348) (h 4810) (h 4811) (h 1301)

theorem derived65503 (p : Nat → Prop) (h : Inputs p) :
    (p 3349) :=
  ElevenRUP.step65503 (p 3348) (p 3349) (derived65502 p h) (h 4828)

theorem derived65504 (p : Nat → Prop) (h : Inputs p) :
    (p 5179) :=
  ElevenRUP.step65504 (p 3349) (p 5179) (derived65503 p h) (h 8789)

theorem derived65505 (p : Nat → Prop) (h : Inputs p) :
    (p 6033) :=
  ElevenRUP.step65505 (p 5179) (p 6033) (derived65504 p h) (h 13211)

theorem derived65506 (p : Nat → Prop) (h : Inputs p) :
    (p 3336) :=
  ElevenRUP.step65506 (p 1178) (p 1184) (p 3336) (h 4789) (h 4790) (h 1288)

theorem derived65507 (p : Nat → Prop) (h : Inputs p) :
    (p 3337) :=
  ElevenRUP.step65507 (p 3336) (p 3337) (derived65506 p h) (h 4807)

theorem derived65508 (p : Nat → Prop) (h : Inputs p) :
    (p 5168) :=
  ElevenRUP.step65508 (p 3337) (p 5168) (derived65507 p h) (h 8772)

theorem derived65509 (p : Nat → Prop) (h : Inputs p) :
    (p 6030) :=
  ElevenRUP.step65509 (p 5168) (p 6030) (derived65508 p h) (h 13194)

theorem derived65510 (p : Nat → Prop) (h : Inputs p) :
    (p 3326) :=
  ElevenRUP.step65510 (p 1166) (p 1172) (p 3326) (h 4769) (h 4770) (h 1275)

theorem derived65511 (p : Nat → Prop) (h : Inputs p) :
    (p 3327) :=
  ElevenRUP.step65511 (p 3326) (p 3327) (derived65510 p h) (h 4787)

theorem derived65512 (p : Nat → Prop) (h : Inputs p) :
    (p 5156) :=
  ElevenRUP.step65512 (p 3327) (p 5156) (derived65511 p h) (h 8754)

theorem derived65513 (p : Nat → Prop) (h : Inputs p) :
    (p 6027) :=
  ElevenRUP.step65513 (p 5156) (p 6027) (derived65512 p h) (h 13177)

theorem derived65514 (p : Nat → Prop) (h : Inputs p) :
    (p 3312) :=
  ElevenRUP.step65514 (p 1154) (p 1160) (p 3312) (h 4747) (h 4748) (h 1262)

theorem derived65515 (p : Nat → Prop) (h : Inputs p) :
    (p 3313) :=
  ElevenRUP.step65515 (p 3312) (p 3313) (derived65514 p h) (h 4765)

theorem derived65516 (p : Nat → Prop) (h : Inputs p) :
    (p 5146) :=
  ElevenRUP.step65516 (p 3313) (p 5146) (derived65515 p h) (h 8736)

theorem derived65517 (p : Nat → Prop) (h : Inputs p) :
    (p 6024) :=
  ElevenRUP.step65517 (p 5146) (p 6024) (derived65516 p h) (h 13159)

theorem derived65518 (p : Nat → Prop) (h : Inputs p) :
    (p 3302) :=
  ElevenRUP.step65518 (p 1142) (p 1148) (p 3302) (h 4727) (h 4728) (h 1249)

theorem derived65519 (p : Nat → Prop) (h : Inputs p) :
    (p 3303) :=
  ElevenRUP.step65519 (p 3302) (p 3303) (derived65518 p h) (h 4745)

theorem derived65520 (p : Nat → Prop) (h : Inputs p) :
    (p 5139) :=
  ElevenRUP.step65520 (p 3303) (p 5139) (derived65519 p h) (h 8718)

theorem derived65521 (p : Nat → Prop) (h : Inputs p) :
    (p 6021) :=
  ElevenRUP.step65521 (p 5139) (p 6021) (derived65520 p h) (h 13142)

theorem derived65522 (p : Nat → Prop) (h : Inputs p) :
    (p 3269) :=
  ElevenRUP.step65522 (p 1118) (p 1124) (p 3269) (h 4659) (h 4660) (h 1223)

theorem derived65523 (p : Nat → Prop) (h : Inputs p) :
    (p 3270) :=
  ElevenRUP.step65523 (p 3269) (p 3270) (derived65522 p h) (h 4677)

theorem derived65524 (p : Nat → Prop) (h : Inputs p) :
    (p 5124) :=
  ElevenRUP.step65524 (p 3270) (p 5124) (derived65523 p h) (h 8677)

theorem derived65525 (p : Nat → Prop) (h : Inputs p) :
    (p 6018) :=
  ElevenRUP.step65525 (p 5124) (p 6018) (derived65524 p h) (h 13123)

theorem derived65526 (p : Nat → Prop) (h : Inputs p) :
    (p 3259) :=
  ElevenRUP.step65526 (p 1106) (p 1112) (p 3259) (h 4639) (h 4640) (h 1210)

theorem derived65527 (p : Nat → Prop) (h : Inputs p) :
    (p 3260) :=
  ElevenRUP.step65527 (p 3259) (p 3260) (derived65526 p h) (h 4657)

theorem derived65528 (p : Nat → Prop) (h : Inputs p) :
    (p 5114) :=
  ElevenRUP.step65528 (p 3260) (p 5114) (derived65527 p h) (h 8659)

theorem derived65529 (p : Nat → Prop) (h : Inputs p) :
    (p 6015) :=
  ElevenRUP.step65529 (p 5114) (p 6015) (derived65528 p h) (h 13106)

theorem derived65530 (p : Nat → Prop) (h : Inputs p) :
    (p 2601) :=
  ElevenRUP.step65530 (p 482) (p 488) (p 2601) (h 3327) (h 3328) (h 534)

theorem derived65531 (p : Nat → Prop) (h : Inputs p) :
    (p 2602) :=
  ElevenRUP.step65531 (p 2601) (p 2602) (derived65530 p h) (h 3345)

theorem derived65532 (p : Nat → Prop) (h : Inputs p) :
    (p 4731) :=
  ElevenRUP.step65532 (p 2602) (p 4731) (derived65531 p h) (h 7694)

theorem derived65533 (p : Nat → Prop) (h : Inputs p) :
    (p 5883) :=
  ElevenRUP.step65533 (p 4731) (p 5883) (derived65532 p h) (h 12306)

theorem derived65534 (p : Nat → Prop) (h : Inputs p) :
    (p 3249) :=
  ElevenRUP.step65534 (p 1094) (p 1100) (p 3249) (h 4619) (h 4620) (h 1197)

theorem derived65535 (p : Nat → Prop) (h : Inputs p) :
    (p 3250) :=
  ElevenRUP.step65535 (p 3249) (p 3250) (derived65534 p h) (h 4637)

theorem derived65536 (p : Nat → Prop) (h : Inputs p) :
    (p 5105) :=
  ElevenRUP.step65536 (p 3250) (p 5105) (derived65535 p h) (h 8641)

theorem derived65537 (p : Nat → Prop) (h : Inputs p) :
    (p 6012) :=
  ElevenRUP.step65537 (p 5105) (p 6012) (derived65536 p h) (h 13088)

theorem derived65538 (p : Nat → Prop) (h : Inputs p) :
    (p 3239) :=
  ElevenRUP.step65538 (p 1082) (p 1088) (p 3239) (h 4599) (h 4600) (h 1184)

theorem derived65539 (p : Nat → Prop) (h : Inputs p) :
    (p 3240) :=
  ElevenRUP.step65539 (p 3239) (p 3240) (derived65538 p h) (h 4617)

theorem derived65540 (p : Nat → Prop) (h : Inputs p) :
    (p 5100) :=
  ElevenRUP.step65540 (p 3240) (p 5100) (derived65539 p h) (h 8622)

theorem derived65541 (p : Nat → Prop) (h : Inputs p) :
    (p 6009) :=
  ElevenRUP.step65541 (p 5100) (p 6009) (derived65540 p h) (h 13068)

theorem derived65542 (p : Nat → Prop) (h : Inputs p) :
    (p 3205) :=
  ElevenRUP.step65542 (p 1058) (p 1064) (p 3205) (h 4529) (h 4530) (h 1158)

theorem derived65543 (p : Nat → Prop) (h : Inputs p) :
    (p 3206) :=
  ElevenRUP.step65543 (p 3205) (p 3206) (derived65542 p h) (h 4547)

theorem derived65544 (p : Nat → Prop) (h : Inputs p) :
    (p 5088) :=
  ElevenRUP.step65544 (p 3206) (p 5088) (derived65543 p h) (h 8584)

theorem derived65546 (p : Nat → Prop) (h : Inputs p) :
    (p 3194) :=
  ElevenRUP.step65546 (p 1046) (p 1052) (p 3194) (h 4508) (h 4509) (h 1145)

theorem derived65547 (p : Nat → Prop) (h : Inputs p) :
    (p 3195) :=
  ElevenRUP.step65547 (p 3194) (p 3195) (derived65546 p h) (h 4526)

theorem derived65548 (p : Nat → Prop) (h : Inputs p) :
    (p 5080) :=
  ElevenRUP.step65548 (p 3195) (p 5080) (derived65547 p h) (h 8565)

theorem derived65549 (p : Nat → Prop) (h : Inputs p) :
    (p 6003) :=
  ElevenRUP.step65549 (p 5080) (p 6003) (derived65548 p h) (h 13029)

theorem derived65550 (p : Nat → Prop) (h : Inputs p) :
    (p 3182) :=
  ElevenRUP.step65550 (p 1034) (p 1040) (p 3182) (h 4487) (h 4488) (h 1132)

theorem derived65551 (p : Nat → Prop) (h : Inputs p) :
    (p 3183) :=
  ElevenRUP.step65551 (p 3182) (p 3183) (derived65550 p h) (h 4505)

theorem derived65552 (p : Nat → Prop) (h : Inputs p) :
    (p 5072) :=
  ElevenRUP.step65552 (p 3183) (p 5072) (derived65551 p h) (h 8547)

theorem derived65553 (p : Nat → Prop) (h : Inputs p) :
    (p 6000) :=
  ElevenRUP.step65553 (p 5072) (p 6000) (derived65552 p h) (h 13009)

theorem derived65554 (p : Nat → Prop) (h : Inputs p) :
    (p 2234) :=
  ElevenRUP.step65554 (p 146) (p 152) (p 2234) (h 2603) (h 2604) (h 170)

theorem derived65555 (p : Nat → Prop) (h : Inputs p) :
    (p 2235) :=
  ElevenRUP.step65555 (p 2234) (p 2235) (derived65554 p h) (h 2621)

theorem derived65556 (p : Nat → Prop) (h : Inputs p) :
    (p 4540) :=
  ElevenRUP.step65556 (p 2235) (p 4540) (derived65555 p h) (h 7160)

theorem derived65557 (p : Nat → Prop) (h : Inputs p) :
    (p 3149) :=
  ElevenRUP.step65557 (p 1010) (p 1016) (p 3149) (h 4419) (h 4420) (h 1106)

theorem derived65558 (p : Nat → Prop) (h : Inputs p) :
    (p 3150) :=
  ElevenRUP.step65558 (p 3149) (p 3150) (derived65557 p h) (h 4437)

theorem derived65559 (p : Nat → Prop) (h : Inputs p) :
    (p 5060) :=
  ElevenRUP.step65559 (p 3150) (p 5060) (derived65558 p h) (h 8503)

theorem derived65560 (p : Nat → Prop) (h : Inputs p) :
    (p 5997) :=
  ElevenRUP.step65560 (p 5060) (p 5997) (derived65559 p h) (h 12989)

theorem derived65561 (p : Nat → Prop) (h : Inputs p) :
    (p 3139) :=
  ElevenRUP.step65561 (p 998) (p 1004) (p 3139) (h 4399) (h 4400) (h 1093)

theorem derived65562 (p : Nat → Prop) (h : Inputs p) :
    (p 3140) :=
  ElevenRUP.step65562 (p 3139) (p 3140) (derived65561 p h) (h 4417)

theorem derived65563 (p : Nat → Prop) (h : Inputs p) :
    (p 5054) :=
  ElevenRUP.step65563 (p 3140) (p 5054) (derived65562 p h) (h 8486)

theorem derived65564 (p : Nat → Prop) (h : Inputs p) :
    (p 5994) :=
  ElevenRUP.step65564 (p 5054) (p 5994) (derived65563 p h) (h 12972)

theorem derived65565 (p : Nat → Prop) (h : Inputs p) :
    (p 3129) :=
  ElevenRUP.step65565 (p 986) (p 992) (p 3129) (h 4379) (h 4380) (h 1080)

theorem derived65566 (p : Nat → Prop) (h : Inputs p) :
    (p 3130) :=
  ElevenRUP.step65566 (p 3129) (p 3130) (derived65565 p h) (h 4397)

theorem derived65567 (p : Nat → Prop) (h : Inputs p) :
    (p 5047) :=
  ElevenRUP.step65567 (p 3130) (p 5047) (derived65566 p h) (h 8469)

theorem derived65568 (p : Nat → Prop) (h : Inputs p) :
    (p 5991) :=
  ElevenRUP.step65568 (p 5047) (p 5991) (derived65567 p h) (h 12955)

theorem derived65569 (p : Nat → Prop) (h : Inputs p) :
    (p 3118) :=
  ElevenRUP.step65569 (p 974) (p 980) (p 3118) (h 4357) (h 4358) (h 1067)

theorem derived65570 (p : Nat → Prop) (h : Inputs p) :
    (p 3119) :=
  ElevenRUP.step65570 (p 3118) (p 3119) (derived65569 p h) (h 4375)

theorem derived65571 (p : Nat → Prop) (h : Inputs p) :
    (p 5041) :=
  ElevenRUP.step65571 (p 3119) (p 5041) (derived65570 p h) (h 8452)

theorem derived65572 (p : Nat → Prop) (h : Inputs p) :
    (p 5988) :=
  ElevenRUP.step65572 (p 5041) (p 5988) (derived65571 p h) (h 12937)

theorem derived65573 (p : Nat → Prop) (h : Inputs p) :
    (p 3108) :=
  ElevenRUP.step65573 (p 962) (p 968) (p 3108) (h 4337) (h 4338) (h 1054)

theorem derived65574 (p : Nat → Prop) (h : Inputs p) :
    (p 3109) :=
  ElevenRUP.step65574 (p 3108) (p 3109) (derived65573 p h) (h 4355)

theorem derived65575 (p : Nat → Prop) (h : Inputs p) :
    (p 5034) :=
  ElevenRUP.step65575 (p 3109) (p 5034) (derived65574 p h) (h 8435)

theorem derived65576 (p : Nat → Prop) (h : Inputs p) :
    (p 5985) :=
  ElevenRUP.step65576 (p 5034) (p 5985) (derived65575 p h) (h 12920)

theorem derived65577 (p : Nat → Prop) (h : Inputs p) :
    (p 3098) :=
  ElevenRUP.step65577 (p 950) (p 956) (p 3098) (h 4317) (h 4318) (h 1041)

theorem derived65578 (p : Nat → Prop) (h : Inputs p) :
    (p 3099) :=
  ElevenRUP.step65578 (p 3098) (p 3099) (derived65577 p h) (h 4335)

theorem derived65579 (p : Nat → Prop) (h : Inputs p) :
    (p 5023) :=
  ElevenRUP.step65579 (p 3099) (p 5023) (derived65578 p h) (h 8418)

theorem derived65580 (p : Nat → Prop) (h : Inputs p) :
    (p 5982) :=
  ElevenRUP.step65580 (p 5023) (p 5982) (derived65579 p h) (h 12902)

theorem derived65581 (p : Nat → Prop) (h : Inputs p) :
    (p 3086) :=
  ElevenRUP.step65581 (p 938) (p 944) (p 3086) (h 4296) (h 4297) (h 1028)

theorem derived65582 (p : Nat → Prop) (h : Inputs p) :
    (p 3087) :=
  ElevenRUP.step65582 (p 3086) (p 3087) (derived65581 p h) (h 4314)

theorem derived65583 (p : Nat → Prop) (h : Inputs p) :
    (p 5013) :=
  ElevenRUP.step65583 (p 3087) (p 5013) (derived65582 p h) (h 8399)

theorem derived65584 (p : Nat → Prop) (h : Inputs p) :
    (p 5979) :=
  ElevenRUP.step65584 (p 5013) (p 5979) (derived65583 p h) (h 12884)

theorem derived65585 (p : Nat → Prop) (h : Inputs p) :
    (p 2754) :=
  ElevenRUP.step65585 (p 626) (p 632) (p 2754) (h 3635) (h 3636) (h 690)

theorem derived65586 (p : Nat → Prop) (h : Inputs p) :
    (p 2755) :=
  ElevenRUP.step65586 (p 2754) (p 2755) (derived65585 p h) (h 3653)

theorem derived65587 (p : Nat → Prop) (h : Inputs p) :
    (p 4821) :=
  ElevenRUP.step65587 (p 2755) (p 4821) (derived65586 p h) (h 7915)

theorem derived65588 (p : Nat → Prop) (h : Inputs p) :
    (p 5913) :=
  ElevenRUP.step65588 (p 4821) (p 5913) (derived65587 p h) (h 12480)

theorem derived65589 (p : Nat → Prop) (h : Inputs p) :
    (p 2591) :=
  ElevenRUP.step65589 (p 470) (p 476) (p 2591) (h 3307) (h 3308) (h 521)

theorem derived65590 (p : Nat → Prop) (h : Inputs p) :
    (p 2592) :=
  ElevenRUP.step65590 (p 2591) (p 2592) (derived65589 p h) (h 3325)

theorem derived65591 (p : Nat → Prop) (h : Inputs p) :
    (p 4725) :=
  ElevenRUP.step65591 (p 2592) (p 4725) (derived65590 p h) (h 7677)

theorem derived65592 (p : Nat → Prop) (h : Inputs p) :
    (p 5880) :=
  ElevenRUP.step65592 (p 4725) (p 5880) (derived65591 p h) (h 12289)

theorem derived65595 (p : Nat → Prop) (h : Inputs p) :
    (p 3066) :=
  ElevenRUP.step65595 (p 914) (p 920) (p 3066) (h 4256) (h 4257) (h 1002)

theorem derived65596 (p : Nat → Prop) (h : Inputs p) :
    (p 3067) :=
  ElevenRUP.step65596 (p 3066) (p 3067) (derived65595 p h) (h 4274)

theorem derived65597 (p : Nat → Prop) (h : Inputs p) :
    (p 4999) :=
  ElevenRUP.step65597 (p 3067) (p 4999) (derived65596 p h) (h 8364)

theorem derived65598 (p : Nat → Prop) (h : Inputs p) :
    (p 5973) :=
  ElevenRUP.step65598 (p 4999) (p 5973) (derived65597 p h) (h 12849)

theorem derived65599 (p : Nat → Prop) (h : Inputs p) :
    (p 6055) ∨ (¬ p 4444) ∨ (¬ p 2608) ∨ (p 6079) ∨ (¬ p 4340) :=
  ElevenRUP.step65599 (p 2103) (p 2608) (p 3073) (p 3439) (p 3857) (p 3860) (p 4261) (p 4340) (p 4353) (p 4416) (p 4444) (p 4999) (p 5000) (p 5003) (p 5312) (p 6055) (p 6079) (derived65597 p h) (h 13506) (h 13504) (h 13333) (h 13335) (h 13336) (derived45633 p h) (h 30173) (h 8351) (h 6582) (h 8363) (derived42229 p h) (h 8357)

theorem derived65600 (p : Nat → Prop) (h : Inputs p) :
    (p 2689) :=
  ElevenRUP.step65600 (p 566) (p 572) (p 2689) (h 3504) (h 3505) (h 625)

theorem derived65601 (p : Nat → Prop) (h : Inputs p) :
    (p 2690) :=
  ElevenRUP.step65601 (p 2689) (p 2690) (derived65600 p h) (h 3522)

theorem derived65602 (p : Nat → Prop) (h : Inputs p) :
    (p 4784) :=
  ElevenRUP.step65602 (p 2690) (p 4784) (derived65601 p h) (h 7818)

theorem derived65603 (p : Nat → Prop) (h : Inputs p) :
    (p 5901) :=
  ElevenRUP.step65603 (p 4784) (p 5901) (derived65602 p h) (h 12409)

theorem derived65604 (p : Nat → Prop) (h : Inputs p) :
    (p 2623) :=
  ElevenRUP.step65604 (p 506) (p 512) (p 2623) (h 3371) (h 3372) (h 560)

theorem derived65605 (p : Nat → Prop) (h : Inputs p) :
    (p 2624) :=
  ElevenRUP.step65605 (p 2623) (p 2624) (derived65604 p h) (h 3389)

theorem derived65606 (p : Nat → Prop) (h : Inputs p) :
    (p 4747) :=
  ElevenRUP.step65606 (p 2624) (p 4747) (derived65605 p h) (h 7728)

theorem derived65607 (p : Nat → Prop) (h : Inputs p) :
    (p 5889) :=
  ElevenRUP.step65607 (p 4747) (p 5889) (derived65606 p h) (h 12340)

theorem derived65608 (p : Nat → Prop) (h : Inputs p) :
    (p 2091) :=
  ElevenRUP.step65608 (p 13) (p 19) (p 2091) (h 2316) (h 2317) (h 26)

theorem derived65609 (p : Nat → Prop) (h : Inputs p) :
    (p 2092) :=
  ElevenRUP.step65609 (p 2091) (p 2092) (derived65608 p h) (h 2334)

theorem derived65610 (p : Nat → Prop) (h : Inputs p) :
    (p 4464) :=
  ElevenRUP.step65610 (p 2092) (p 4464) (derived65609 p h) (h 6964)

theorem derived65611 (p : Nat → Prop) (h : Inputs p) :
    (p 2730) :=
  ElevenRUP.step65611 (p 614) (p 620) (p 2730) (h 3586) (h 3587) (h 677)

theorem derived65612 (p : Nat → Prop) (h : Inputs p) :
    (p 2731) :=
  ElevenRUP.step65612 (p 2730) (p 2731) (derived65611 p h) (h 3604)

theorem derived65613 (p : Nat → Prop) (h : Inputs p) :
    (p 4815) :=
  ElevenRUP.step65613 (p 2731) (p 4815) (derived65612 p h) (h 7876)

theorem derived65615 (p : Nat → Prop) (h : Inputs p) :
    (p 2612) :=
  ElevenRUP.step65615 (p 494) (p 500) (p 2612) (h 3349) (h 3350) (h 547)

theorem derived65616 (p : Nat → Prop) (h : Inputs p) :
    (p 2613) :=
  ElevenRUP.step65616 (p 2612) (p 2613) (derived65615 p h) (h 3367)

theorem derived65617 (p : Nat → Prop) (h : Inputs p) :
    (p 4738) :=
  ElevenRUP.step65617 (p 2613) (p 4738) (derived65616 p h) (h 7711)

theorem derived65618 (p : Nat → Prop) (h : Inputs p) :
    (p 5886) :=
  ElevenRUP.step65618 (p 4738) (p 5886) (derived65617 p h) (h 12323)

theorem derived65620 (p : Nat → Prop) (h : Inputs p) :
    (p 2700) :=
  ElevenRUP.step65620 (p 578) (p 584) (p 2700) (h 3526) (h 3527) (h 638)

theorem derived65621 (p : Nat → Prop) (h : Inputs p) :
    (p 2701) :=
  ElevenRUP.step65621 (p 2700) (p 2701) (derived65620 p h) (h 3544)

theorem derived65622 (p : Nat → Prop) (h : Inputs p) :
    (p 4791) :=
  ElevenRUP.step65622 (p 2701) (p 4791) (derived65621 p h) (h 7836)

theorem derived65623 (p : Nat → Prop) (h : Inputs p) :
    (p 5904) :=
  ElevenRUP.step65623 (p 4791) (p 5904) (derived65622 p h) (h 12427)

theorem derived65624 (p : Nat → Prop) (h : Inputs p) :
    (p 2710) :=
  ElevenRUP.step65624 (p 590) (p 596) (p 2710) (h 3546) (h 3547) (h 651)

theorem derived65625 (p : Nat → Prop) (h : Inputs p) :
    (p 2711) :=
  ElevenRUP.step65625 (p 2710) (p 2711) (derived65624 p h) (h 3564)

theorem derived65626 (p : Nat → Prop) (h : Inputs p) :
    (p 4798) :=
  ElevenRUP.step65626 (p 2711) (p 4798) (derived65625 p h) (h 7853)

theorem derived65627 (p : Nat → Prop) (h : Inputs p) :
    (p 5907) :=
  ElevenRUP.step65627 (p 4798) (p 5907) (derived65626 p h) (h 12445)

theorem derived65628 (p : Nat → Prop) (h : Inputs p) :
    (p 2863) :=
  ElevenRUP.step65628 (p 734) (p 740) (p 2863) (h 3852) (h 3853) (h 807)

theorem derived65629 (p : Nat → Prop) (h : Inputs p) :
    (p 2864) :=
  ElevenRUP.step65629 (p 2863) (p 2864) (derived65628 p h) (h 3870)

theorem derived65630 (p : Nat → Prop) (h : Inputs p) :
    (p 4892) :=
  ElevenRUP.step65630 (p 2864) (p 4892) (derived65629 p h) (h 8081)

theorem derived65631 (p : Nat → Prop) (h : Inputs p) :
    (p 5937) :=
  ElevenRUP.step65631 (p 4892) (p 5937) (derived65630 p h) (h 12626)

theorem derived65632 (p : Nat → Prop) (h : Inputs p) :
    (p 3076) :=
  ElevenRUP.step65632 (p 926) (p 932) (p 3076) (h 4276) (h 4277) (h 1015)

theorem derived65633 (p : Nat → Prop) (h : Inputs p) :
    (p 3077) :=
  ElevenRUP.step65633 (p 3076) (p 3077) (derived65632 p h) (h 4294)

theorem derived65634 (p : Nat → Prop) (h : Inputs p) :
    (p 5006) :=
  ElevenRUP.step65634 (p 3077) (p 5006) (derived65633 p h) (h 8382)

theorem derived65635 (p : Nat → Prop) (h : Inputs p) :
    (p 5976) :=
  ElevenRUP.step65635 (p 5006) (p 5976) (derived65634 p h) (h 12867)

theorem derived65636 (p : Nat → Prop) (h : Inputs p) :
    (p 3056) :=
  ElevenRUP.step65636 (p 902) (p 908) (p 3056) (h 4236) (h 4237) (h 989)

theorem derived65637 (p : Nat → Prop) (h : Inputs p) :
    (p 3057) :=
  ElevenRUP.step65637 (p 3056) (p 3057) (derived65636 p h) (h 4254)

theorem derived65638 (p : Nat → Prop) (h : Inputs p) :
    (p 4991) :=
  ElevenRUP.step65638 (p 3057) (p 4991) (derived65637 p h) (h 8347)

theorem derived65639 (p : Nat → Prop) (h : Inputs p) :
    (p 5970) :=
  ElevenRUP.step65639 (p 4991) (p 5970) (derived65638 p h) (h 12832)

theorem derived65640 (p : Nat → Prop) (h : Inputs p) :
    (p 3044) :=
  ElevenRUP.step65640 (p 890) (p 896) (p 3044) (h 4215) (h 4216) (h 976)

theorem derived65641 (p : Nat → Prop) (h : Inputs p) :
    (p 3045) :=
  ElevenRUP.step65641 (p 3044) (p 3045) (derived65640 p h) (h 4233)

theorem derived65642 (p : Nat → Prop) (h : Inputs p) :
    (p 4982) :=
  ElevenRUP.step65642 (p 3045) (p 4982) (derived65641 p h) (h 8328)

theorem derived65643 (p : Nat → Prop) (h : Inputs p) :
    (p 5967) :=
  ElevenRUP.step65643 (p 4982) (p 5967) (derived65642 p h) (h 12815)

theorem derived65644 (p : Nat → Prop) (h : Inputs p) :
    (p 2125) :=
  ElevenRUP.step65644 (p 38) (p 44) (p 2125) (h 2386) (h 2387) (h 53)

theorem derived65645 (p : Nat → Prop) (h : Inputs p) :
    (p 2126) :=
  ElevenRUP.step65645 (p 2125) (p 2126) (derived65644 p h) (h 2404)

theorem derived65646 (p : Nat → Prop) (h : Inputs p) :
    (p 4478) :=
  ElevenRUP.step65646 (p 2126) (p 4478) (derived65645 p h) (h 7002)

theorem derived65647 (p : Nat → Prop) (h : Inputs p) :
    (p 2874) :=
  ElevenRUP.step65647 (p 746) (p 752) (p 2874) (h 3874) (h 3875) (h 820)

theorem derived65648 (p : Nat → Prop) (h : Inputs p) :
    (p 2875) :=
  ElevenRUP.step65648 (p 2874) (p 2875) (derived65647 p h) (h 3892)

theorem derived65649 (p : Nat → Prop) (h : Inputs p) :
    (p 4899) :=
  ElevenRUP.step65649 (p 2875) (p 4899) (derived65648 p h) (h 8099)

theorem derived65650 (p : Nat → Prop) (h : Inputs p) :
    (p 5940) :=
  ElevenRUP.step65650 (p 4899) (p 5940) (derived65649 p h) (h 12645)

theorem derived65651 (p : Nat → Prop) (h : Inputs p) :
    (p 3009) :=
  ElevenRUP.step65651 (p 866) (p 872) (p 3009) (h 4142) (h 4143) (h 950)

theorem derived65652 (p : Nat → Prop) (h : Inputs p) :
    (p 3010) :=
  ElevenRUP.step65652 (p 3009) (p 3010) (derived65651 p h) (h 4160)

theorem derived65653 (p : Nat → Prop) (h : Inputs p) :
    (p 4970) :=
  ElevenRUP.step65653 (p 3010) (p 4970) (derived65652 p h) (h 8287)

theorem derived65654 (p : Nat → Prop) (h : Inputs p) :
    (p 5964) :=
  ElevenRUP.step65654 (p 4970) (p 5964) (derived65653 p h) (h 12794)

theorem derived65655 (p : Nat → Prop) (h : Inputs p) :
    (p 2998) :=
  ElevenRUP.step65655 (p 854) (p 860) (p 2998) (h 4120) (h 4121) (h 937)

theorem derived65656 (p : Nat → Prop) (h : Inputs p) :
    (p 2999) :=
  ElevenRUP.step65656 (p 2998) (p 2999) (derived65655 p h) (h 4138)

theorem derived65657 (p : Nat → Prop) (h : Inputs p) :
    (p 4961) :=
  ElevenRUP.step65657 (p 2999) (p 4961) (derived65656 p h) (h 8270)

theorem derived65658 (p : Nat → Prop) (h : Inputs p) :
    (p 5961) :=
  ElevenRUP.step65658 (p 4961) (p 5961) (derived65657 p h) (h 12774)

theorem derived65659 (p : Nat → Prop) (h : Inputs p) :
    (p 2985) :=
  ElevenRUP.step65659 (p 842) (p 848) (p 2985) (h 4097) (h 4098) (h 924)

theorem derived65660 (p : Nat → Prop) (h : Inputs p) :
    (p 2986) :=
  ElevenRUP.step65660 (p 2985) (p 2986) (derived65659 p h) (h 4115)

theorem derived65661 (p : Nat → Prop) (h : Inputs p) :
    (p 4955) :=
  ElevenRUP.step65661 (p 2986) (p 4955) (derived65660 p h) (h 8253)

theorem derived65662 (p : Nat → Prop) (h : Inputs p) :
    (p 5958) :=
  ElevenRUP.step65662 (p 4955) (p 5958) (derived65661 p h) (h 12752)

theorem derived65663 (p : Nat → Prop) (h : Inputs p) :
    (p 2634) :=
  ElevenRUP.step65663 (p 518) (p 524) (p 2634) (h 3393) (h 3394) (h 573)

theorem derived65664 (p : Nat → Prop) (h : Inputs p) :
    (p 2635) :=
  ElevenRUP.step65664 (p 2634) (p 2635) (derived65663 p h) (h 3411)

theorem derived65665 (p : Nat → Prop) (h : Inputs p) :
    (p 4754) :=
  ElevenRUP.step65665 (p 2635) (p 4754) (derived65664 p h) (h 7746)

theorem derived65666 (p : Nat → Prop) (h : Inputs p) :
    (p 5892) :=
  ElevenRUP.step65666 (p 4754) (p 5892) (derived65665 p h) (h 12358)

theorem derived65667 (p : Nat → Prop) (h : Inputs p) :
    (p 2975) :=
  ElevenRUP.step65667 (p 830) (p 836) (p 2975) (h 4077) (h 4078) (h 911)

theorem derived65668 (p : Nat → Prop) (h : Inputs p) :
    (p 2976) :=
  ElevenRUP.step65668 (p 2975) (p 2976) (derived65667 p h) (h 4095)

theorem derived65669 (p : Nat → Prop) (h : Inputs p) :
    (p 4945) :=
  ElevenRUP.step65669 (p 2976) (p 4945) (derived65668 p h) (h 8236)

theorem derived65670 (p : Nat → Prop) (h : Inputs p) :
    (p 5955) :=
  ElevenRUP.step65670 (p 4945) (p 5955) (derived65669 p h) (h 12734)

theorem derived65671 (p : Nat → Prop) (h : Inputs p) :
    (p 2223) :=
  ElevenRUP.step65671 (p 134) (p 140) (p 2223) (h 2581) (h 2582) (h 157)

theorem derived65672 (p : Nat → Prop) (h : Inputs p) :
    (p 2224) :=
  ElevenRUP.step65672 (p 2223) (p 2224) (derived65671 p h) (h 2599)

theorem derived65673 (p : Nat → Prop) (h : Inputs p) :
    (p 4534) :=
  ElevenRUP.step65673 (p 2224) (p 4534) (derived65672 p h) (h 7155)

theorem derived65674 (p : Nat → Prop) (h : Inputs p) :
    (p 5811) :=
  ElevenRUP.step65674 (p 4534) (p 5811) (derived65673 p h) (h 11885)

theorem derived65675 (p : Nat → Prop) (h : Inputs p) :
    (p 2965) :=
  ElevenRUP.step65675 (p 818) (p 824) (p 2965) (h 4057) (h 4058) (h 898)

theorem derived65676 (p : Nat → Prop) (h : Inputs p) :
    (p 2966) :=
  ElevenRUP.step65676 (p 2965) (p 2966) (derived65675 p h) (h 4075)

theorem derived65677 (p : Nat → Prop) (h : Inputs p) :
    (p 4936) :=
  ElevenRUP.step65677 (p 2966) (p 4936) (derived65676 p h) (h 8219)

theorem derived65678 (p : Nat → Prop) (h : Inputs p) :
    (p 5952) :=
  ElevenRUP.step65678 (p 4936) (p 5952) (derived65677 p h) (h 12716)

theorem derived65679 (p : Nat → Prop) (h : Inputs p) :
    (p 2884) :=
  ElevenRUP.step65679 (p 758) (p 764) (p 2884) (h 3894) (h 3895) (h 833)

theorem derived65680 (p : Nat → Prop) (h : Inputs p) :
    (p 2885) :=
  ElevenRUP.step65680 (p 2884) (p 2885) (derived65679 p h) (h 3912)

theorem derived65681 (p : Nat → Prop) (h : Inputs p) :
    (p 4907) :=
  ElevenRUP.step65681 (p 2885) (p 4907) (derived65680 p h) (h 8117)

theorem derived65682 (p : Nat → Prop) (h : Inputs p) :
    (p 5943) :=
  ElevenRUP.step65682 (p 4907) (p 5943) (derived65681 p h) (h 12662)

theorem derived65685 (p : Nat → Prop) (h : Inputs p) :
    (p 2939) :=
  ElevenRUP.step65685 (p 806) (p 812) (p 2939) (h 4006) (h 4007) (h 885)

theorem derived65686 (p : Nat → Prop) (h : Inputs p) :
    (p 2940) :=
  ElevenRUP.step65686 (p 2939) (p 2940) (derived65685 p h) (h 4024)

theorem derived65687 (p : Nat → Prop) (h : Inputs p) :
    (p 4931) :=
  ElevenRUP.step65687 (p 2940) (p 4931) (derived65686 p h) (h 8183)

theorem derived65688 (p : Nat → Prop) (h : Inputs p) :
    (p 2159) :=
  ElevenRUP.step65688 (p 62) (p 68) (p 2159) (h 2456) (h 2457) (h 79)

theorem derived65689 (p : Nat → Prop) (h : Inputs p) :
    (p 2160) :=
  ElevenRUP.step65689 (p 2159) (p 2160) (derived65688 p h) (h 2474)

theorem derived65690 (p : Nat → Prop) (h : Inputs p) :
    (p 4490) :=
  ElevenRUP.step65690 (p 2160) (p 4490) (derived65689 p h) (h 7052)

theorem derived65691 (p : Nat → Prop) (h : Inputs p) :
    (p 5793) :=
  ElevenRUP.step65691 (p 4490) (p 5793) (derived65690 p h) (h 11781)

theorem derived65692 (p : Nat → Prop) (h : Inputs p) :
    (p 2452) :=
  ElevenRUP.step65692 (p 362) (p 368) (p 2452) (h 3035) (h 3036) (h 404)

theorem derived65693 (p : Nat → Prop) (h : Inputs p) :
    (p 2453) :=
  ElevenRUP.step65693 (p 2452) (p 2453) (derived65692 p h) (h 3053)

theorem derived65694 (p : Nat → Prop) (h : Inputs p) :
    (p 4664) :=
  ElevenRUP.step65694 (p 2453) (p 4664) (derived65693 p h) (h 7494)

theorem derived65695 (p : Nat → Prop) (h : Inputs p) :
    (p 5862) :=
  ElevenRUP.step65695 (p 4664) (p 5862) (derived65694 p h) (h 12183)

theorem derived65697 (p : Nat → Prop) (h : Inputs p) :
    (p 2832) :=
  ElevenRUP.step65697 (p 698) (p 704) (p 2832) (h 3790) (h 3791) (h 768)

theorem derived65698 (p : Nat → Prop) (h : Inputs p) :
    (p 2833) :=
  ElevenRUP.step65698 (p 2832) (p 2833) (derived65697 p h) (h 3808)

theorem derived65699 (p : Nat → Prop) (h : Inputs p) :
    (p 4872) :=
  ElevenRUP.step65699 (p 2833) (p 4872) (derived65698 p h) (h 8030)

theorem derived65700 (p : Nat → Prop) (h : Inputs p) :
    (p 5928) :=
  ElevenRUP.step65700 (p 4872) (p 5928) (derived65699 p h) (h 12574)

theorem derived65702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4743) ∨ (¬ p 2098) ∨ (¬ p 2191) :=
  ElevenRUP.step65702 (p 2098) (p 2132) (p 2135) (p 2138) (p 2142) (p 2166) (p 2191) (p 2619) (p 2753) (p 3537) (p 4188) (p 4242) (p 4243) (p 4478) (p 4731) (p 4732) (p 4735) (p 4737) (p 4743) (p 4872) (p 4873) (p 4874) (p 4875) (p 4876) (p 5310) (p 5311) (p 5314) (derived65699 p h) (derived65444 p h) (derived65646 p h) (derived65532 p h) (h 9935) (h 7702) (h 7704) (h 6718) (h 8021) (h 8029) (h 8015) (h 8019) (h 25955) (derived42331 p h) (h 9067) (h 2408) (h 9073) (h 7001) (h 9061) (h 2422) (h 6369) (derived49512 p h) (h 7680) (h 7689) (h 7693)

theorem derived65703 (p : Nat → Prop) (h : Inputs p) :
    (p 2213) :=
  ElevenRUP.step65703 (p 122) (p 128) (p 2213) (h 2561) (h 2562) (h 144)

theorem derived65704 (p : Nat → Prop) (h : Inputs p) :
    (p 2214) :=
  ElevenRUP.step65704 (p 2213) (p 2214) (derived65703 p h) (h 2579)

theorem derived65705 (p : Nat → Prop) (h : Inputs p) :
    (p 4526) :=
  ElevenRUP.step65705 (p 2214) (p 4526) (derived65704 p h) (h 7137)

theorem derived65706 (p : Nat → Prop) (h : Inputs p) :
    (p 5808) :=
  ElevenRUP.step65706 (p 4526) (p 5808) (derived65705 p h) (h 11868)

theorem derived65707 (p : Nat → Prop) (h : Inputs p) :
    (p 2678) :=
  ElevenRUP.step65707 (p 554) (p 560) (p 2678) (h 3482) (h 3483) (h 612)

theorem derived65708 (p : Nat → Prop) (h : Inputs p) :
    (p 2679) :=
  ElevenRUP.step65708 (p 2678) (p 2679) (derived65707 p h) (h 3500)

theorem derived65709 (p : Nat → Prop) (h : Inputs p) :
    (p 4775) :=
  ElevenRUP.step65709 (p 2679) (p 4775) (derived65708 p h) (h 7801)

theorem derived65710 (p : Nat → Prop) (h : Inputs p) :
    (p 5898) :=
  ElevenRUP.step65710 (p 4775) (p 5898) (derived65709 p h) (h 12392)

theorem derived65711 (p : Nat → Prop) (h : Inputs p) :
    (p 3760) :=
  ElevenRUP.step65711 (p 1550) (p 1556) (p 3760) (h 5513) (h 5514) (h 1691)

theorem derived65712 (p : Nat → Prop) (h : Inputs p) :
    (p 3761) :=
  ElevenRUP.step65712 (p 3760) (p 3761) (derived65711 p h) (h 5531)

theorem derived65713 (p : Nat → Prop) (h : Inputs p) :
    (p 5462) :=
  ElevenRUP.step65713 (p 3761) (p 5462) (derived65712 p h) (h 9455)

theorem derived65714 (p : Nat → Prop) (h : Inputs p) :
    (p 2822) :=
  ElevenRUP.step65714 (p 686) (p 692) (p 2822) (h 3770) (h 3771) (h 755)

theorem derived65715 (p : Nat → Prop) (h : Inputs p) :
    (p 2823) :=
  ElevenRUP.step65715 (p 2822) (p 2823) (derived65714 p h) (h 3788)

theorem derived65716 (p : Nat → Prop) (h : Inputs p) :
    (p 4864) :=
  ElevenRUP.step65716 (p 2823) (p 4864) (derived65715 p h) (h 8013)

theorem derived65717 (p : Nat → Prop) (h : Inputs p) :
    (p 5925) :=
  ElevenRUP.step65717 (p 4864) (p 5925) (derived65716 p h) (h 12557)

theorem derived65718 (p : Nat → Prop) (h : Inputs p) :
    (p 2389) :=
  ElevenRUP.step65718 (p 290) (p 296) (p 2389) (h 2912) (h 2913) (h 326)

theorem derived65719 (p : Nat → Prop) (h : Inputs p) :
    (p 2390) :=
  ElevenRUP.step65719 (p 2389) (p 2390) (derived65718 p h) (h 2930)

theorem derived65720 (p : Nat → Prop) (h : Inputs p) :
    (p 4618) :=
  ElevenRUP.step65720 (p 2390) (p 4618) (derived65719 p h) (h 7391)

theorem derived65721 (p : Nat → Prop) (h : Inputs p) :
    (p 5844) :=
  ElevenRUP.step65721 (p 4618) (p 5844) (derived65720 p h) (h 12079)

theorem derived65722 (p : Nat → Prop) (h : Inputs p) :
    (p 2267) :=
  ElevenRUP.step65722 (p 170) (p 176) (p 2267) (h 2671) (h 2672) (h 196)

theorem derived65723 (p : Nat → Prop) (h : Inputs p) :
    (p 2268) :=
  ElevenRUP.step65723 (p 2267) (p 2268) (derived65722 p h) (h 2689)

theorem derived65724 (p : Nat → Prop) (h : Inputs p) :
    (p 4553) :=
  ElevenRUP.step65724 (p 2268) (p 4553) (derived65723 p h) (h 7215)

theorem derived65725 (p : Nat → Prop) (h : Inputs p) :
    (p 5817) :=
  ElevenRUP.step65725 (p 4553) (p 5817) (derived65724 p h) (h 11920)

theorem derived65726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4191) ∨ (¬ p 2761) ∨ (p 4322) ∨ (¬ p 3246) :=
  ElevenRUP.step65726 (p 2761) (p 3097) (p 3125) (p 3246) (p 4025) (p 4033) (p 4191) (p 4322) (p 4381) (p 4553) (p 4554) (p 4557) (p 4559) (p 4618) (p 4619) (p 4622) (p 4623) (p 5041) (p 5042) (p 5044) (derived65571 p h) (derived65720 p h) (derived65724 p h) (h 10478) (h 6872) (h 23007) (h 8438) (h 7382) (h 8451) (h 7390) (h 8445) (h 7376) (h 20392) (derived41086 p h) (h 7202) (h 7210) (h 7214)

theorem derived65727 (p : Nat → Prop) (h : Inputs p) :
    (p 2894) :=
  ElevenRUP.step65727 (p 770) (p 776) (p 2894) (h 3914) (h 3915) (h 846)

theorem derived65728 (p : Nat → Prop) (h : Inputs p) :
    (p 2895) :=
  ElevenRUP.step65728 (p 2894) (p 2895) (derived65727 p h) (h 3932)

theorem derived65729 (p : Nat → Prop) (h : Inputs p) :
    (p 4915) :=
  ElevenRUP.step65729 (p 2895) (p 4915) (derived65728 p h) (h 8134)

theorem derived65730 (p : Nat → Prop) (h : Inputs p) :
    (p 5946) :=
  ElevenRUP.step65730 (p 4915) (p 5946) (derived65729 p h) (h 12679)

theorem derived65731 (p : Nat → Prop) (h : Inputs p) :
    (p 2277) :=
  ElevenRUP.step65731 (p 182) (p 188) (p 2277) (h 2691) (h 2692) (h 209)

theorem derived65732 (p : Nat → Prop) (h : Inputs p) :
    (p 2278) :=
  ElevenRUP.step65732 (p 2277) (p 2278) (derived65731 p h) (h 2709)

theorem derived65733 (p : Nat → Prop) (h : Inputs p) :
    (p 4561) :=
  ElevenRUP.step65733 (p 2278) (p 4561) (derived65732 p h) (h 7233)

theorem derived65734 (p : Nat → Prop) (h : Inputs p) :
    (p 5820) :=
  ElevenRUP.step65734 (p 4561) (p 5820) (derived65733 p h) (h 11937)

theorem derived65735 (p : Nat → Prop) (h : Inputs p) :
    (p 2149) :=
  ElevenRUP.step65735 (p 50) (p 56) (p 2149) (h 2436) (h 2437) (h 66)

theorem derived65736 (p : Nat → Prop) (h : Inputs p) :
    (p 2150) :=
  ElevenRUP.step65736 (p 2149) (p 2150) (derived65735 p h) (h 2454)

theorem derived65737 (p : Nat → Prop) (h : Inputs p) :
    (p 4483) :=
  ElevenRUP.step65737 (p 2150) (p 4483) (derived65736 p h) (h 7035)

theorem derived65738 (p : Nat → Prop) (h : Inputs p) :
    (p 5790) :=
  ElevenRUP.step65738 (p 4483) (p 5790) (derived65737 p h) (h 11764)

theorem derived65739 (p : Nat → Prop) (h : Inputs p) :
    (p 2853) :=
  ElevenRUP.step65739 (p 722) (p 728) (p 2853) (h 3832) (h 3833) (h 794)

theorem derived65740 (p : Nat → Prop) (h : Inputs p) :
    (p 2854) :=
  ElevenRUP.step65740 (p 2853) (p 2854) (derived65739 p h) (h 3850)

theorem derived65741 (p : Nat → Prop) (h : Inputs p) :
    (p 4886) :=
  ElevenRUP.step65741 (p 2854) (p 4886) (derived65740 p h) (h 8064)

theorem derived65742 (p : Nat → Prop) (h : Inputs p) :
    (p 5934) :=
  ElevenRUP.step65742 (p 4886) (p 5934) (derived65741 p h) (h 12608)

theorem derived65745 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3744) ∨ (¬ p 2274) ∨ (¬ p 3872) ∨ (p 3690) :=
  ElevenRUP.step65745 (p 2274) (p 3690) (p 3744) (p 3872) (p 4187) (p 4396) (p 4618) (p 4619) (p 4622) (derived65720 p h) (h 33874) (h 19781) (h 7377) (h 7383) (h 7390)

theorem derived65746 (p : Nat → Prop) (h : Inputs p) :
    (p 2170) :=
  ElevenRUP.step65746 (p 74) (p 80) (p 2170) (h 2478) (h 2479) (h 92)

theorem derived65747 (p : Nat → Prop) (h : Inputs p) :
    (p 2171) :=
  ElevenRUP.step65747 (p 2170) (p 2171) (derived65746 p h) (h 2496)

theorem derived65748 (p : Nat → Prop) (h : Inputs p) :
    (p 4499) :=
  ElevenRUP.step65748 (p 2171) (p 4499) (derived65747 p h) (h 7069)

theorem derived65749 (p : Nat → Prop) (h : Inputs p) :
    (p 5796) :=
  ElevenRUP.step65749 (p 4499) (p 5796) (derived65748 p h) (h 11798)

theorem derived65751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4665) ∨ (¬ p 3146) ∨ (¬ p 4903) ∨ (¬ p 4107) ∨ (¬ p 4559) :=
  ElevenRUP.step65751 (p 2177) (p 2299) (p 3146) (p 3747) (p 4107) (p 4348) (p 4445) (p 4499) (p 4500) (p 4502) (p 4559) (p 4665) (p 4903) (p 4905) (derived65748 p h) (h 8094) (h 8091) (h 7480) (h 7481) (derived41698 p h) (derived41325 p h) (h 7062) (h 7056) (h 7068)

theorem derived65752 (p : Nat → Prop) (h : Inputs p) :
    (p 2300) :=
  ElevenRUP.step65752 (p 206) (p 212) (p 2300) (h 2734) (h 2735) (h 235)

theorem derived65753 (p : Nat → Prop) (h : Inputs p) :
    (p 2301) :=
  ElevenRUP.step65753 (p 2300) (p 2301) (derived65752 p h) (h 2752)

theorem derived65754 (p : Nat → Prop) (h : Inputs p) :
    (p 4573) :=
  ElevenRUP.step65754 (p 2301) (p 4573) (derived65753 p h) (h 7255)

theorem derived65756 (p : Nat → Prop) (h : Inputs p) :
    (p 2356) :=
  ElevenRUP.step65756 (p 254) (p 260) (p 2356) (h 2849) (h 2850) (h 287)

theorem derived65757 (p : Nat → Prop) (h : Inputs p) :
    (p 2357) :=
  ElevenRUP.step65757 (p 2356) (p 2357) (derived65756 p h) (h 2867)

theorem derived65758 (p : Nat → Prop) (h : Inputs p) :
    (p 4599) :=
  ElevenRUP.step65758 (p 2357) (p 4599) (derived65757 p h) (h 7339)

theorem derived65759 (p : Nat → Prop) (h : Inputs p) :
    (p 5835) :=
  ElevenRUP.step65759 (p 4599) (p 5835) (derived65758 p h) (h 12025)

theorem derived65761 (p : Nat → Prop) (h : Inputs p) :
    (p 2376) :=
  ElevenRUP.step65761 (p 278) (p 284) (p 2376) (h 2889) (h 2890) (h 313)

theorem derived65762 (p : Nat → Prop) (h : Inputs p) :
    (p 2377) :=
  ElevenRUP.step65762 (p 2376) (p 2377) (derived65761 p h) (h 2907)

theorem derived65763 (p : Nat → Prop) (h : Inputs p) :
    (p 4611) :=
  ElevenRUP.step65763 (p 2377) (p 4611) (derived65762 p h) (h 7374)

theorem derived65764 (p : Nat → Prop) (h : Inputs p) :
    (p 5841) :=
  ElevenRUP.step65764 (p 4611) (p 5841) (derived65763 p h) (h 12061)

theorem derived65765 (p : Nat → Prop) (h : Inputs p) :
    (p 2334) :=
  ElevenRUP.step65765 (p 230) (p 236) (p 2334) (h 2804) (h 2805) (h 261)

theorem derived65766 (p : Nat → Prop) (h : Inputs p) :
    (p 2335) :=
  ElevenRUP.step65766 (p 2334) (p 2335) (derived65765 p h) (h 2822)

theorem derived65767 (p : Nat → Prop) (h : Inputs p) :
    (p 4585) :=
  ElevenRUP.step65767 (p 2335) (p 4585) (derived65766 p h) (h 7305)

theorem derived65768 (p : Nat → Prop) (h : Inputs p) :
    (p 5829) :=
  ElevenRUP.step65768 (p 4585) (p 5829) (derived65767 p h) (h 11989)

theorem derived65769 (p : Nat → Prop) (h : Inputs p) :
    (p 2366) :=
  ElevenRUP.step65769 (p 266) (p 272) (p 2366) (h 2869) (h 2870) (h 300)

theorem derived65770 (p : Nat → Prop) (h : Inputs p) :
    (p 2367) :=
  ElevenRUP.step65770 (p 2366) (p 2367) (derived65769 p h) (h 2887)

end ElevenLogic
