import SunPrize.Certificate.Derived001
import SunPrize.Certificate.Logic002
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived42105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3583) ∨ (¬ p 4110) ∨ (¬ p 4185) ∨ (¬ p 4316) ∨ (¬ p 4705) :=
  ElevenRUP.step42105 (p 2027) (p 2829) (p 3583) (p 4110) (p 4185) (p 4316) (p 4705) (derived40810 p h) (h 11123)

theorem derived42106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 2996) ∨ (¬ p 3947) ∨ (¬ p 4666) ∨ (¬ p 5190) :=
  ElevenRUP.step42106 (p 2027) (p 2230) (p 2247) (p 2427) (p 2881) (p 2996) (p 3947) (p 4666) (p 5190) (derived40810 p h) (h 11124)

theorem derived42107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 3954) ∨ (¬ p 4242) ∨ (¬ p 4340) ∨ (¬ p 5190) :=
  ElevenRUP.step42107 (p 2027) (p 2230) (p 2427) (p 3246) (p 3950) (p 3954) (p 4242) (p 4340) (p 5190) (derived40810 p h) (h 11125)

theorem derived42109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2717) ∨ (¬ p 2782) ∨ (¬ p 3426) :=
  ElevenRUP.step42109 (p 2027) (p 2299) (p 2313) (p 2717) (p 2782) (p 3426) (derived40810 p h) (h 11127)

theorem derived42110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 3256) ∨ (¬ p 3949) ∨ (¬ p 4032) ∨ (¬ p 4043) :=
  ElevenRUP.step42110 (p 2027) (p 2220) (p 3256) (p 3949) (p 4032) (p 4043) (derived40810 p h) (h 11129)

theorem derived42111 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2440) ∨ (¬ p 3005) ∨ (¬ p 3361) ∨ (¬ p 4111) ∨ (¬ p 4346) ∨ (¬ p 4610) :=
  ElevenRUP.step42111 (p 2027) (p 2246) (p 2440) (p 3005) (p 3361) (p 4111) (p 4346) (p 4610) (derived40810 p h) (h 11130)

theorem derived42112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 4009) ∨ (¬ p 4121) ∨ (¬ p 4286) ∨ (¬ p 4610) :=
  ElevenRUP.step42112 (p 2027) (p 2440) (p 4009) (p 4121) (p 4286) (p 4610) (derived40810 p h) (h 11131)

theorem derived42114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2656) ∨ (¬ p 2685) ∨ (¬ p 3364) ∨ (¬ p 3684) ∨ (¬ p 4652) :=
  ElevenRUP.step42114 (p 2027) (p 2230) (p 2656) (p 2685) (p 3364) (p 3684) (p 4652) (derived40810 p h) (h 11133)

theorem derived42115 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3555) ∨ (¬ p 3692) ∨ (¬ p 3950) ∨ (¬ p 5190) :=
  ElevenRUP.step42115 (p 2027) (p 2191) (p 2396) (p 2553) (p 2573) (p 3555) (p 3692) (p 3950) (p 5190) (derived40810 p h) (h 11134)

theorem derived42116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2891) ∨ (¬ p 3876) ∨ (¬ p 4001) ∨ (¬ p 4632) :=
  ElevenRUP.step42116 (p 2027) (p 2850) (p 2891) (p 3876) (p 4001) (p 4632) (derived40810 p h) (h 11135)

theorem derived42118 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3486) ∨ (¬ p 4078) ∨ (¬ p 4185) ∨ (¬ p 4340) ∨ (¬ p 4496) ∨ (¬ p 4555) :=
  ElevenRUP.step42118 (p 2027) (p 3073) (p 3486) (p 4078) (p 4185) (p 4340) (p 4496) (p 4555) (derived40810 p h) (h 11137)

theorem derived42119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 5190) :=
  ElevenRUP.step42119 (p 2027) (p 2247) (p 2396) (p 2553) (p 2573) (p 3950) (p 4118) (p 4360) (p 5190) (derived40810 p h) (h 11138)

theorem derived42121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3371) ∨ (¬ p 3588) ∨ (¬ p 3694) ∨ (¬ p 4392) ∨ (¬ p 4778) :=
  ElevenRUP.step42121 (p 2027) (p 2166) (p 3371) (p 3588) (p 3694) (p 4392) (p 4778) (derived40810 p h) (h 11140)

theorem derived42122 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2573) ∨ (¬ p 4154) ∨ (¬ p 4389) ∨ (¬ p 5190) :=
  ElevenRUP.step42122 (p 2027) (p 2247) (p 2573) (p 4154) (p 4389) (p 5190) (derived40810 p h) (h 11141)

theorem derived42123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2588) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3564) ∨ (¬ p 3583) ∨ (¬ p 4208) ∨ (¬ p 4316) ∨ (¬ p 4368) ∨ (¬ p 4842) :=
  ElevenRUP.step42123 (p 2027) (p 2122) (p 2588) (p 2696) (p 2753) (p 3564) (p 3583) (p 4208) (p 4316) (p 4368) (p 4842) (derived40810 p h) (h 11142)

theorem derived42125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3949) ∨ (¬ p 3969) ∨ (¬ p 4385) ∨ (¬ p 5122) :=
  ElevenRUP.step42125 (p 2027) (p 2619) (p 3949) (p 3969) (p 4385) (p 5122) (derived40810 p h) (h 11144)

theorem derived42126 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3063) ∨ (¬ p 3585) ∨ (¬ p 4358) ∨ (¬ p 4749) ∨ (¬ p 4841) ∨ (¬ p 4869) :=
  ElevenRUP.step42126 (p 2027) (p 3063) (p 3585) (p 4358) (p 4749) (p 4841) (p 4869) (derived40810 p h) (h 11145)

theorem derived42127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3950) ∨ (¬ p 4118) ∨ (¬ p 4360) ∨ (¬ p 5190) :=
  ElevenRUP.step42127 (p 2027) (p 2230) (p 2247) (p 2427) (p 3246) (p 3950) (p 4118) (p 4360) (p 5190) (derived40810 p h) (h 11146)

theorem derived42128 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3954) ∨ (¬ p 4242) ∨ (¬ p 4521) ∨ (¬ p 5123) ∨ (¬ p 5612) :=
  ElevenRUP.step42128 (p 2027) (p 2761) (p 3051) (p 3246) (p 3954) (p 4242) (p 4521) (p 5123) (p 5612) (derived40810 p h) (h 11147)

theorem derived42129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2696) ∨ (¬ p 2778) ∨ (¬ p 4842) :=
  ElevenRUP.step42129 (p 2027) (p 2122) (p 2313) (p 2696) (p 2778) (p 4842) (derived40810 p h) (h 11148)

theorem derived42130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3549) ∨ (¬ p 4110) ∨ (¬ p 4356) ∨ (¬ p 4405) ∨ (¬ p 4441) ∨ (¬ p 5016) :=
  ElevenRUP.step42130 (p 2027) (p 2373) (p 3549) (p 4110) (p 4356) (p 4405) (p 4441) (p 5016) (derived40810 p h) (h 11149)

theorem derived42131 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2589) ∨ (¬ p 2696) ∨ (¬ p 3590) ∨ (¬ p 3905) ∨ (¬ p 4749) :=
  ElevenRUP.step42131 (p 2027) (p 2406) (p 2589) (p 2696) (p 3590) (p 3905) (p 4749) (derived40810 p h) (h 11150)

theorem derived42132 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3032) ∨ (¬ p 3527) ∨ (¬ p 3956) ∨ (¬ p 4138) ∨ (¬ p 4361) :=
  ElevenRUP.step42132 (p 2027) (p 2553) (p 3032) (p 3527) (p 3956) (p 4138) (p 4361) (derived40810 p h) (h 11151)

theorem derived42133 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (¬ p 3055) ∨ (¬ p 3572) ∨ (¬ p 4117) ∨ (¬ p 4749) :=
  ElevenRUP.step42133 (p 2027) (p 2807) (p 3055) (p 3572) (p 4117) (p 4749) (derived40810 p h) (h 11152)

theorem derived42135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3093) ∨ (¬ p 3115) ∨ (¬ p 3136) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4450) ∨ (¬ p 4870) :=
  ElevenRUP.step42135 (p 2027) (p 2696) (p 2753) (p 3093) (p 3115) (p 3136) (p 3860) (p 4261) (p 4450) (p 4870) (derived40810 p h) (h 11154)

theorem derived42136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 2850) ∨ (¬ p 2982) ∨ (¬ p 3093) ∨ (¬ p 4107) ∨ (¬ p 4366) ∨ (¬ p 4395) ∨ (¬ p 4427) ∨ (¬ p 4870) :=
  ElevenRUP.step42136 (p 2027) (p 2598) (p 2753) (p 2850) (p 2982) (p 3093) (p 4107) (p 4366) (p 4395) (p 4427) (p 4870) (derived40810 p h) (h 11155)

theorem derived42137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 2850) ∨ (¬ p 2982) ∨ (¬ p 3549) ∨ (¬ p 4348) ∨ (¬ p 4450) ∨ (¬ p 4870) :=
  ElevenRUP.step42137 (p 2027) (p 2299) (p 2598) (p 2753) (p 2850) (p 2982) (p 3549) (p 4348) (p 4450) (p 4870) (derived40810 p h) (h 11156)

theorem derived42140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2373) ∨ (¬ p 3860) ∨ (¬ p 3906) ∨ (¬ p 4629) :=
  ElevenRUP.step42140 (p 2027) (p 2210) (p 2373) (p 3860) (p 3906) (p 4629) (derived40810 p h) (h 11159)

theorem derived42141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2930) ∨ (¬ p 3399) ∨ (¬ p 3834) ∨ (¬ p 5358) :=
  ElevenRUP.step42141 (p 2027) (p 2417) (p 2930) (p 3399) (p 3834) (p 5358) (derived40810 p h) (h 11160)

theorem derived42143 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2630) ∨ (¬ p 2668) ∨ (¬ p 2785) ∨ (¬ p 4841) ∨ (¬ p 4972) :=
  ElevenRUP.step42143 (p 2027) (p 2387) (p 2630) (p 2668) (p 2785) (p 4841) (p 4972) (derived40810 p h) (h 11162)

theorem derived42144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3096) ∨ (¬ p 3564) ∨ (¬ p 3989) ∨ (¬ p 4340) ∨ (¬ p 4345) ∨ (¬ p 4859) :=
  ElevenRUP.step42144 (p 2027) (p 3096) (p 3564) (p 3989) (p 4340) (p 4345) (p 4859) (derived40810 p h) (h 11166)

theorem derived42145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3438) ∨ (¬ p 3449) ∨ (¬ p 3834) ∨ (¬ p 4995) :=
  ElevenRUP.step42145 (p 2027) (p 2363) (p 3438) (p 3449) (p 3834) (p 4995) (derived40810 p h) (h 11168)

theorem derived42146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 2982) ∨ (¬ p 3857) ∨ (¬ p 3880) ∨ (¬ p 4529) :=
  ElevenRUP.step42146 (p 2027) (p 2532) (p 2982) (p 3857) (p 3880) (p 4529) (derived40810 p h) (h 11169)

theorem derived42147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 3343) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4332) ∨ (¬ p 4348) :=
  ElevenRUP.step42147 (p 2027) (p 2145) (p 2630) (p 2696) (p 3343) (p 3556) (p 3570) (p 4332) (p 4348) (derived40810 p h) (h 11170)

theorem derived42148 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2406) ∨ (¬ p 3292) ∨ (¬ p 3379) ∨ (¬ p 4949) ∨ (¬ p 5171) :=
  ElevenRUP.step42148 (p 2027) (p 2245) (p 2406) (p 3292) (p 3379) (p 4949) (p 5171) (derived40810 p h) (h 11171)

theorem derived42149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3193) ∨ (¬ p 3452) ∨ (¬ p 4210) ∨ (¬ p 4512) ∨ (¬ p 4949) :=
  ElevenRUP.step42149 (p 2027) (p 3093) (p 3193) (p 3452) (p 4210) (p 4512) (p 4949) (derived40810 p h) (h 11172)

theorem derived42150 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2598) ∨ (¬ p 3556) ∨ (¬ p 3641) ∨ (¬ p 3690) ∨ (¬ p 4149) ∨ (¬ p 4381) ∨ (¬ p 5119) :=
  ElevenRUP.step42150 (p 2027) (p 2145) (p 2598) (p 3556) (p 3641) (p 3690) (p 4149) (p 4381) (p 5119) (derived40810 p h) (h 11174)

theorem derived42151 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 2952) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 3952) ∨ (¬ p 4393) ∨ (¬ p 5254) :=
  ElevenRUP.step42151 (p 2027) (p 2252) (p 2750) (p 2753) (p 2761) (p 2952) (p 3434) (p 3471) (p 3952) (p 4393) (p 5254) (derived40810 p h) (h 11175)

theorem derived42152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 4053) ∨ (¬ p 4366) ∨ (¬ p 4427) ∨ (¬ p 5477) :=
  ElevenRUP.step42152 (p 2027) (p 3093) (p 4053) (p 4366) (p 4427) (p 5477) (derived40810 p h) (h 11176)

theorem derived42154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3434) ∨ (¬ p 3527) ∨ (¬ p 3659) ∨ (¬ p 3687) ∨ (¬ p 3744) ∨ (¬ p 3952) ∨ (¬ p 4625) :=
  ElevenRUP.step42154 (p 2027) (p 2252) (p 2750) (p 2952) (p 3434) (p 3527) (p 3659) (p 3687) (p 3744) (p 3952) (p 4625) (derived40810 p h) (h 11178)

theorem derived42158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2109) ∨ (¬ p 2839) ∨ (¬ p 3156) ∨ (¬ p 3696) ∨ (¬ p 4242) ∨ (¬ p 4906) :=
  ElevenRUP.step42158 (p 2027) (p 2109) (p 2839) (p 3156) (p 3696) (p 4242) (p 4906) (derived40810 p h) (h 11182)

theorem derived42159 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 2950) ∨ (¬ p 3055) ∨ (¬ p 3646) ∨ (¬ p 3744) ∨ (¬ p 4019) ∨ (¬ p 4191) ∨ (¬ p 4749) ∨ (¬ p 5119) :=
  ElevenRUP.step42159 (p 2027) (p 2098) (p 2252) (p 2748) (p 2950) (p 3055) (p 3646) (p 3744) (p 4019) (p 4191) (p 4749) (p 5119) (derived40810 p h) (h 11183)

theorem derived42161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3156) ∨ (¬ p 3204) ∨ (¬ p 3969) ∨ (¬ p 4197) ∨ (¬ p 4512) ∨ (¬ p 4957) ∨ (¬ p 5590) :=
  ElevenRUP.step42161 (p 2027) (p 3156) (p 3204) (p 3969) (p 4197) (p 4512) (p 4957) (p 5590) (derived40810 p h) (h 11185)

theorem derived42162 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3413) ∨ (¬ p 3646) ∨ (¬ p 4031) ∨ (¬ p 4256) ∨ (¬ p 4608) :=
  ElevenRUP.step42162 (p 2027) (p 2284) (p 3413) (p 3646) (p 4031) (p 4256) (p 4608) (derived40810 p h) (h 11186)

theorem derived42163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2737) ∨ (¬ p 3641) ∨ (¬ p 4257) ∨ (¬ p 4749) :=
  ElevenRUP.step42163 (p 2027) (p 2509) (p 2737) (p 3641) (p 4257) (p 4749) (derived40810 p h) (h 11187)

theorem derived42164 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 2963) ∨ (¬ p 3055) ∨ (¬ p 3324) ∨ (¬ p 4019) ∨ (¬ p 4347) ∨ (¬ p 4749) ∨ (¬ p 5122) :=
  ElevenRUP.step42164 (p 2027) (p 2098) (p 2252) (p 2748) (p 2963) (p 3055) (p 3324) (p 4019) (p 4347) (p 4749) (p 5122) (derived40810 p h) (h 11188)

theorem derived42165 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3115) ∨ (¬ p 3576) ∨ (¬ p 3817) ∨ (¬ p 4135) ∨ (¬ p 4320) ∨ (¬ p 4895) :=
  ElevenRUP.step42165 (p 2027) (p 3115) (p 3576) (p 3817) (p 4135) (p 4320) (p 4895) (derived40810 p h) (h 11189)

theorem derived42168 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2745) ∨ (¬ p 2797) ∨ (¬ p 3567) ∨ (¬ p 4114) ∨ (¬ p 4261) ∨ (¬ p 4262) :=
  ElevenRUP.step42168 (p 2027) (p 2088) (p 2745) (p 2797) (p 3567) (p 4114) (p 4261) (p 4262) (derived40810 p h) (h 11192)

theorem derived42169 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2497) ∨ (¬ p 2498) ∨ (¬ p 2573) ∨ (¬ p 3684) ∨ (¬ p 4730) :=
  ElevenRUP.step42169 (p 2027) (p 2406) (p 2497) (p 2498) (p 2573) (p 3684) (p 4730) (derived40810 p h) (h 11193)

theorem derived42170 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2459) ∨ (¬ p 2750) ∨ (¬ p 3172) ∨ (¬ p 3379) ∨ (¬ p 3641) ∨ (¬ p 3954) ∨ (¬ p 4030) ∨ (¬ p 4118) ∨ (¬ p 4420) :=
  ElevenRUP.step42170 (p 2027) (p 2252) (p 2459) (p 2750) (p 3172) (p 3379) (p 3641) (p 3954) (p 4030) (p 4118) (p 4420) (derived40810 p h) (h 11194)

theorem derived42173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3551) ∨ (¬ p 3587) ∨ (¬ p 4235) ∨ (¬ p 4283) ∨ (¬ p 4885) :=
  ElevenRUP.step42173 (p 2027) (p 2717) (p 3551) (p 3587) (p 4235) (p 4283) (p 4885) (derived40810 p h) (h 11197)

theorem derived42174 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3587) ∨ (¬ p 4235) ∨ (¬ p 4253) ∨ (¬ p 4885) ∨ (¬ p 5660) :=
  ElevenRUP.step42174 (p 2027) (p 3587) (p 4235) (p 4253) (p 4885) (p 5660) (derived40810 p h) (h 11198)

theorem derived42175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3483) ∨ (¬ p 4033) ∨ (¬ p 4208) ∨ (¬ p 4241) ∨ (¬ p 4401) :=
  ElevenRUP.step42175 (p 2027) (p 2563) (p 3483) (p 4033) (p 4208) (p 4241) (p 4401) (derived40810 p h) (h 11199)

theorem derived42176 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3880) ∨ (¬ p 4446) ∨ (¬ p 4632) :=
  ElevenRUP.step42176 (p 2027) (p 3449) (p 3555) (p 3880) (p 4446) (p 4632) (derived40810 p h) (h 11200)

theorem derived42177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2474) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 3857) ∨ (¬ p 5191) :=
  ElevenRUP.step42177 (p 2027) (p 2474) (p 2518) (p 2528) (p 3857) (p 5191) (derived40810 p h) (h 11201)

theorem derived42178 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2819) ∨ (¬ p 2957) ∨ (¬ p 4120) ∨ (¬ p 4401) ∨ (¬ p 4506) :=
  ElevenRUP.step42178 (p 2027) (p 2284) (p 2819) (p 2957) (p 4120) (p 4401) (p 4506) (derived40810 p h) (h 11203)

theorem derived42181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3599) ∨ (¬ p 4242) ∨ (¬ p 4348) ∨ (¬ p 4807) ∨ (¬ p 5343) :=
  ElevenRUP.step42181 (p 2027) (p 3599) (p 4242) (p 4348) (p 4807) (p 5343) (derived40810 p h) (h 11206)

theorem derived42184 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3212) ∨ (¬ p 3519) ∨ (¬ p 3680) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 4261) ∨ (¬ p 4376) ∨ (¬ p 4381) ∨ (¬ p 4399) :=
  ElevenRUP.step42184 (p 2027) (p 2608) (p 3212) (p 3519) (p 3680) (p 3860) (p 3950) (p 4261) (p 4376) (p 4381) (p 4399) (derived40810 p h) (h 11209)

theorem derived42186 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4370) ∨ (¬ p 4608) :=
  ElevenRUP.step42186 (p 2027) (p 2406) (p 3379) (p 3860) (p 4370) (p 4608) (derived40810 p h) (h 11211)

theorem derived42187 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2749) ∨ (¬ p 3585) ∨ (¬ p 4195) ∨ (¬ p 4749) :=
  ElevenRUP.step42187 (p 2027) (p 2641) (p 2749) (p 3585) (p 4195) (p 4749) (derived40810 p h) (h 11212)

theorem derived42188 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3266) ∨ (¬ p 3657) ∨ (¬ p 4041) ∨ (¬ p 4191) ∨ (¬ p 4623) :=
  ElevenRUP.step42188 (p 2027) (p 3256) (p 3266) (p 3657) (p 4041) (p 4191) (p 4623) (derived40810 p h) (h 11213)

theorem derived42191 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2501) ∨ (¬ p 3093) ∨ (¬ p 3860) ∨ (¬ p 4993) :=
  ElevenRUP.step42191 (p 2027) (p 2352) (p 2501) (p 3093) (p 3860) (p 4993) (derived40810 p h) (h 11216)

theorem derived42192 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 3449) ∨ (¬ p 4366) ∨ (¬ p 5145) ∨ (¬ p 5307) :=
  ElevenRUP.step42192 (p 2027) (p 2299) (p 3449) (p 4366) (p 5145) (p 5307) (derived40810 p h) (h 11217)

theorem derived42193 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3555) ∨ (¬ p 3952) ∨ (¬ p 4516) ∨ (¬ p 4960) :=
  ElevenRUP.step42193 (p 2027) (p 3093) (p 3555) (p 3952) (p 4516) (p 4960) (derived40810 p h) (h 11218)

theorem derived42194 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2501) ∨ (¬ p 3093) ∨ (¬ p 3564) ∨ (¬ p 3834) ∨ (¬ p 5148) :=
  ElevenRUP.step42194 (p 2027) (p 2501) (p 3093) (p 3564) (p 3834) (p 5148) (derived40810 p h) (h 11219)

theorem derived42195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2476) ∨ (¬ p 4110) ∨ (¬ p 4399) ∨ (¬ p 4608) :=
  ElevenRUP.step42195 (p 2027) (p 2156) (p 2476) (p 4110) (p 4399) (p 4608) (derived40810 p h) (h 11220)

theorem derived42196 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2509) ∨ (¬ p 3452) ∨ (¬ p 4210) ∨ (¬ p 4608) :=
  ElevenRUP.step42196 (p 2027) (p 2210) (p 2509) (p 3452) (p 4210) (p 4608) (derived40810 p h) (h 11221)

theorem derived42197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2982) ∨ (¬ p 3904) ∨ (¬ p 4032) ∨ (¬ p 4717) :=
  ElevenRUP.step42197 (p 2027) (p 2573) (p 2982) (p 3904) (p 4032) (p 4717) (derived40810 p h) (h 11222)

theorem derived42198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2210) ∨ (¬ p 2311) ∨ (¬ p 2972) ∨ (¬ p 3204) ∨ (¬ p 3551) ∨ (¬ p 3954) ∨ (¬ p 4107) ∨ (¬ p 4395) ∨ (¬ p 4870) :=
  ElevenRUP.step42198 (p 2027) (p 2177) (p 2210) (p 2311) (p 2972) (p 3204) (p 3551) (p 3954) (p 4107) (p 4395) (p 4870) (derived40810 p h) (h 11223)

theorem derived42199 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 3051) ∨ (¬ p 4109) ∨ (¬ p 4320) ∨ (¬ p 4700) ∨ (¬ p 4717) :=
  ElevenRUP.step42199 (p 2027) (p 3016) (p 3051) (p 4109) (p 4320) (p 4700) (p 4717) (derived40810 p h) (h 11224)

theorem derived42200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2717) ∨ (¬ p 3551) ∨ (¬ p 3820) ∨ (¬ p 4778) :=
  ElevenRUP.step42200 (p 2027) (p 2696) (p 2717) (p 3551) (p 3820) (p 4778) (derived40810 p h) (h 11225)

theorem derived42201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2928) ∨ (¬ p 3551) ∨ (¬ p 3580) ∨ (¬ p 4279) ∨ (¬ p 4811) :=
  ElevenRUP.step42201 (p 2027) (p 2264) (p 2928) (p 3551) (p 3580) (p 4279) (p 4811) (derived40810 p h) (h 11226)

theorem derived42202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3551) ∨ (¬ p 3742) ∨ (¬ p 4279) ∨ (¬ p 4753) ∨ (¬ p 5085) :=
  ElevenRUP.step42202 (p 2027) (p 2717) (p 3551) (p 3742) (p 4279) (p 4753) (p 5085) (derived40810 p h) (h 11227)

theorem derived42203 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2542) ∨ (¬ p 2860) ∨ (¬ p 3574) ∨ (¬ p 3743) ∨ (¬ p 4885) :=
  ElevenRUP.step42203 (p 2027) (p 2386) (p 2542) (p 2860) (p 3574) (p 3743) (p 4885) (derived40810 p h) (h 11228)

theorem derived42204 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2870) ∨ (¬ p 3556) ∨ (¬ p 3582) ∨ (¬ p 4031) ∨ (¬ p 4753) :=
  ElevenRUP.step42204 (p 2027) (p 2440) (p 2870) (p 3556) (p 3582) (p 4031) (p 4753) (derived40810 p h) (h 11229)

theorem derived42205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2741) ∨ (¬ p 2946) ∨ (¬ p 3452) ∨ (¬ p 3662) ∨ (¬ p 4376) :=
  ElevenRUP.step42205 (p 2027) (p 2253) (p 2741) (p 2946) (p 3452) (p 3662) (p 4376) (derived40810 p h) (h 11230)

theorem derived42206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2417) ∨ (¬ p 3365) ∨ (¬ p 3644) ∨ (¬ p 4037) ∨ (¬ p 4195) ∨ (¬ p 4625) ∨ (¬ p 5257) :=
  ElevenRUP.step42206 (p 2027) (p 2341) (p 2417) (p 3365) (p 3644) (p 4037) (p 4195) (p 4625) (p 5257) (derived40810 p h) (h 11231)

theorem derived42207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3452) ∨ (¬ p 4172) ∨ (¬ p 4173) ∨ (¬ p 4376) ∨ (¬ p 4874) :=
  ElevenRUP.step42207 (p 2027) (p 2156) (p 3452) (p 4172) (p 4173) (p 4376) (p 4874) (derived40810 p h) (h 11232)

theorem derived42208 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3323) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3744) ∨ (¬ p 4336) ∨ (¬ p 4957) :=
  ElevenRUP.step42208 (p 2027) (p 3323) (p 3645) (p 3646) (p 3744) (p 4336) (p 4957) (derived40810 p h) (h 11233)

theorem derived42209 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3266) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4195) ∨ (¬ p 4376) ∨ (¬ p 5254) ∨ (¬ p 5717) :=
  ElevenRUP.step42209 (p 2027) (p 2470) (p 2528) (p 3266) (p 3365) (p 3366) (p 3519) (p 4195) (p 4376) (p 5254) (p 5717) (derived40810 p h) (h 11234)

theorem derived42210 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3497) ∨ (¬ p 3737) ∨ (¬ p 4506) ∨ (¬ p 5586) :=
  ElevenRUP.step42210 (p 2027) (p 2284) (p 3497) (p 3737) (p 4506) (p 5586) (derived40810 p h) (h 11235)

theorem derived42211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 4366) ∨ (¬ p 4555) ∨ (¬ p 4909) :=
  ElevenRUP.step42211 (p 2027) (p 2192) (p 2210) (p 4366) (p 4555) (p 4909) (derived40810 p h) (h 11236)

theorem derived42212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 3877) ∨ (¬ p 4228) ∨ (¬ p 4769) ∨ (¬ p 5586) :=
  ElevenRUP.step42212 (p 2027) (p 2797) (p 3877) (p 4228) (p 4769) (p 5586) (derived40810 p h) (h 11237)

theorem derived42213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2745) ∨ (¬ p 3005) ∨ (¬ p 3860) ∨ (¬ p 5074) :=
  ElevenRUP.step42213 (p 2027) (p 2241) (p 2745) (p 3005) (p 3860) (p 5074) (derived40810 p h) (h 11238)

theorem derived42215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2995) ∨ (¬ p 3551) ∨ (¬ p 4235) ∨ (¬ p 4283) ∨ (¬ p 4705) :=
  ElevenRUP.step42215 (p 2027) (p 2264) (p 2995) (p 3551) (p 4235) (p 4283) (p 4705) (derived40810 p h) (h 11241)

theorem derived42216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 3555) ∨ (¬ p 4079) ∨ (¬ p 4257) ∨ (¬ p 4377) :=
  ElevenRUP.step42216 (p 2027) (p 2499) (p 2573) (p 3555) (p 4079) (p 4257) (p 4377) (derived40810 p h) (h 11242)

theorem derived42222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 3830) ∨ (¬ p 4107) ∨ (¬ p 4361) ∨ (¬ p 4366) ∨ (¬ p 5362) :=
  ElevenRUP.step42222 (p 2027) (p 3032) (p 3830) (p 4107) (p 4361) (p 4366) (p 5362) (derived40810 p h) (h 11250)

theorem derived42225 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3093) ∨ (¬ p 3860) ∨ (¬ p 4867) ∨ (¬ p 4993) :=
  ElevenRUP.step42225 (p 2027) (p 2819) (p 3093) (p 3860) (p 4867) (p 4993) (derived40810 p h) (h 11253)

theorem derived42226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2782) ∨ (¬ p 2819) ∨ (¬ p 3979) ∨ (¬ p 4197) ∨ (¬ p 5590) :=
  ElevenRUP.step42226 (p 2027) (p 2782) (p 2819) (p 3979) (p 4197) (p 5590) (derived40810 p h) (h 11254)

theorem derived42227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) ∨ (¬ p 5307) :=
  ElevenRUP.step42227 (p 2027) (p 3449) (p 3817) (p 4366) (p 4666) (p 5307) (derived40810 p h) (h 11255)

theorem derived42228 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2778) ∨ (¬ p 2819) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3917) ∨ (¬ p 4381) ∨ (¬ p 4419) ∨ (¬ p 4625) :=
  ElevenRUP.step42228 (p 2027) (p 2387) (p 2778) (p 2819) (p 3276) (p 3355) (p 3917) (p 4381) (p 4419) (p 4625) (derived40810 p h) (h 11256)

theorem derived42229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3073) ∨ (¬ p 3857) ∨ (¬ p 4416) ∨ (¬ p 5312) :=
  ElevenRUP.step42229 (p 2027) (p 2608) (p 3073) (p 3857) (p 4416) (p 5312) (derived40810 p h) (h 11257)

theorem derived42230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2741) ∨ (¬ p 3166) ∨ (¬ p 3452) ∨ (¬ p 4360) ∨ (¬ p 4376) :=
  ElevenRUP.step42230 (p 2027) (p 2253) (p 2741) (p 3166) (p 3452) (p 4360) (p 4376) (derived40810 p h) (h 11258)

theorem derived42231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3189) ∨ (¬ p 3452) ∨ (¬ p 4116) ∨ (¬ p 5011) :=
  ElevenRUP.step42231 (p 2027) (p 2241) (p 3189) (p 3452) (p 4116) (p 5011) (derived40810 p h) (h 11259)

theorem derived42232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2741) ∨ (¬ p 3286) ∨ (¬ p 3452) ∨ (¬ p 3848) ∨ (¬ p 4376) :=
  ElevenRUP.step42232 (p 2027) (p 2253) (p 2741) (p 3286) (p 3452) (p 3848) (p 4376) (derived40810 p h) (h 11260)

theorem derived42233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3452) ∨ (¬ p 3842) ∨ (¬ p 4116) ∨ (¬ p 5177) :=
  ElevenRUP.step42233 (p 2027) (p 2241) (p 3452) (p 3842) (p 4116) (p 5177) (derived40810 p h) (h 11261)

theorem derived42234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 3688) ∨ (¬ p 3917) ∨ (¬ p 3954) ∨ (¬ p 4604) ∨ (¬ p 5190) :=
  ElevenRUP.step42234 (p 2027) (p 2459) (p 2911) (p 3389) (p 3688) (p 3917) (p 3954) (p 4604) (p 5190) (derived40810 p h) (h 11262)

theorem derived42235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3256) ∨ (¬ p 3860) ∨ (¬ p 4041) ∨ (¬ p 4261) ∨ (¬ p 5190) :=
  ElevenRUP.step42235 (p 2027) (p 2230) (p 2427) (p 2881) (p 3256) (p 3860) (p 4041) (p 4261) (p 5190) (derived40810 p h) (h 11263)

theorem derived42236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2534) ∨ (¬ p 3573) ∨ (¬ p 3888) ∨ (¬ p 5586) :=
  ElevenRUP.step42236 (p 2027) (p 2363) (p 2534) (p 3573) (p 3888) (p 5586) (derived40810 p h) (h 11264)

theorem derived42237 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3519) ∨ (¬ p 3590) ∨ (¬ p 4129) ∨ (¬ p 4379) ∨ (¬ p 4749) ∨ (¬ p 4826) ∨ (¬ p 5387) :=
  ElevenRUP.step42237 (p 2027) (p 2230) (p 2427) (p 2696) (p 2753) (p 3519) (p 3590) (p 4129) (p 4379) (p 4749) (p 4826) (p 5387) (derived40810 p h) (h 11265)

theorem derived42242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2963) ∨ (¬ p 3641) ∨ (¬ p 4037) ∨ (¬ p 4149) ∨ (¬ p 4191) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step42242 (p 2027) (p 2598) (p 2963) (p 3641) (p 4037) (p 4149) (p 4191) (p 4789) (p 5119) (derived40810 p h) (h 11273)

theorem derived42243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2608) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3591) ∨ (¬ p 4026) ∨ (¬ p 4376) ∨ (¬ p 4604) :=
  ElevenRUP.step42243 (p 2027) (p 2459) (p 2608) (p 2911) (p 2922) (p 3591) (p 4026) (p 4376) (p 4604) (derived40810 p h) (h 11274)

theorem derived42246 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3583) ∨ (¬ p 3599) ∨ (¬ p 4885) ∨ (¬ p 4948) ∨ (¬ p 5030) :=
  ElevenRUP.step42246 (p 2027) (p 3583) (p 3599) (p 4885) (p 4948) (p 5030) (derived40810 p h) (h 11277)

theorem derived42247 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2553) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3096) ∨ (¬ p 3519) ∨ (¬ p 3590) ∨ (¬ p 3791) ∨ (¬ p 4379) ∨ (¬ p 4399) ∨ (¬ p 4749) ∨ (¬ p 4826) ∨ (¬ p 5387) :=
  ElevenRUP.step42247 (p 2027) (p 2156) (p 2553) (p 2696) (p 2753) (p 3096) (p 3519) (p 3590) (p 3791) (p 4379) (p 4399) (p 4749) (p 4826) (p 5387) (derived40810 p h) (h 11278)

theorem derived42248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 3689) ∨ (¬ p 4075) ∨ (¬ p 4185) ∨ (¬ p 4405) ∨ (¬ p 4423) ∨ (¬ p 4427) :=
  ElevenRUP.step42248 (p 2027) (p 2187) (p 3689) (p 4075) (p 4185) (p 4405) (p 4423) (p 4427) (derived40810 p h) (h 11279)

theorem derived42249 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2441) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 4278) ∨ (¬ p 4885) :=
  ElevenRUP.step42249 (p 2027) (p 2137) (p 2441) (p 3051) (p 3246) (p 4278) (p 4885) (derived40810 p h) (h 11280)

theorem derived42252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 2751) ∨ (¬ p 3758) ∨ (¬ p 4392) ∨ (¬ p 4399) :=
  ElevenRUP.step42252 (p 2027) (p 2156) (p 2656) (p 2727) (p 2751) (p 3758) (p 4392) (p 4399) (derived40810 p h) (h 11283)

theorem derived42255 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3631) ∨ (¬ p 3821) ∨ (¬ p 4235) ∨ (¬ p 4283) ∨ (¬ p 4338) ∨ (¬ p 4452) ∨ (¬ p 4632) :=
  ElevenRUP.step42255 (p 2027) (p 3631) (p 3821) (p 4235) (p 4283) (p 4338) (p 4452) (p 4632) (derived40810 p h) (h 11286)

theorem derived42256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2839) ∨ (¬ p 3688) ∨ (¬ p 4428) ∨ (¬ p 4906) :=
  ElevenRUP.step42256 (p 2027) (p 2284) (p 2839) (p 3688) (p 4428) (p 4906) (derived40810 p h) (h 11287)

theorem derived42257 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2819) ∨ (¬ p 3923) ∨ (¬ p 3953) ∨ (¬ p 4842) :=
  ElevenRUP.step42257 (p 2027) (p 2737) (p 2819) (p 3923) (p 3953) (p 4842) (derived40810 p h) (h 11288)

theorem derived42258 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2807) ∨ (¬ p 2950) ∨ (¬ p 3413) ∨ (¬ p 3646) ∨ (¬ p 4652) :=
  ElevenRUP.step42258 (p 2027) (p 2284) (p 2807) (p 2950) (p 3413) (p 3646) (p 4652) (derived40810 p h) (h 11289)

theorem derived42259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2528) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4438) ∨ (¬ p 4789) :=
  ElevenRUP.step42259 (p 2027) (p 2132) (p 2528) (p 2870) (p 2881) (p 3172) (p 4118) (p 4438) (p 4789) (derived40810 p h) (h 11290)

theorem derived42260 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3227) ∨ (¬ p 3343) ∨ (¬ p 3379) ∨ (¬ p 3834) ∨ (¬ p 4811) :=
  ElevenRUP.step42260 (p 2027) (p 3227) (p 3343) (p 3379) (p 3834) (p 4811) (derived40810 p h) (h 11292)

theorem derived42261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4370) ∨ (¬ p 4811) :=
  ElevenRUP.step42261 (p 2027) (p 3083) (p 3379) (p 3860) (p 4370) (p 4811) (derived40810 p h) (h 11294)

theorem derived42262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2252) ∨ (¬ p 2396) ∨ (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2829) ∨ (¬ p 3951) ∨ (¬ p 4948) :=
  ElevenRUP.step42262 (p 2027) (p 2122) (p 2252) (p 2396) (p 2440) (p 2657) (p 2750) (p 2829) (p 3951) (p 4948) (derived40810 p h) (h 11295)

theorem derived42263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3359) ∨ (¬ p 3979) ∨ (¬ p 4425) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step42263 (p 2027) (p 2657) (p 2774) (p 2819) (p 3359) (p 3979) (p 4425) (p 4789) (p 5119) (derived40810 p h) (h 11296)

theorem derived42264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3834) ∨ (¬ p 3979) ∨ (¬ p 4321) ∨ (¬ p 5119) :=
  ElevenRUP.step42264 (p 2027) (p 2241) (p 2750) (p 2753) (p 2774) (p 2819) (p 3834) (p 3979) (p 4321) (p 5119) (derived40810 p h) (h 11297)

theorem derived42265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 3868) ∨ (¬ p 4256) ∨ (¬ p 4383) ∨ (¬ p 5564) :=
  ElevenRUP.step42265 (p 2027) (p 2437) (p 3868) (p 4256) (p 4383) (p 5564) (derived40810 p h) (h 11299)

theorem derived42266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2761) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 4789) ∨ (¬ p 5123) :=
  ElevenRUP.step42266 (p 2027) (p 2657) (p 2761) (p 3434) (p 3471) (p 4256) (p 4286) (p 4789) (p 5123) (derived40810 p h) (h 11300)

theorem derived42267 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2829) ∨ (¬ p 2952) ∨ (¬ p 3461) ∨ (¬ p 3483) ∨ (¬ p 3497) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step42267 (p 2027) (p 2252) (p 2750) (p 2829) (p 2952) (p 3461) (p 3483) (p 3497) (p 5123) (p 5568) (derived40810 p h) (h 11301)

theorem derived42268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2829) ∨ (¬ p 3461) ∨ (¬ p 3483) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 5123) :=
  ElevenRUP.step42268 (p 2027) (p 2252) (p 2657) (p 2750) (p 2829) (p 3461) (p 3483) (p 4256) (p 4286) (p 5123) (derived40810 p h) (h 11302)

theorem derived42269 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3591) ∨ (¬ p 3830) ∨ (¬ p 3917) ∨ (¬ p 4871) ∨ (¬ p 5152) :=
  ElevenRUP.step42269 (p 2027) (p 3591) (p 3830) (p 3917) (p 4871) (p 5152) (derived40810 p h) (h 11303)

theorem derived42270 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 2819) ∨ (¬ p 3550) ∨ (¬ p 3821) ∨ (¬ p 3822) ∨ (¬ p 4666) :=
  ElevenRUP.step42270 (p 2027) (p 2318) (p 2819) (p 3550) (p 3821) (p 3822) (p 4666) (derived40810 p h) (h 11304)

theorem derived42271 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2252) ∨ (¬ p 2396) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3292) ∨ (¬ p 3680) ∨ (¬ p 3951) ∨ (¬ p 5284) :=
  ElevenRUP.step42271 (p 2027) (p 2122) (p 2252) (p 2396) (p 2750) (p 2753) (p 2774) (p 3292) (p 3680) (p 3951) (p 5284) (derived40810 p h) (h 11305)

theorem derived42273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2952) ∨ (¬ p 3449) ∨ (¬ p 3497) ∨ (¬ p 3692) ∨ (¬ p 3954) ∨ (¬ p 4181) ∨ (¬ p 5122) :=
  ElevenRUP.step42273 (p 2027) (p 2252) (p 2750) (p 2952) (p 3449) (p 3497) (p 3692) (p 3954) (p 4181) (p 5122) (derived40810 p h) (h 11307)

theorem derived42274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 3073) ∨ (¬ p 3857) ∨ (¬ p 4416) ∨ (¬ p 5316) :=
  ElevenRUP.step42274 (p 2027) (p 2241) (p 2750) (p 3073) (p 3857) (p 4416) (p 5316) (derived40810 p h) (h 11308)

theorem derived42275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 4318) ∨ (¬ p 4358) ∨ (¬ p 4871) :=
  ElevenRUP.step42275 (p 2027) (p 3449) (p 3591) (p 4318) (p 4358) (p 4871) (derived40810 p h) (h 11309)

theorem derived42276 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2780) ∨ (¬ p 2829) ∨ (¬ p 3873) :=
  ElevenRUP.step42276 (p 2027) (p 2241) (p 2750) (p 2780) (p 2829) (p 3873) (derived40810 p h) (h 11310)

theorem derived42277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2786) ∨ (¬ p 3292) ∨ (¬ p 3483) ∨ (¬ p 3680) ∨ (¬ p 4358) ∨ (¬ p 4368) ∨ (¬ p 4789) ∨ (¬ p 5284) :=
  ElevenRUP.step42277 (p 2027) (p 2383) (p 2786) (p 3292) (p 3483) (p 3680) (p 4358) (p 4368) (p 4789) (p 5284) (derived40810 p h) (h 11311)

theorem derived42278 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3834) ∨ (¬ p 3941) ∨ (¬ p 4321) ∨ (¬ p 5119) :=
  ElevenRUP.step42278 (p 2027) (p 2241) (p 2717) (p 2750) (p 2753) (p 3471) (p 3834) (p 3941) (p 4321) (p 5119) (derived40810 p h) (h 11312)

theorem derived42279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2383) ∨ (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2786) ∨ (¬ p 3483) ∨ (¬ p 4358) ∨ (¬ p 4368) ∨ (¬ p 4948) :=
  ElevenRUP.step42279 (p 2027) (p 2252) (p 2383) (p 2440) (p 2657) (p 2750) (p 2753) (p 2786) (p 3483) (p 4358) (p 4368) (p 4948) (derived40810 p h) (h 11313)

theorem derived42280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 4110) ∨ (¬ p 4358) ∨ (¬ p 4441) ∨ (¬ p 4889) :=
  ElevenRUP.step42280 (p 2027) (p 2373) (p 4110) (p 4358) (p 4441) (p 4889) (derived40810 p h) (h 11314)

theorem derived42281 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3879) ∨ (¬ p 3880) ∨ (¬ p 4129) ∨ (¬ p 4132) ∨ (¬ p 5564) :=
  ElevenRUP.step42281 (p 2027) (p 2901) (p 3879) (p 3880) (p 4129) (p 4132) (p 5564) (derived40810 p h) (h 11315)

theorem derived42282 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2737) ∨ (¬ p 3591) ∨ (¬ p 3918) ∨ (¬ p 4842) :=
  ElevenRUP.step42282 (p 2027) (p 2608) (p 2737) (p 3591) (p 3918) (p 4842) (derived40810 p h) (h 11316)

theorem derived42285 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 2807) ∨ (¬ p 3579) ∨ (¬ p 4646) :=
  ElevenRUP.step42285 (p 2027) (p 2440) (p 2657) (p 2807) (p 3579) (p 4646) (derived40810 p h) (h 11319)

theorem derived42286 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 2911) ∨ (¬ p 3551) ∨ (¬ p 3822) ∨ (¬ p 3920) ∨ (¬ p 5222) :=
  ElevenRUP.step42286 (p 2027) (p 2318) (p 2911) (p 3551) (p 3822) (p 3920) (p 5222) (derived40810 p h) (h 11320)

theorem derived42287 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2901) ∨ (¬ p 3425) ∨ (¬ p 4169) ∨ (¬ p 4906) :=
  ElevenRUP.step42287 (p 2027) (p 2132) (p 2901) (p 3425) (p 4169) (p 4906) (derived40810 p h) (h 11321)

theorem derived42288 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2318) ∨ (¬ p 3551) ∨ (¬ p 4037) ∨ (¬ p 4156) ∨ (¬ p 4620) :=
  ElevenRUP.step42288 (p 2027) (p 2264) (p 2318) (p 3551) (p 4037) (p 4156) (p 4620) (derived40810 p h) (h 11322)

theorem derived42289 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2668) ∨ (¬ p 3758) ∨ (¬ p 4336) ∨ (¬ p 4356) ∨ (¬ p 4906) :=
  ElevenRUP.step42289 (p 2027) (p 2387) (p 2668) (p 3758) (p 4336) (p 4356) (p 4906) (derived40810 p h) (h 11323)

theorem derived42290 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 4452) ∨ (¬ p 4869) ∨ (¬ p 5206) :=
  ElevenRUP.step42290 (p 2027) (p 2241) (p 2750) (p 3527) (p 3551) (p 4452) (p 4869) (p 5206) (derived40810 p h) (h 11325)

theorem derived42291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 3979) ∨ (¬ p 4381) ∨ (¬ p 5119) :=
  ElevenRUP.step42291 (p 2027) (p 2252) (p 2750) (p 2753) (p 2774) (p 2819) (p 3414) (p 3947) (p 3979) (p 4381) (p 5119) (derived40810 p h) (h 11326)

theorem derived42292 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 3379) ∨ (¬ p 3555) ∨ (¬ p 4034) ∨ (¬ p 4811) :=
  ElevenRUP.step42292 (p 2027) (p 2542) (p 3379) (p 3555) (p 4034) (p 4811) (derived40810 p h) (h 11327)

theorem derived42293 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 3969) ∨ (¬ p 4381) ∨ (¬ p 4789) ∨ (¬ p 5119) :=
  ElevenRUP.step42293 (p 2027) (p 2132) (p 2619) (p 3414) (p 3947) (p 3969) (p 4381) (p 4789) (p 5119) (derived40810 p h) (h 11328)

theorem derived42296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2962) ∨ (¬ p 3989) ∨ (¬ p 4173) ∨ (¬ p 4525) :=
  ElevenRUP.step42296 (p 2027) (p 2383) (p 2962) (p 3989) (p 4173) (p 4525) (derived40810 p h) (h 11331)

theorem derived42297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2829) ∨ (¬ p 4242) ∨ (¬ p 4857) ∨ (¬ p 4889) :=
  ElevenRUP.step42297 (p 2027) (p 2187) (p 2829) (p 4242) (p 4857) (p 4889) (derived40810 p h) (h 11332)

theorem derived42298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3516) ∨ (¬ p 3819) ∨ (¬ p 4324) ∨ (¬ p 4357) ∨ (¬ p 4842) :=
  ElevenRUP.step42298 (p 2027) (p 2780) (p 3516) (p 3819) (p 4324) (p 4357) (p 4842) (derived40810 p h) (h 11333)

theorem derived42299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2737) ∨ (¬ p 2779) ∨ (¬ p 3549) ∨ (¬ p 3953) ∨ (¬ p 4842) :=
  ElevenRUP.step42299 (p 2027) (p 2307) (p 2737) (p 2779) (p 3549) (p 3953) (p 4842) (derived40810 p h) (h 11334)

theorem derived42300 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3742) ∨ (¬ p 4278) ∨ (¬ p 4666) :=
  ElevenRUP.step42300 (p 2027) (p 2122) (p 2177) (p 2252) (p 2657) (p 2750) (p 2753) (p 2774) (p 3742) (p 4278) (p 4666) (derived40810 p h) (h 11335)

theorem derived42301 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3115) ∨ (¬ p 3497) ∨ (¬ p 4340) ∨ (¬ p 4742) :=
  ElevenRUP.step42301 (p 2027) (p 2532) (p 3115) (p 3497) (p 4340) (p 4742) (derived40810 p h) (h 11337)

theorem derived42303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2954) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3697) ∨ (¬ p 3857) :=
  ElevenRUP.step42303 (p 2027) (p 2954) (p 3146) (p 3156) (p 3697) (p 3857) (derived40810 p h) (h 11339)

theorem derived42304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2745) ∨ (¬ p 3005) ∨ (¬ p 3170) ∨ (¬ p 3256) ∨ (¬ p 3857) :=
  ElevenRUP.step42304 (p 2027) (p 2252) (p 2745) (p 3005) (p 3170) (p 3256) (p 3857) (derived40810 p h) (h 11340)

theorem derived42308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3680) ∨ (¬ p 3821) ∨ (¬ p 4192) ∨ (¬ p 4381) ∨ (¬ p 4986) :=
  ElevenRUP.step42308 (p 2027) (p 3680) (p 3821) (p 4192) (p 4381) (p 4986) (derived40810 p h) (h 11344)

theorem derived42309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3646) ∨ (¬ p 4140) ∨ (¬ p 4393) ∨ (¬ p 5472) :=
  ElevenRUP.step42309 (p 2027) (p 3051) (p 3646) (p 4140) (p 4393) (p 5472) (derived40810 p h) (h 11345)

theorem derived42310 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2780) ∨ (¬ p 3989) ∨ (¬ p 4401) ∨ (¬ p 4417) ∨ (¬ p 4967) :=
  ElevenRUP.step42310 (p 2027) (p 2098) (p 2780) (p 3989) (p 4401) (p 4417) (p 4967) (derived40810 p h) (h 11346)

theorem derived42313 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3609) ∨ (¬ p 3949) ∨ (¬ p 4363) ∨ (¬ p 4746) :=
  ElevenRUP.step42313 (p 2027) (p 2166) (p 3609) (p 3949) (p 4363) (p 4746) (derived40810 p h) (h 11350)

theorem derived42314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 3105) ∨ (¬ p 4037) ∨ (¬ p 4397) ∨ (¬ p 5021) :=
  ElevenRUP.step42314 (p 2027) (p 2295) (p 2313) (p 2608) (p 2839) (p 3105) (p 4037) (p 4397) (p 5021) (derived40810 p h) (h 11351)

theorem derived42315 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2745) ∨ (¬ p 3031) ∨ (¬ p 3817) :=
  ElevenRUP.step42315 (p 2027) (p 2449) (p 2685) (p 2745) (p 3031) (p 3817) (derived40810 p h) (h 11352)

theorem derived42316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3093) ∨ (¬ p 3860) ∨ (¬ p 4757) ∨ (¬ p 4993) :=
  ElevenRUP.step42316 (p 2027) (p 2668) (p 3093) (p 3860) (p 4757) (p 4993) (derived40810 p h) (h 11353)

theorem derived42317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 3877) ∨ (¬ p 3931) ∨ (¬ p 4548) ∨ (¬ p 5564) :=
  ElevenRUP.step42317 (p 2027) (p 2685) (p 3877) (p 3931) (p 4548) (p 5564) (derived40810 p h) (h 11354)

theorem derived42318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4376) :=
  ElevenRUP.step42318 (p 2027) (p 2470) (p 2528) (p 3365) (p 3366) (p 3519) (p 3553) (p 3572) (p 4133) (p 4347) (p 4376) (derived40810 p h) (h 11355)

theorem derived42321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2741) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3519) ∨ (¬ p 4035) ∨ (¬ p 4376) ∨ (¬ p 5113) :=
  ElevenRUP.step42321 (p 2027) (p 2252) (p 2352) (p 2363) (p 2573) (p 2741) (p 2952) (p 3136) (p 3519) (p 4035) (p 4376) (p 5113) (derived40810 p h) (h 11358)

theorem derived42322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2962) ∨ (¬ p 3556) ∨ (¬ p 3654) ∨ (¬ p 3744) ∨ (¬ p 4555) :=
  ElevenRUP.step42322 (p 2027) (p 2962) (p 3556) (p 3654) (p 3744) (p 4555) (derived40810 p h) (h 11359)

theorem derived42323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2589) ∨ (¬ p 2742) ∨ (¬ p 2774) ∨ (¬ p 3905) ∨ (¬ p 4281) ∨ (¬ p 4845) :=
  ElevenRUP.step42323 (p 2027) (p 2406) (p 2589) (p 2742) (p 2774) (p 3905) (p 4281) (p 4845) (derived40810 p h) (h 11360)

theorem derived42325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2737) ∨ (¬ p 2779) ∨ (¬ p 3923) ∨ (¬ p 3953) ∨ (¬ p 4842) :=
  ElevenRUP.step42325 (p 2027) (p 2383) (p 2737) (p 2779) (p 3923) (p 3953) (p 4842) (derived40810 p h) (h 11362)

theorem derived42326 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3055) ∨ (¬ p 3471) ∨ (¬ p 3658) ∨ (¬ p 5214) :=
  ElevenRUP.step42326 (p 2027) (p 2928) (p 3055) (p 3471) (p 3658) (p 5214) (derived40810 p h) (h 11363)

theorem derived42327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3097) ∨ (¬ p 3471) ∨ (¬ p 4401) ∨ (¬ p 4475) :=
  ElevenRUP.step42327 (p 2027) (p 2780) (p 3097) (p 3471) (p 4401) (p 4475) (derived40810 p h) (h 11364)

theorem derived42328 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 3692) ∨ (¬ p 4119) ∨ (¬ p 4362) :=
  ElevenRUP.step42328 (p 2027) (p 2264) (p 2459) (p 3692) (p 4119) (p 4362) (derived40810 p h) (h 11365)

theorem derived42330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3684) ∨ (¬ p 4019) ∨ (¬ p 4186) ∨ (¬ p 4286) ∨ (¬ p 4354) ∨ (¬ p 4646) :=
  ElevenRUP.step42330 (p 2027) (p 3684) (p 4019) (p 4186) (p 4286) (p 4354) (p 4646) (derived40810 p h) (h 11367)

theorem derived42331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2138) ∨ (¬ p 2191) ∨ (¬ p 4188) ∨ (¬ p 4875) :=
  ElevenRUP.step42331 (p 2027) (p 2098) (p 2138) (p 2191) (p 4188) (p 4875) (derived40810 p h) (h 11368)

theorem derived42333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 3422) ∨ (¬ p 3878) ∨ (¬ p 4118) ∨ (¬ p 4753) :=
  ElevenRUP.step42333 (p 2027) (p 2510) (p 2528) (p 3422) (p 3878) (p 4118) (p 4753) (derived40810 p h) (h 11370)

theorem derived42334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2230) ∨ (¬ p 2313) ∨ (¬ p 2440) ∨ (¬ p 2778) ∨ (¬ p 3083) ∨ (¬ p 4358) ∨ (¬ p 4419) ∨ (¬ p 4596) :=
  ElevenRUP.step42334 (p 2027) (p 2122) (p 2230) (p 2313) (p 2440) (p 2778) (p 3083) (p 4358) (p 4419) (p 4596) (derived40810 p h) (h 11371)

theorem derived42335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2313) ∨ (¬ p 2440) ∨ (¬ p 2459) ∨ (¬ p 2778) ∨ (¬ p 3083) ∨ (¬ p 3955) ∨ (¬ p 4347) ∨ (¬ p 4419) ∨ (¬ p 4420) :=
  ElevenRUP.step42335 (p 2027) (p 2230) (p 2313) (p 2440) (p 2459) (p 2778) (p 3083) (p 3955) (p 4347) (p 4419) (p 4420) (derived40810 p h) (h 11372)

theorem derived42336 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2778) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3692) ∨ (¬ p 3917) ∨ (¬ p 3990) ∨ (¬ p 4433) ∨ (¬ p 4786) :=
  ElevenRUP.step42336 (p 2027) (p 2122) (p 2313) (p 2778) (p 3166) (p 3256) (p 3692) (p 3917) (p 3990) (p 4433) (p 4786) (derived40810 p h) (h 11373)

theorem derived42337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2534) ∨ (¬ p 3055) ∨ (¬ p 3323) ∨ (¬ p 3366) ∨ (¬ p 3568) ∨ (¬ p 3874) ∨ (¬ p 3950) ∨ (¬ p 4623) ∨ (¬ p 4866) ∨ (¬ p 5016) :=
  ElevenRUP.step42337 (p 2027) (p 2307) (p 2534) (p 3055) (p 3323) (p 3366) (p 3568) (p 3874) (p 3950) (p 4623) (p 4866) (p 5016) (derived40810 p h) (h 11374)

theorem derived42340 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2589) ∨ (¬ p 2668) ∨ (¬ p 3905) ∨ (¬ p 3979) ∨ (¬ p 4322) ∨ (¬ p 4786) ∨ (¬ p 4948) ∨ (¬ p 5119) :=
  ElevenRUP.step42340 (p 2027) (p 2331) (p 2589) (p 2668) (p 3905) (p 3979) (p 4322) (p 4786) (p 4948) (p 5119) (derived40810 p h) (h 11377)

theorem derived42342 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 3323) ∨ (¬ p 3366) ∨ (¬ p 3568) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3950) ∨ (¬ p 4623) ∨ (¬ p 4866) ∨ (¬ p 5016) :=
  ElevenRUP.step42342 (p 2027) (p 2138) (p 2307) (p 3323) (p 3366) (p 3568) (p 3692) (p 3694) (p 3950) (p 4623) (p 4866) (p 5016) (derived40810 p h) (h 11379)

theorem derived42343 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3333) ∨ (¬ p 3876) ∨ (¬ p 3947) ∨ (¬ p 4327) ∨ (¬ p 5182) ∨ (¬ p 5299) :=
  ElevenRUP.step42343 (p 2027) (p 3333) (p 3876) (p 3947) (p 4327) (p 5182) (p 5299) (derived40810 p h) (h 11380)

theorem derived42344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2449) ∨ (¬ p 3055) ∨ (¬ p 3553) ∨ (¬ p 3584) ∨ (¬ p 4137) ∨ (¬ p 4625) ∨ (¬ p 5257) :=
  ElevenRUP.step42344 (p 2027) (p 2341) (p 2449) (p 3055) (p 3553) (p 3584) (p 4137) (p 4625) (p 5257) (derived40810 p h) (h 11381)

theorem derived42345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2589) ∨ (¬ p 2668) ∨ (¬ p 2781) ∨ (¬ p 2850) ∨ (¬ p 3568) ∨ (¬ p 3874) ∨ (¬ p 3905) ∨ (¬ p 4384) :=
  ElevenRUP.step42345 (p 2027) (p 2307) (p 2589) (p 2668) (p 2781) (p 2850) (p 3568) (p 3874) (p 3905) (p 4384) (derived40810 p h) (h 11382)

theorem derived42346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3227) ∨ (¬ p 3333) ∨ (¬ p 3584) ∨ (¬ p 4037) ∨ (¬ p 4973) ∨ (¬ p 5152) :=
  ElevenRUP.step42346 (p 2027) (p 3227) (p 3333) (p 3584) (p 4037) (p 4973) (p 5152) (derived40810 p h) (h 11383)

theorem derived42347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2781) ∨ (¬ p 3323) ∨ (¬ p 3346) ∨ (¬ p 3568) ∨ (¬ p 3680) ∨ (¬ p 3905) ∨ (¬ p 4368) ∨ (¬ p 4425) :=
  ElevenRUP.step42347 (p 2027) (p 2307) (p 2781) (p 3323) (p 3346) (p 3568) (p 3680) (p 3905) (p 4368) (p 4425) (derived40810 p h) (h 11384)

theorem derived42348 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2166) ∨ (¬ p 3952) ∨ (¬ p 4120) ∨ (¬ p 4960) :=
  ElevenRUP.step42348 (p 2027) (p 2156) (p 2166) (p 3952) (p 4120) (p 4960) (derived40810 p h) (h 11385)

theorem derived42350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2190) ∨ (¬ p 2958) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3644) ∨ (¬ p 3876) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4786) :=
  ElevenRUP.step42350 (p 2027) (p 2156) (p 2190) (p 2958) (p 3055) (p 3146) (p 3644) (p 3876) (p 4133) (p 4347) (p 4786) (derived40810 p h) (h 11387)

theorem derived42351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3497) ∨ (¬ p 3555) ∨ (¬ p 4418) ∨ (¬ p 4446) ∨ (¬ p 5053) :=
  ElevenRUP.step42351 (p 2027) (p 3449) (p 3497) (p 3555) (p 4418) (p 4446) (p 5053) (derived40810 p h) (h 11388)

theorem derived42352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2946) ∨ (¬ p 3125) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4786) :=
  ElevenRUP.step42352 (p 2027) (p 2284) (p 2946) (p 3125) (p 3425) (p 3659) (p 4330) (p 4348) (p 4786) (derived40810 p h) (h 11389)

theorem derived42353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2284) ∨ (¬ p 2459) ∨ (¬ p 2946) ∨ (¬ p 3425) ∨ (¬ p 3685) ∨ (¬ p 4133) ∨ (¬ p 4340) ∨ (¬ p 4786) :=
  ElevenRUP.step42353 (p 2027) (p 2187) (p 2284) (p 2459) (p 2946) (p 3425) (p 3685) (p 4133) (p 4340) (p 4786) (derived40810 p h) (h 11390)

theorem derived42354 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2284) ∨ (¬ p 2946) ∨ (¬ p 3201) ∨ (¬ p 3540) ∨ (¬ p 3874) ∨ (¬ p 3905) ∨ (¬ p 4384) ∨ (¬ p 4786) :=
  ElevenRUP.step42354 (p 2027) (p 2187) (p 2284) (p 2946) (p 3201) (p 3540) (p 3874) (p 3905) (p 4384) (p 4786) (derived40810 p h) (h 11391)

theorem derived42356 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 2819) ∨ (¬ p 3016) ∨ (¬ p 4170) ∨ (¬ p 4256) ∨ (¬ p 5225) :=
  ElevenRUP.step42356 (p 2027) (p 2481) (p 2819) (p 3016) (p 4170) (p 4256) (p 5225) (derived40810 p h) (h 11393)

theorem derived42357 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3177) ∨ (¬ p 3570) ∨ (¬ p 3857) ∨ (¬ p 4189) ∨ (¬ p 4378) ∨ (¬ p 4914) :=
  ElevenRUP.step42357 (p 2027) (p 3073) (p 3177) (p 3570) (p 3857) (p 4189) (p 4378) (p 4914) (derived40810 p h) (h 11394)

theorem derived42358 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2284) ∨ (¬ p 3125) ∨ (¬ p 3879) ∨ (¬ p 3954) ∨ (¬ p 4242) ∨ (¬ p 4330) ∨ (¬ p 4340) ∨ (¬ p 5190) :=
  ElevenRUP.step42358 (p 2027) (p 2230) (p 2284) (p 3125) (p 3879) (p 3954) (p 4242) (p 4330) (p 4340) (p 5190) (derived40810 p h) (h 11395)

theorem derived42359 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3426) ∨ (¬ p 3434) ∨ (¬ p 3742) ∨ (¬ p 3821) ∨ (¬ p 4279) ∨ (¬ p 4375) ∨ (¬ p 4753) :=
  ElevenRUP.step42359 (p 2027) (p 3426) (p 3434) (p 3742) (p 3821) (p 4279) (p 4375) (p 4753) (derived40810 p h) (h 11396)

theorem derived42360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2387) ∨ (¬ p 2819) ∨ (¬ p 3574) ∨ (¬ p 4375) ∨ (¬ p 4753) :=
  ElevenRUP.step42360 (p 2027) (p 2386) (p 2387) (p 2819) (p 3574) (p 4375) (p 4753) (derived40810 p h) (h 11397)

theorem derived42361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2573) ∨ (¬ p 3083) ∨ (¬ p 3574) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4420) ∨ (¬ p 5190) :=
  ElevenRUP.step42361 (p 2027) (p 2459) (p 2573) (p 3083) (p 3574) (p 3860) (p 4261) (p 4420) (p 5190) (derived40810 p h) (h 11398)

theorem derived42362 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2946) ∨ (¬ p 3425) ∨ (¬ p 3737) ∨ (¬ p 4324) ∨ (¬ p 4381) ∨ (¬ p 4786) ∨ (¬ p 5250) :=
  ElevenRUP.step42362 (p 2027) (p 2284) (p 2946) (p 3425) (p 3737) (p 4324) (p 4381) (p 4786) (p 5250) (derived40810 p h) (h 11399)

theorem derived42363 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2284) ∨ (¬ p 3125) ∨ (¬ p 3548) ∨ (¬ p 3879) ∨ (¬ p 4330) ∨ (¬ p 4348) ∨ (¬ p 4366) ∨ (¬ p 5190) :=
  ElevenRUP.step42363 (p 2027) (p 2230) (p 2284) (p 3125) (p 3548) (p 3879) (p 4330) (p 4348) (p 4366) (p 5190) (derived40810 p h) (h 11400)

theorem derived42364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2437) ∨ (¬ p 2440) ∨ (¬ p 3434) ∨ (¬ p 3817) ∨ (¬ p 3954) ∨ (¬ p 4400) ∨ (¬ p 5087) ∨ (¬ p 5190) :=
  ElevenRUP.step42364 (p 2027) (p 2230) (p 2437) (p 2440) (p 3434) (p 3817) (p 3954) (p 4400) (p 5087) (p 5190) (derived40810 p h) (h 11402)

theorem derived42365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 2761) ∨ (¬ p 2778) ∨ (¬ p 3083) ∨ (¬ p 3946) ∨ (¬ p 4669) ∨ (¬ p 4786) ∨ (¬ p 5269) ∨ (¬ p 5387) :=
  ElevenRUP.step42365 (p 2027) (p 2528) (p 2651) (p 2761) (p 2778) (p 3083) (p 3946) (p 4669) (p 4786) (p 5269) (p 5387) (derived40810 p h) (h 11403)

theorem derived42366 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2299) ∨ (¬ p 2313) ∨ (¬ p 2440) ∨ (¬ p 2778) ∨ (¬ p 3343) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4332) ∨ (¬ p 4348) ∨ (¬ p 4376) :=
  ElevenRUP.step42366 (p 2027) (p 2230) (p 2299) (p 2313) (p 2440) (p 2778) (p 3343) (p 3366) (p 3519) (p 4332) (p 4348) (p 4376) (derived40810 p h) (h 11404)

theorem derived42368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 3483) ∨ (¬ p 3574) ∨ (¬ p 3946) ∨ (¬ p 4375) ∨ (¬ p 4753) :=
  ElevenRUP.step42368 (p 2027) (p 2386) (p 3483) (p 3574) (p 3946) (p 4375) (p 4753) (derived40810 p h) (h 11406)

theorem derived42372 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2743) ∨ (¬ p 2785) ∨ (¬ p 3309) ∨ (¬ p 4845) ∨ (¬ p 4869) :=
  ElevenRUP.step42372 (p 2027) (p 2313) (p 2743) (p 2785) (p 3309) (p 4845) (p 4869) (derived40810 p h) (h 11410)

theorem derived42373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2668) ∨ (¬ p 3055) ∨ (¬ p 3745) ∨ (¬ p 3979) ∨ (¬ p 4425) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step42373 (p 2027) (p 2139) (p 2156) (p 2668) (p 3055) (p 3745) (p 3979) (p 4425) (p 5119) (p 5160) (derived40810 p h) (h 11412)

theorem derived42376 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2745) ∨ (¬ p 2951) ∨ (¬ p 3051) ∨ (¬ p 3136) ∨ (¬ p 3368) ∨ (¬ p 3486) :=
  ElevenRUP.step42376 (p 2027) (p 2745) (p 2951) (p 3051) (p 3136) (p 3368) (p 3486) (derived40810 p h) (h 11415)

theorem derived42378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3343) ∨ (¬ p 3879) ∨ (¬ p 4315) ∨ (¬ p 4953) :=
  ElevenRUP.step42378 (p 2027) (p 2630) (p 3343) (p 3879) (p 4315) (p 4953) (derived40810 p h) (h 11417)

theorem derived42379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2668) ∨ (¬ p 2807) ∨ (¬ p 3019) ∨ (¬ p 3983) ∨ (¬ p 4652) :=
  ElevenRUP.step42379 (p 2027) (p 2387) (p 2668) (p 2807) (p 3019) (p 3983) (p 4652) (derived40810 p h) (h 11418)

theorem derived42381 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 2685) ∨ (¬ p 2741) ∨ (¬ p 2996) ∨ (¬ p 3146) ∨ (¬ p 3519) ∨ (¬ p 4035) ∨ (¬ p 4376) ∨ (¬ p 5113) :=
  ElevenRUP.step42381 (p 2027) (p 2230) (p 2373) (p 2685) (p 2741) (p 2996) (p 3146) (p 3519) (p 4035) (p 4376) (p 5113) (derived40810 p h) (h 11421)

theorem derived42382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3425) ∨ (¬ p 3969) ∨ (¬ p 4324) ∨ (¬ p 4381) ∨ (¬ p 4419) ∨ (¬ p 5119) :=
  ElevenRUP.step42382 (p 2027) (p 2230) (p 2373) (p 3425) (p 3969) (p 4324) (p 4381) (p 4419) (p 5119) (derived40810 p h) (h 11422)

theorem derived42383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2563) ∨ (¬ p 2685) ∨ (¬ p 3125) ∨ (¬ p 3414) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 5279) :=
  ElevenRUP.step42383 (p 2027) (p 2230) (p 2563) (p 2685) (p 3125) (p 3414) (p 4035) (p 4236) (p 4419) (p 5279) (derived40810 p h) (h 11423)

theorem derived42384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3549) ∨ (¬ p 3555) ∨ (¬ p 3953) ∨ (¬ p 4377) ∨ (¬ p 5020) :=
  ElevenRUP.step42384 (p 2027) (p 2307) (p 3549) (p 3555) (p 3953) (p 4377) (p 5020) (derived40810 p h) (h 11424)

theorem derived42385 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 4037) ∨ (¬ p 4195) ∨ (¬ p 4377) ∨ (¬ p 4604) :=
  ElevenRUP.step42385 (p 2027) (p 3073) (p 3365) (p 3366) (p 3449) (p 3555) (p 4037) (p 4195) (p 4377) (p 4604) (derived40810 p h) (h 11425)

theorem derived42386 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2741) ∨ (¬ p 3073) ∨ (¬ p 3292) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 3461) ∨ (¬ p 4376) ∨ (¬ p 4604) ∨ (¬ p 5284) :=
  ElevenRUP.step42386 (p 2027) (p 2252) (p 2741) (p 3073) (p 3292) (p 3449) (p 3452) (p 3461) (p 4376) (p 4604) (p 5284) (derived40810 p h) (h 11426)

theorem derived42387 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2741) ∨ (¬ p 2807) ∨ (¬ p 2996) ∨ (¬ p 3452) ∨ (¬ p 4376) :=
  ElevenRUP.step42387 (p 2027) (p 2253) (p 2741) (p 2807) (p 2996) (p 3452) (p 4376) (derived40810 p h) (h 11427)

theorem derived42392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 4181) ∨ (¬ p 4377) ∨ (¬ p 4425) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step42392 (p 2027) (p 3055) (p 3366) (p 3449) (p 3555) (p 4181) (p 4377) (p 4425) (p 5119) (p 5160) (derived40810 p h) (h 11432)

theorem derived42394 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 3584) ∨ (¬ p 5254) ∨ (¬ p 5514) :=
  ElevenRUP.step42394 (p 2027) (p 2139) (p 2220) (p 3055) (p 3146) (p 3266) (p 3584) (p 5254) (p 5514) (derived40810 p h) (h 11434)

theorem derived42396 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3389) ∨ (¬ p 3555) ∨ (¬ p 4079) ∨ (¬ p 4257) ∨ (¬ p 4377) :=
  ElevenRUP.step42396 (p 2027) (p 2928) (p 3389) (p 3555) (p 4079) (p 4257) (p 4377) (derived40810 p h) (h 11436)

theorem derived42397 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2657) ∨ (¬ p 2761) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 4236) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 5123) :=
  ElevenRUP.step42397 (p 2027) (p 2139) (p 2657) (p 2761) (p 3051) (p 3246) (p 4236) (p 4256) (p 4286) (p 5123) (derived40810 p h) (h 11437)

theorem derived42398 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2657) ∨ (¬ p 3125) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3461) ∨ (¬ p 4236) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 4377) ∨ (¬ p 5123) :=
  ElevenRUP.step42398 (p 2027) (p 2156) (p 2657) (p 3125) (p 3366) (p 3370) (p 3461) (p 4236) (p 4256) (p 4286) (p 4377) (p 5123) (derived40810 p h) (h 11438)

theorem derived42399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2252) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 2741) ∨ (¬ p 3370) ∨ (¬ p 4035) ∨ (¬ p 4377) ∨ (¬ p 4641) ∨ (¬ p 5171) :=
  ElevenRUP.step42399 (p 2027) (p 2156) (p 2252) (p 2274) (p 2396) (p 2630) (p 2657) (p 2741) (p 3370) (p 4035) (p 4377) (p 4641) (p 5171) (derived40810 p h) (h 11439)

theorem derived42400 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 3879) ∨ (¬ p 4315) ∨ (¬ p 4610) :=
  ElevenRUP.step42400 (p 2027) (p 2470) (p 2630) (p 2656) (p 3879) (p 4315) (p 4610) (derived40810 p h) (h 11440)

theorem derived42401 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 3989) ∨ (¬ p 4318) ∨ (¬ p 4518) :=
  ElevenRUP.step42401 (p 2027) (p 3449) (p 3591) (p 3989) (p 4318) (p 4518) (derived40810 p h) (h 11441)

theorem derived42402 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 3365) ∨ (¬ p 3979) ∨ (¬ p 4035) ∨ (¬ p 5119) ∨ (¬ p 5284) :=
  ElevenRUP.step42402 (p 2027) (p 2139) (p 2156) (p 2187) (p 3365) (p 3979) (p 4035) (p 5119) (p 5284) (derived40810 p h) (h 11459)

theorem derived42403 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3979) ∨ (¬ p 4377) ∨ (¬ p 4425) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step42403 (p 2027) (p 2156) (p 2187) (p 3055) (p 3366) (p 3370) (p 3979) (p 4377) (p 4425) (p 5119) (p 5160) (derived40810 p h) (h 11460)

theorem derived42405 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 2657) ∨ (¬ p 3276) ∨ (¬ p 4236) ∨ (¬ p 4641) ∨ (¬ p 5170) ∨ (¬ p 5284) :=
  ElevenRUP.step42405 (p 2027) (p 2139) (p 2156) (p 2274) (p 2396) (p 2657) (p 3276) (p 4236) (p 4641) (p 5170) (p 5284) (derived40810 p h) (h 11462)

theorem derived42407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2459) ∨ (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 2781) ∨ (¬ p 2881) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4275) ∨ (¬ p 5113) :=
  ElevenRUP.step42407 (p 2027) (p 2307) (p 2459) (p 2630) (p 2657) (p 2781) (p 2881) (p 4035) (p 4236) (p 4275) (p 5113) (derived40810 p h) (h 11464)

theorem derived42408 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2396) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 3950) ∨ (¬ p 4236) ∨ (¬ p 4256) :=
  ElevenRUP.step42408 (p 2027) (p 2139) (p 2156) (p 2274) (p 2396) (p 2534) (p 2657) (p 3950) (p 4236) (p 4256) (derived40810 p h) (h 11465)

theorem derived42409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2307) ∨ (¬ p 2781) ∨ (¬ p 2810) ∨ (¬ p 3097) ∨ (¬ p 3365) ∨ (¬ p 4256) ∨ (¬ p 4384) :=
  ElevenRUP.step42409 (p 2027) (p 2187) (p 2307) (p 2781) (p 2810) (p 3097) (p 3365) (p 4256) (p 4384) (derived40810 p h) (h 11466)

theorem derived42410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 3919) ∨ (¬ p 3931) ∨ (¬ p 4340) ∨ (¬ p 4383) ∨ (¬ p 4967) ∨ (¬ p 5564) :=
  ElevenRUP.step42410 (p 2027) (p 2528) (p 3919) (p 3931) (p 4340) (p 4383) (p 4967) (p 5564) (derived40810 p h) (h 11467)

theorem derived42413 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3580) ∨ (¬ p 3931) ∨ (¬ p 4646) ∨ (¬ p 5503) :=
  ElevenRUP.step42413 (p 2027) (p 2440) (p 3580) (p 3931) (p 4646) (p 5503) (derived40810 p h) (h 11470)

theorem derived42414 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2810) ∨ (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 3359) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 4377) ∨ (¬ p 4697) :=
  ElevenRUP.step42414 (p 2027) (p 2459) (p 2810) (p 2881) (p 3051) (p 3359) (p 3365) (p 3366) (p 3370) (p 4377) (p 4697) (derived40810 p h) (h 11472)

theorem derived42415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 3055) ∨ (¬ p 3941) ∨ (¬ p 4425) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step42415 (p 2027) (p 2139) (p 2881) (p 3051) (p 3055) (p 3941) (p 4425) (p 5119) (p 5160) (derived40810 p h) (h 11473)

theorem derived42417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3572) ∨ (¬ p 3690) ∨ (¬ p 3755) ∨ (¬ p 4362) ∨ (¬ p 4660) :=
  ElevenRUP.step42417 (p 2027) (p 3572) (p 3690) (p 3755) (p 4362) (p 4660) (derived40810 p h) (h 11476)

theorem derived42418 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2797) ∨ (¬ p 2963) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3569) ∨ (¬ p 3644) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4376) ∨ (¬ p 4399) ∨ (¬ p 4663) ∨ (¬ p 4988) :=
  ElevenRUP.step42418 (p 2027) (p 2341) (p 2797) (p 2963) (p 3246) (p 3366) (p 3519) (p 3569) (p 3644) (p 4035) (p 4236) (p 4376) (p 4399) (p 4663) (p 4988) (derived40810 p h) (h 11477)

theorem derived42419 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 3688) ∨ (¬ p 3917) ∨ (¬ p 3954) ∨ (¬ p 4521) ∨ (¬ p 4625) ∨ (¬ p 4988) :=
  ElevenRUP.step42419 (p 2027) (p 2341) (p 3246) (p 3570) (p 3688) (p 3917) (p 3954) (p 4521) (p 4625) (p 4988) (derived40810 p h) (h 11478)

theorem derived42420 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 3874) ∨ (¬ p 3888) ∨ (¬ p 4432) ∨ (¬ p 5586) :=
  ElevenRUP.step42420 (p 2027) (p 3422) (p 3874) (p 3888) (p 4432) (p 5586) (derived40810 p h) (h 11479)

theorem derived42421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 4037) ∨ (¬ p 4195) ∨ (¬ p 4419) ∨ (¬ p 4604) :=
  ElevenRUP.step42421 (p 2027) (p 2230) (p 2373) (p 3146) (p 3365) (p 4037) (p 4195) (p 4419) (p 4604) (derived40810 p h) (h 11480)

theorem derived42422 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3690) ∨ (¬ p 3830) ∨ (¬ p 4366) ∨ (¬ p 4914) ∨ (¬ p 5362) :=
  ElevenRUP.step42422 (p 2027) (p 3690) (p 3830) (p 4366) (p 4914) (p 5362) (derived40810 p h) (h 11481)

theorem derived42423 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2995) ∨ (¬ p 3486) ∨ (¬ p 3551) ∨ (¬ p 4283) ∨ (¬ p 4957) :=
  ElevenRUP.step42423 (p 2027) (p 2264) (p 2995) (p 3486) (p 3551) (p 4283) (p 4957) (derived40810 p h) (h 11482)

theorem derived42424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2264) ∨ (¬ p 2891) ∨ (¬ p 4132) ∨ (¬ p 4362) :=
  ElevenRUP.step42424 (p 2027) (p 2191) (p 2264) (p 2891) (p 4132) (p 4362) (derived40810 p h) (h 11483)

theorem derived42426 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 3097) ∨ (¬ p 3609) ∨ (¬ p 3857) ∨ (¬ p 3961) ∨ (¬ p 4401) ∨ (¬ p 4861) :=
  ElevenRUP.step42426 (p 2027) (p 2318) (p 3097) (p 3609) (p 3857) (p 3961) (p 4401) (p 4861) (derived40810 p h) (h 11485)

theorem derived42427 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3952) ∨ (¬ p 4140) ∨ (¬ p 4393) ∨ (¬ p 5472) :=
  ElevenRUP.step42427 (p 2027) (p 2901) (p 3952) (p 4140) (p 4393) (p 5472) (derived40810 p h) (h 11486)

theorem derived42429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3609) ∨ (¬ p 4256) ∨ (¬ p 4375) ∨ (¬ p 4753) ∨ (¬ p 4861) :=
  ElevenRUP.step42429 (p 2027) (p 2534) (p 3609) (p 4256) (p 4375) (p 4753) (p 4861) (derived40810 p h) (h 11488)

theorem derived42430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2850) ∨ (¬ p 3741) ∨ (¬ p 3947) ∨ (¬ p 4112) ∨ (¬ p 4753) :=
  ElevenRUP.step42430 (p 2027) (p 2417) (p 2850) (p 3741) (p 3947) (p 4112) (p 4753) (derived40810 p h) (h 11489)

theorem derived42436 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2619) ∨ (¬ p 3347) ∨ (¬ p 3582) ∨ (¬ p 3880) ∨ (¬ p 5214) :=
  ElevenRUP.step42436 (p 2027) (p 2589) (p 2619) (p 3347) (p 3582) (p 3880) (p 5214) (derived40810 p h) (h 11495)

theorem derived42437 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2928) ∨ (¬ p 3146) ∨ (¬ p 3452) ∨ (¬ p 3644) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4521) :=
  ElevenRUP.step42437 (p 2027) (p 2220) (p 2928) (p 3146) (p 3452) (p 3644) (p 4133) (p 4347) (p 4521) (derived40810 p h) (h 11496)

theorem derived42438 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2850) ∨ (¬ p 3497) ∨ (¬ p 4700) ∨ (¬ p 4753) :=
  ElevenRUP.step42438 (p 2027) (p 2373) (p 2850) (p 3497) (p 4700) (p 4753) (derived40810 p h) (h 11497)

theorem derived42439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3051) ∨ (¬ p 4109) ∨ (¬ p 4320) ∨ (¬ p 4700) ∨ (¬ p 4753) :=
  ElevenRUP.step42439 (p 2027) (p 2850) (p 3051) (p 4109) (p 4320) (p 4700) (p 4753) (derived40810 p h) (h 11498)

theorem derived42440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 3791) ∨ (¬ p 4138) ∨ (¬ p 4358) ∨ (¬ p 5564) :=
  ElevenRUP.step42440 (p 2027) (p 2122) (p 3791) (p 4138) (p 4358) (p 5564) (derived40810 p h) (h 11499)

theorem derived42441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3227) ∨ (¬ p 3333) ∨ (¬ p 3379) ∨ (¬ p 3834) ∨ (¬ p 5214) :=
  ElevenRUP.step42441 (p 2027) (p 3227) (p 3333) (p 3379) (p 3834) (p 5214) (derived40810 p h) (h 11500)

theorem derived42442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 5190) :=
  ElevenRUP.step42442 (p 2027) (p 2247) (p 2470) (p 2528) (p 2996) (p 3553) (p 4133) (p 4347) (p 5190) (derived40810 p h) (h 11503)

theorem derived42443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 4120) ∨ (¬ p 4129) ∨ (¬ p 4132) ∨ (¬ p 5564) :=
  ElevenRUP.step42443 (p 2027) (p 3051) (p 4120) (p 4129) (p 4132) (p 5564) (derived40810 p h) (h 11504)

theorem derived42445 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2417) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 3591) ∨ (¬ p 3644) ∨ (¬ p 4026) ∨ (¬ p 4376) ∨ (¬ p 4625) ∨ (¬ p 5201) :=
  ElevenRUP.step42445 (p 2027) (p 2341) (p 2417) (p 2608) (p 3519) (p 3591) (p 3644) (p 4026) (p 4376) (p 4625) (p 5201) (derived40810 p h) (h 11506)

theorem derived42446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 4516) ∨ (¬ p 4555) :=
  ElevenRUP.step42446 (p 2027) (p 3093) (p 3486) (p 3555) (p 4516) (p 4555) (derived40810 p h) (h 11507)

theorem derived42449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2482) ∨ (¬ p 3860) ∨ (¬ p 3998) ∨ (¬ p 5190) ∨ (¬ p 5693) :=
  ElevenRUP.step42449 (p 2027) (p 2482) (p 3860) (p 3998) (p 5190) (p 5693) (derived40810 p h) (h 11510)

theorem derived42451 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3834) ∨ (¬ p 3941) ∨ (¬ p 4321) ∨ (¬ p 4376) ∨ (¬ p 5119) :=
  ElevenRUP.step42451 (p 2027) (p 2608) (p 2911) (p 3389) (p 3519) (p 3834) (p 3941) (p 4321) (p 4376) (p 5119) (derived40810 p h) (h 11512)

theorem derived42452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2911) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 4037) ∨ (¬ p 4195) ∨ (¬ p 4376) ∨ (¬ p 4604) :=
  ElevenRUP.step42452 (p 2027) (p 2459) (p 2911) (p 3365) (p 3366) (p 3389) (p 3519) (p 4037) (p 4195) (p 4376) (p 4604) (derived40810 p h) (h 11513)

theorem derived42453 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2459) ∨ (¬ p 2911) ∨ (¬ p 3366) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3744) ∨ (¬ p 3758) ∨ (¬ p 4376) ∨ (¬ p 4604) :=
  ElevenRUP.step42453 (p 2027) (p 2138) (p 2459) (p 2911) (p 3366) (p 3389) (p 3519) (p 3744) (p 3758) (p 4376) (p 4604) (derived40810 p h) (h 11514)

theorem derived42454 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2307) ∨ (¬ p 2781) ∨ (¬ p 2911) ∨ (¬ p 3921) ∨ (¬ p 3941) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 5119) :=
  ElevenRUP.step42454 (p 2027) (p 2138) (p 2307) (p 2781) (p 2911) (p 3921) (p 3941) (p 4322) (p 4385) (p 5119) (derived40810 p h) (h 11515)

theorem derived42455 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2911) ∨ (¬ p 2922) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 4315) ∨ (¬ p 4320) ∨ (¬ p 4376) ∨ (¬ p 4559) :=
  ElevenRUP.step42455 (p 2027) (p 2299) (p 2911) (p 2922) (p 3365) (p 3366) (p 4315) (p 4320) (p 4376) (p 4559) (derived40810 p h) (h 11516)

theorem derived42457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2573) ∨ (¬ p 3083) ∨ (¬ p 3519) ∨ (¬ p 3556) ∨ (¬ p 3574) ∨ (¬ p 3645) ∨ (¬ p 3692) ∨ (¬ p 4119) ∨ (¬ p 4376) ∨ (¬ p 4420) ∨ (¬ p 4874) :=
  ElevenRUP.step42457 (p 2027) (p 2459) (p 2573) (p 3083) (p 3519) (p 3556) (p 3574) (p 3645) (p 3692) (p 4119) (p 4376) (p 4420) (p 4874) (derived40810 p h) (h 11518)

theorem derived42458 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2386) ∨ (¬ p 3083) ∨ (¬ p 3574) ∨ (¬ p 4157) ∨ (¬ p 4405) :=
  ElevenRUP.step42458 (p 2027) (p 2313) (p 2386) (p 3083) (p 3574) (p 4157) (p 4405) (derived40810 p h) (h 11520)

theorem derived42462 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 3323) ∨ (¬ p 3425) ∨ (¬ p 3461) ∨ (¬ p 3659) ∨ (¬ p 4786) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step42462 (p 2027) (p 2331) (p 3323) (p 3425) (p 3461) (p 3659) (p 4786) (p 5123) (p 5558) (derived40810 p h) (h 11524)

theorem derived42463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3551) ∨ (¬ p 4042) ∨ (¬ p 4244) ∨ (¬ p 4986) :=
  ElevenRUP.step42463 (p 2027) (p 2619) (p 3551) (p 4042) (p 4244) (p 4986) (derived40810 p h) (h 11525)

theorem derived42464 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2531) ∨ (¬ p 3422) ∨ (¬ p 3497) ∨ (¬ p 3684) ∨ (¬ p 4702) :=
  ElevenRUP.step42464 (p 2027) (p 2510) (p 2531) (p 3422) (p 3497) (p 3684) (p 4702) (derived40810 p h) (h 11526)

theorem derived42465 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2578) ∨ (¬ p 2667) ∨ (¬ p 2727) ∨ (¬ p 3422) ∨ (¬ p 4154) ∨ (¬ p 4753) :=
  ElevenRUP.step42465 (p 2027) (p 2578) (p 2667) (p 2727) (p 3422) (p 4154) (p 4753) (derived40810 p h) (h 11527)

theorem derived42466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2745) ∨ (¬ p 2797) ∨ (¬ p 3549) ∨ (¬ p 3567) ∨ (¬ p 4245) :=
  ElevenRUP.step42466 (p 2027) (p 2307) (p 2745) (p 2797) (p 3549) (p 3567) (p 4245) (derived40810 p h) (h 11528)

theorem derived42468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2659) ∨ (¬ p 2870) ∨ (¬ p 3556) ∨ (¬ p 3698) ∨ (¬ p 3904) :=
  ElevenRUP.step42468 (p 2027) (p 2542) (p 2659) (p 2870) (p 3556) (p 3698) (p 3904) (derived40810 p h) (h 11530)

theorem derived42469 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2307) ∨ (¬ p 2459) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3684) ∨ (¬ p 4866) ∨ (¬ p 4948) ∨ (¬ p 5016) ∨ (¬ p 5059) :=
  ElevenRUP.step42469 (p 2027) (p 2177) (p 2307) (p 2459) (p 3055) (p 3366) (p 3684) (p 4866) (p 4948) (p 5016) (p 5059) (derived40810 p h) (h 11531)

theorem derived42470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2299) ∨ (¬ p 2319) ∨ (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 3662) ∨ (¬ p 3951) ∨ (¬ p 4208) ∨ (¬ p 5017) :=
  ElevenRUP.step42470 (p 2027) (p 2247) (p 2299) (p 2319) (p 2341) (p 2396) (p 3662) (p 3951) (p 4208) (p 5017) (derived40810 p h) (h 11532)

theorem derived42471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3516) ∨ (¬ p 3817) ∨ (¬ p 3819) ∨ (¬ p 4024) ∨ (¬ p 4105) ∨ (¬ p 4845) :=
  ElevenRUP.step42471 (p 2027) (p 3365) (p 3516) (p 3817) (p 3819) (p 4024) (p 4105) (p 4845) (derived40810 p h) (h 11533)

theorem derived42472 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 3688) ∨ (¬ p 3917) ∨ (¬ p 3954) ∨ (¬ p 4604) ∨ (¬ p 5190) :=
  ElevenRUP.step42472 (p 2027) (p 2230) (p 2373) (p 3146) (p 3688) (p 3917) (p 3954) (p 4604) (p 5190) (derived40810 p h) (h 11534)

theorem derived42473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 3222) ∨ (¬ p 3346) ∨ (¬ p 4154) ∨ (¬ p 4281) ∨ (¬ p 4972) :=
  ElevenRUP.step42473 (p 2027) (p 2662) (p 3222) (p 3346) (p 4154) (p 4281) (p 4972) (derived40810 p h) (h 11535)

theorem derived42475 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2933) ∨ (¬ p 3426) ∨ (¬ p 3434) ∨ (¬ p 3540) ∨ (¬ p 3817) ∨ (¬ p 4375) ∨ (¬ p 4727) :=
  ElevenRUP.step42475 (p 2027) (p 2933) (p 3426) (p 3434) (p 3540) (p 3817) (p 4375) (p 4727) (derived40810 p h) (h 11537)

theorem derived42479 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 3367) ∨ (¬ p 4242) ∨ (¬ p 4608) ∨ (¬ p 5369) :=
  ElevenRUP.step42479 (p 2027) (p 2850) (p 3367) (p 4242) (p 4608) (p 5369) (derived40810 p h) (h 11541)

theorem derived42480 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2751) ∨ (¬ p 3073) ∨ (¬ p 3572) ∨ (¬ p 3857) ∨ (¬ p 3859) ∨ (¬ p 3961) ∨ (¬ p 4155) :=
  ElevenRUP.step42480 (p 2027) (p 2751) (p 3073) (p 3572) (p 3857) (p 3859) (p 3961) (p 4155) (derived40810 p h) (h 11543)

theorem derived42481 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3063) ∨ (¬ p 3857) ∨ (¬ p 4197) ∨ (¬ p 5018) :=
  ElevenRUP.step42481 (p 2027) (p 2363) (p 3063) (p 3857) (p 4197) (p 5018) (derived40810 p h) (h 11544)

theorem derived42482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4318) ∨ (¬ p 4405) :=
  ElevenRUP.step42482 (p 2027) (p 3449) (p 3549) (p 3591) (p 4318) (p 4405) (derived40810 p h) (h 11545)

theorem derived42483 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3093) ∨ (¬ p 3365) ∨ (¬ p 3873) ∨ (¬ p 4870) :=
  ElevenRUP.step42483 (p 2027) (p 2737) (p 3093) (p 3365) (p 3873) (p 4870) (derived40810 p h) (h 11546)

theorem derived42484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 4315) ∨ (¬ p 4333) ∨ (¬ p 5661) ∨ (¬ p 5740) :=
  ElevenRUP.step42484 (p 2027) (p 2685) (p 4315) (p 4333) (p 5661) (p 5740) (derived40810 p h) (h 11547)

theorem derived42485 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2386) ∨ (¬ p 3684) ∨ (¬ p 4375) ∨ (¬ p 4717) :=
  ElevenRUP.step42485 (p 2027) (p 2122) (p 2313) (p 2386) (p 3684) (p 4375) (p 4717) (derived40810 p h) (h 11549)

theorem derived42486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 2507) ∨ (¬ p 3016) ∨ (¬ p 3309) ∨ (¬ p 3742) ∨ (¬ p 4279) :=
  ElevenRUP.step42486 (p 2027) (p 2312) (p 2507) (p 3016) (p 3309) (p 3742) (p 4279) (derived40810 p h) (h 11550)

theorem derived42488 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 2341) ∨ (¬ p 3309) ∨ (¬ p 3553) ∨ (¬ p 4067) ∨ (¬ p 4761) :=
  ElevenRUP.step42488 (p 2027) (p 2312) (p 2341) (p 3309) (p 3553) (p 4067) (p 4761) (derived40810 p h) (h 11552)

theorem derived42490 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3343) ∨ (¬ p 3389) ∨ (¬ p 3742) ∨ (¬ p 3954) ∨ (¬ p 4242) ∨ (¬ p 4332) ∨ (¬ p 4340) ∨ (¬ p 5190) :=
  ElevenRUP.step42490 (p 2027) (p 3343) (p 3389) (p 3742) (p 3954) (p 4242) (p 4332) (p 4340) (p 5190) (derived40810 p h) (h 11554)

theorem derived42491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4107) ∨ (¬ p 4322) ∨ (¬ p 4395) ∨ (¬ p 5190) :=
  ElevenRUP.step42491 (p 2027) (p 3276) (p 3355) (p 3549) (p 3591) (p 4107) (p 4322) (p 4395) (p 5190) (derived40810 p h) (h 11555)

theorem derived42493 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2743) ∨ (¬ p 2774) ∨ (¬ p 3537) ∨ (¬ p 4845) :=
  ElevenRUP.step42493 (p 2027) (p 2104) (p 2743) (p 2774) (p 3537) (p 4845) (derived40810 p h) (h 11557)

theorem derived42496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3389) ∨ (¬ p 3583) ∨ (¬ p 3694) ∨ (¬ p 3742) ∨ (¬ p 3954) ∨ (¬ p 4158) ∨ (¬ p 5190) :=
  ElevenRUP.step42496 (p 2027) (p 3083) (p 3389) (p 3583) (p 3694) (p 3742) (p 3954) (p 4158) (p 5190) (derived40810 p h) (h 11560)

theorem derived42497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3426) ∨ (¬ p 3568) ∨ (¬ p 4253) ∨ (¬ p 4260) ∨ (¬ p 4846) :=
  ElevenRUP.step42497 (p 2027) (p 3426) (p 3568) (p 4253) (p 4260) (p 4846) (derived40810 p h) (h 11561)

theorem derived42498 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 2751) ∨ (¬ p 2810) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4281) :=
  ElevenRUP.step42498 (p 2027) (p 2662) (p 2751) (p 2810) (p 2922) (p 3540) (p 4281) (derived40810 p h) (h 11562)

theorem derived42501 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3646) ∨ (¬ p 3950) ∨ (¬ p 3989) ∨ (¬ p 4347) :=
  ElevenRUP.step42501 (p 2027) (p 2145) (p 2449) (p 2685) (p 2696) (p 3646) (p 3950) (p 3989) (p 4347) (derived40810 p h) (h 11565)

theorem derived42503 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3093) ∨ (¬ p 3540) ∨ (¬ p 3541) ∨ (¬ p 4108) ∨ (¬ p 4870) :=
  ElevenRUP.step42503 (p 2027) (p 2922) (p 3093) (p 3540) (p 3541) (p 4108) (p 4870) (derived40810 p h) (h 11567)

theorem derived42504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3923) ∨ (¬ p 4137) ∨ (¬ p 4625) ∨ (¬ p 4870) :=
  ElevenRUP.step42504 (p 2027) (p 2352) (p 2449) (p 2685) (p 2696) (p 2753) (p 3923) (p 4137) (p 4625) (p 4870) (derived40810 p h) (h 11568)

theorem derived42508 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2630) ∨ (¬ p 3659) ∨ (¬ p 4066) ∨ (¬ p 4357) ∨ (¬ p 4650) :=
  ElevenRUP.step42508 (p 2027) (p 2341) (p 2630) (p 3659) (p 4066) (p 4357) (p 4650) (derived40810 p h) (h 11572)

theorem derived42509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2579) ∨ (¬ p 3051) ∨ (¬ p 3156) ∨ (¬ p 3422) ∨ (¬ p 3874) ∨ (¬ p 3905) ∨ (¬ p 4320) ∨ (¬ p 4434) :=
  ElevenRUP.step42509 (p 2027) (p 2139) (p 2579) (p 3051) (p 3156) (p 3422) (p 3874) (p 3905) (p 4320) (p 4434) (derived40810 p h) (h 11573)

theorem derived42510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3438) ∨ (¬ p 3449) ∨ (¬ p 3834) ∨ (¬ p 4181) ∨ (¬ p 5122) :=
  ElevenRUP.step42510 (p 2027) (p 3438) (p 3449) (p 3834) (p 4181) (p 5122) (derived40810 p h) (h 11574)

theorem derived42511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3422) ∨ (¬ p 3684) ∨ (¬ p 4173) ∨ (¬ p 4203) ∨ (¬ p 4629) :=
  ElevenRUP.step42511 (p 2027) (p 3422) (p 3684) (p 4173) (p 4203) (p 4629) (derived40810 p h) (h 11575)

theorem derived42512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2662) ∨ (¬ p 2745) ∨ (¬ p 3475) ∨ (¬ p 3641) ∨ (¬ p 4111) :=
  ElevenRUP.step42512 (p 2027) (p 2476) (p 2662) (p 2745) (p 3475) (p 3641) (p 4111) (derived40810 p h) (h 11576)

theorem derived42513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2850) ∨ (¬ p 4109) ∨ (¬ p 4173) ∨ (¬ p 4202) ∨ (¬ p 5214) :=
  ElevenRUP.step42513 (p 2027) (p 2156) (p 2850) (p 4109) (p 4173) (p 4202) (p 5214) (derived40810 p h) (h 11577)

theorem derived42514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2741) ∨ (¬ p 2811) ∨ (¬ p 2829) ∨ (¬ p 4111) ∨ (¬ p 4845) :=
  ElevenRUP.step42514 (p 2027) (p 2651) (p 2741) (p 2811) (p 2829) (p 4111) (p 4845) (derived40810 p h) (h 11578)

theorem derived42515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2312) ∨ (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 3984) ∨ (¬ p 4155) ∨ (¬ p 5225) :=
  ElevenRUP.step42515 (p 2027) (p 2122) (p 2312) (p 2641) (p 2996) (p 3984) (p 4155) (p 5225) (derived40810 p h) (h 11579)

theorem derived42522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3571) ∨ (¬ p 3670) ∨ (¬ p 4235) ∨ (¬ p 4321) ∨ (¬ p 4885) ∨ (¬ p 5031) ∨ (¬ p 5357) :=
  ElevenRUP.step42522 (p 2027) (p 3571) (p 3670) (p 4235) (p 4321) (p 4885) (p 5031) (p 5357) (derived40810 p h) (h 11591)

theorem derived42526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2761) ∨ (¬ p 2982) ∨ (¬ p 3379) ∨ (¬ p 3946) ∨ (¬ p 4191) ∨ (¬ p 4395) ∨ (¬ p 5021) :=
  ElevenRUP.step42526 (p 2027) (p 2406) (p 2761) (p 2982) (p 3379) (p 3946) (p 4191) (p 4395) (p 5021) (derived40810 p h) (h 11595)

theorem derived42529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 3031) ∨ (¬ p 3516) ∨ (¬ p 3817) ∨ (¬ p 4066) ∨ (¬ p 4650) :=
  ElevenRUP.step42529 (p 2027) (p 2727) (p 3031) (p 3516) (p 3817) (p 4066) (p 4650) (derived40810 p h) (h 11598)

theorem derived42531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 3097) ∨ (¬ p 3646) ∨ (¬ p 4405) ∨ (¬ p 4441) :=
  ElevenRUP.step42531 (p 2027) (p 2220) (p 3097) (p 3646) (p 4405) (p 4441) (derived40810 p h) (h 11600)

theorem derived42533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2588) ∨ (¬ p 3550) ∨ (¬ p 4107) ∨ (¬ p 4666) :=
  ElevenRUP.step42533 (p 2027) (p 2352) (p 2588) (p 3550) (p 4107) (p 4666) (derived40810 p h) (h 11602)

theorem derived42535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2780) ∨ (¬ p 3956) ∨ (¬ p 4326) ∨ (¬ p 5225) :=
  ElevenRUP.step42535 (p 2027) (p 2098) (p 2780) (p 3956) (p 4326) (p 5225) (derived40810 p h) (h 11604)

theorem derived42537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3543) ∨ (¬ p 3742) ∨ (¬ p 4107) ∨ (¬ p 4279) ∨ (¬ p 4404) ∨ (¬ p 4427) ∨ (¬ p 4666) :=
  ElevenRUP.step42537 (p 2027) (p 3083) (p 3543) (p 3742) (p 4107) (p 4279) (p 4404) (p 4427) (p 4666) (derived40810 p h) (h 11606)

theorem derived42538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2507) ∨ (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 3956) ∨ (¬ p 4318) :=
  ElevenRUP.step42538 (p 2027) (p 2507) (p 3449) (p 3591) (p 3956) (p 4318) (derived40810 p h) (h 11607)

theorem derived42539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2922) ∨ (¬ p 4710) ∨ (¬ p 5472) ∨ (¬ p 5514) :=
  ElevenRUP.step42539 (p 2027) (p 2499) (p 2922) (p 4710) (p 5472) (p 5514) (derived40810 p h) (h 11608)

theorem derived42540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3212) ∨ (¬ p 4120) ∨ (¬ p 4340) ∨ (¬ p 4742) :=
  ElevenRUP.step42540 (p 2027) (p 2532) (p 3212) (p 4120) (p 4340) (p 4742) (derived40810 p h) (h 11609)

theorem derived42541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3744) ∨ (¬ p 4140) ∨ (¬ p 4173) ∨ (¬ p 4282) ∨ (¬ p 4620) :=
  ElevenRUP.step42541 (p 2027) (p 2901) (p 3744) (p 4140) (p 4173) (p 4282) (p 4620) (derived40810 p h) (h 11610)

theorem derived42542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2427) ∨ (¬ p 3691) ∨ (¬ p 4261) ∨ (¬ p 4492) ∨ (¬ p 4590) ∨ (¬ p 4629) :=
  ElevenRUP.step42542 (p 2027) (p 2088) (p 2427) (p 3691) (p 4261) (p 4492) (p 4590) (p 4629) (derived40810 p h) (h 11611)

theorem derived42544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2274) ∨ (¬ p 2717) ∨ (¬ p 3426) ∨ (¬ p 3551) ∨ (¬ p 4137) ∨ (¬ p 4342) ∨ (¬ p 4620) ∨ (¬ p 5210) :=
  ElevenRUP.step42544 (p 2027) (p 2192) (p 2210) (p 2274) (p 2717) (p 3426) (p 3551) (p 4137) (p 4342) (p 4620) (p 5210) (derived40810 p h) (h 11613)

theorem derived42547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2630) ∨ (¬ p 3567) ∨ (¬ p 4114) ∨ (¬ p 4340) ∨ (¬ p 4364) ∨ (¬ p 4972) :=
  ElevenRUP.step42547 (p 2027) (p 2088) (p 2630) (p 3567) (p 4114) (p 4340) (p 4364) (p 4972) (derived40810 p h) (h 11616)

theorem derived42548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2641) ∨ (¬ p 2751) ∨ (¬ p 3567) ∨ (¬ p 3822) ∨ (¬ p 4841) :=
  ElevenRUP.step42548 (p 2027) (p 2307) (p 2641) (p 2751) (p 3567) (p 3822) (p 4841) (derived40810 p h) (h 11617)

theorem derived42549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2589) ∨ (¬ p 3905) ∨ (¬ p 4110) :=
  ElevenRUP.step42549 (p 2027) (p 2139) (p 2156) (p 2589) (p 3905) (p 4110) (derived40810 p h) (h 11618)

theorem derived42551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2518) ∨ (¬ p 3379) ∨ (¬ p 3555) ∨ (¬ p 4034) ∨ (¬ p 4610) :=
  ElevenRUP.step42551 (p 2027) (p 2518) (p 3379) (p 3555) (p 4034) (p 4610) (derived40810 p h) (h 11621)

theorem derived42552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4075) ∨ (¬ p 4320) ∨ (¬ p 4338) ∨ (¬ p 4452) ∨ (¬ p 4960) ∨ (¬ p 5660) :=
  ElevenRUP.step42552 (p 2027) (p 4075) (p 4320) (p 4338) (p 4452) (p 4960) (p 5660) (derived40810 p h) (h 11622)

theorem derived42553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2373) ∨ (¬ p 2396) ∨ (¬ p 3951) ∨ (¬ p 4117) ∨ (¬ p 4120) ∨ (¬ p 4948) :=
  ElevenRUP.step42553 (p 2027) (p 2145) (p 2295) (p 2331) (p 2373) (p 2396) (p 3951) (p 4117) (p 4120) (p 4948) (derived40810 p h) (h 11623)

theorem derived42554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3568) ∨ (¬ p 4075) ∨ (¬ p 4260) ∨ (¬ p 4452) ∨ (¬ p 4761) :=
  ElevenRUP.step42554 (p 2027) (p 3568) (p 4075) (p 4260) (p 4452) (p 4761) (derived40810 p h) (h 11624)

theorem derived42555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3324) ∨ (¬ p 3449) ∨ (¬ p 3591) ∨ (¬ p 4318) ∨ (¬ p 4761) :=
  ElevenRUP.step42555 (p 2027) (p 3324) (p 3449) (p 3591) (p 4318) (p 4761) (derived40810 p h) (h 11625)

theorem derived42556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2145) ∨ (¬ p 2307) ∨ (¬ p 2373) ∨ (¬ p 2786) ∨ (¬ p 3323) ∨ (¬ p 3568) ∨ (¬ p 4120) ∨ (¬ p 4368) ∨ (¬ p 4948) :=
  ElevenRUP.step42556 (p 2027) (p 2145) (p 2307) (p 2373) (p 2786) (p 3323) (p 3568) (p 4120) (p 4368) (p 4948) (derived40810 p h) (h 11626)

theorem derived42557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3038) ∨ (¬ p 3631) ∨ (¬ p 3947) ∨ (¬ p 4111) ∨ (¬ p 4652) :=
  ElevenRUP.step42557 (p 2027) (p 3038) (p 3631) (p 3947) (p 4111) (p 4652) (derived40810 p h) (h 11627)

theorem derived42559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2751) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3758) ∨ (¬ p 4392) :=
  ElevenRUP.step42559 (p 2027) (p 2156) (p 2751) (p 2951) (p 2992) (p 3758) (p 4392) (derived40810 p h) (h 11629)

theorem derived42560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2696) ∨ (¬ p 2751) ∨ (¬ p 2992) ∨ (¬ p 4316) :=
  ElevenRUP.step42560 (p 2027) (p 2138) (p 2696) (p 2751) (p 2992) (p 4316) (derived40810 p h) (h 11630)

theorem derived42561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2641) ∨ (¬ p 2751) ∨ (¬ p 3567) ∨ (¬ p 4358) ∨ (¬ p 4841) :=
  ElevenRUP.step42561 (p 2027) (p 2383) (p 2641) (p 2751) (p 3567) (p 4358) (p 4841) (derived40810 p h) (h 11631)

theorem derived42564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2505) ∨ (¬ p 3238) ∨ (¬ p 4053) ∨ (¬ p 4717) ∨ (¬ p 5514) :=
  ElevenRUP.step42564 (p 2027) (p 2505) (p 3238) (p 4053) (p 4717) (p 5514) (derived40810 p h) (h 11634)

theorem derived42565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 3537) ∨ (¬ p 3585) ∨ (¬ p 4727) ∨ (¬ p 5373) :=
  ElevenRUP.step42565 (p 2027) (p 2476) (p 3537) (p 3585) (p 4727) (p 5373) (derived40810 p h) (h 11635)

theorem derived42566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3461) ∨ (¬ p 3746) ∨ (¬ p 4425) ∨ (¬ p 4620) :=
  ElevenRUP.step42566 (p 2027) (p 2553) (p 3461) (p 3746) (p 4425) (p 4620) (derived40810 p h) (h 11636)

theorem derived42567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2103) ∨ (¬ p 3537) ∨ (¬ p 3688) ∨ (¬ p 3989) ∨ (¬ p 4113) ∨ (¬ p 4401) :=
  ElevenRUP.step42567 (p 2027) (p 2103) (p 3537) (p 3688) (p 3989) (p 4113) (p 4401) (derived40810 p h) (h 11637)

theorem derived42568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3742) ∨ (¬ p 4253) ∨ (¬ p 4753) ∨ (¬ p 5085) ∨ (¬ p 5503) :=
  ElevenRUP.step42568 (p 2027) (p 3742) (p 4253) (p 4753) (p 5085) (p 5503) (derived40810 p h) (h 11638)

theorem derived42569 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 3237) ∨ (¬ p 3680) ∨ (¬ p 4425) ∨ (¬ p 4885) :=
  ElevenRUP.step42569 (p 2027) (p 3105) (p 3237) (p 3680) (p 4425) (p 4885) (derived40810 p h) (h 11639)

theorem derived42571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2298) ∨ (¬ p 2641) ∨ (¬ p 2668) ∨ (¬ p 2996) ∨ (¬ p 4405) :=
  ElevenRUP.step42571 (p 2027) (p 2298) (p 2641) (p 2668) (p 2996) (p 4405) (derived40810 p h) (h 11642)

theorem derived42572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2363) ∨ (¬ p 3325) ∨ (¬ p 3585) ∨ (¬ p 3874) ∨ (¬ p 3954) ∨ (¬ p 4348) ∨ (¬ p 4438) ∨ (¬ p 5017) :=
  ElevenRUP.step42572 (p 2027) (p 2307) (p 2363) (p 3325) (p 3585) (p 3874) (p 3954) (p 4348) (p 4438) (p 5017) (derived40810 p h) (h 11643)

theorem derived42574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 2810) ∨ (¬ p 3146) ∨ (¬ p 3365) ∨ (¬ p 4256) ∨ (¬ p 4348) ∨ (¬ p 4438) :=
  ElevenRUP.step42574 (p 2027) (p 2139) (p 2220) (p 2810) (p 3146) (p 3365) (p 4256) (p 4348) (p 4438) (derived40810 p h) (h 11645)

theorem derived42575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2750) ∨ (¬ p 3414) ∨ (¬ p 3449) ∨ (¬ p 3553) ∨ (¬ p 3954) ∨ (¬ p 4181) ∨ (¬ p 4348) ∨ (¬ p 5122) :=
  ElevenRUP.step42575 (p 2027) (p 2252) (p 2750) (p 3414) (p 3449) (p 3553) (p 3954) (p 4181) (p 4348) (p 5122) (derived40810 p h) (h 11646)

theorem derived42576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 2245) ∨ (¬ p 2274) ∨ (¬ p 2528) ∨ (¬ p 3172) ∨ (¬ p 4118) ∨ (¬ p 4438) ∨ (¬ p 4521) :=
  ElevenRUP.step42576 (p 2027) (p 2156) (p 2177) (p 2245) (p 2274) (p 2528) (p 3172) (p 4118) (p 4438) (p 4521) (derived40810 p h) (h 11647)

theorem derived42577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 2274) ∨ (¬ p 2608) ∨ (¬ p 3370) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4377) ∨ (¬ p 4666) :=
  ElevenRUP.step42577 (p 2027) (p 2156) (p 2177) (p 2274) (p 2608) (p 3370) (p 3817) (p 4366) (p 4377) (p 4666) (derived40810 p h) (h 11648)

theorem derived42579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3105) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 3680) ∨ (¬ p 4789) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step42579 (p 2027) (p 2132) (p 3105) (p 3414) (p 3553) (p 3680) (p 4789) (p 5123) (p 5558) (derived40810 p h) (h 11650)

theorem derived42580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 3051) ∨ (¬ p 3105) ∨ (¬ p 3370) ∨ (¬ p 3371) ∨ (¬ p 4244) ∨ (¬ p 4256) ∨ (¬ p 4450) :=
  ElevenRUP.step42580 (p 2027) (p 2252) (p 2534) (p 2657) (p 2750) (p 3051) (p 3105) (p 3370) (p 3371) (p 4244) (p 4256) (p 4450) (derived40810 p h) (h 11651)

theorem derived42582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3051) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 4195) ∨ (¬ p 4377) ∨ (¬ p 5254) ∨ (¬ p 5717) :=
  ElevenRUP.step42582 (p 2027) (p 2761) (p 3051) (p 3246) (p 3365) (p 3366) (p 3370) (p 4195) (p 4377) (p 5254) (p 5717) (derived40810 p h) (h 11653)

theorem derived42583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2509) ∨ (¬ p 3555) ∨ (¬ p 4079) ∨ (¬ p 4257) ∨ (¬ p 4377) :=
  ElevenRUP.step42583 (p 2027) (p 2470) (p 2509) (p 3555) (p 4079) (p 4257) (p 4377) (derived40810 p h) (h 11654)

theorem derived42585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2707) ∨ (¬ p 2750) ∨ (¬ p 3425) ∨ (¬ p 3873) :=
  ElevenRUP.step42585 (p 2027) (p 2241) (p 2707) (p 2750) (p 3425) (p 3873) (derived40810 p h) (h 11656)

theorem derived42586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3923) ∨ (¬ p 3954) ∨ (¬ p 4870) ∨ (¬ p 5020) :=
  ElevenRUP.step42586 (p 2027) (p 2383) (p 3923) (p 3954) (p 4870) (p 5020) (derived40810 p h) (h 11657)

theorem derived42587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2588) ∨ (¬ p 4149) ∨ (¬ p 4405) ∨ (¬ p 5580) :=
  ElevenRUP.step42587 (p 2027) (p 2510) (p 2588) (p 4149) (p 4405) (p 5580) (derived40810 p h) (h 11658)

theorem derived42589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2717) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3471) ∨ (¬ p 3860) ∨ (¬ p 3941) ∨ (¬ p 4261) ∨ (¬ p 5122) :=
  ElevenRUP.step42589 (p 2027) (p 2241) (p 2717) (p 2750) (p 2753) (p 3471) (p 3860) (p 3941) (p 4261) (p 5122) (derived40810 p h) (h 11660)

theorem derived42591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2241) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3362) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) :=
  ElevenRUP.step42591 (p 2027) (p 2177) (p 2241) (p 2553) (p 2573) (p 2750) (p 2753) (p 3362) (p 3817) (p 4366) (p 4666) (derived40810 p h) (h 11662)

theorem derived42592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3461) ∨ (¬ p 3519) ∨ (¬ p 3564) ∨ (¬ p 3877) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5600) :=
  ElevenRUP.step42592 (p 2027) (p 2573) (p 3365) (p 3366) (p 3461) (p 3519) (p 3564) (p 3877) (p 4376) (p 5123) (p 5600) (derived40810 p h) (h 11663)

theorem derived42593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2982) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3680) ∨ (¬ p 3877) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5600) :=
  ElevenRUP.step42593 (p 2027) (p 2230) (p 2982) (p 3365) (p 3366) (p 3519) (p 3680) (p 3877) (p 4376) (p 5123) (p 5600) (derived40810 p h) (h 11664)

theorem derived42594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 3452) ∨ (¬ p 3923) ∨ (¬ p 3953) ∨ (¬ p 4376) ∨ (¬ p 5020) :=
  ElevenRUP.step42594 (p 2027) (p 2383) (p 3452) (p 3923) (p 3953) (p 4376) (p 5020) (derived40810 p h) (h 11665)

theorem derived42595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3366) ∨ (¬ p 3452) ∨ (¬ p 3707) ∨ (¬ p 3830) ∨ (¬ p 4358) ∨ (¬ p 4376) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step42595 (p 2027) (p 2780) (p 3366) (p 3452) (p 3707) (p 3830) (p 4358) (p 4376) (p 5123) (p 5580) (derived40810 p h) (h 11666)

theorem derived42596 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3292) ∨ (¬ p 3670) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 5236) ∨ (¬ p 5284) :=
  ElevenRUP.step42596 (p 2027) (p 2230) (p 2427) (p 3246) (p 3292) (p 3670) (p 4236) (p 4419) (p 5236) (p 5284) (derived40810 p h) (h 11667)

theorem derived42597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 3005) ∨ (¬ p 3172) ∨ (¬ p 3246) ∨ (¬ p 4035) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 4663) :=
  ElevenRUP.step42597 (p 2027) (p 2230) (p 2427) (p 3005) (p 3172) (p 3246) (p 4035) (p 4236) (p 4419) (p 4663) (derived40810 p h) (h 11668)

theorem derived42598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 4419) ∨ (¬ p 4666) :=
  ElevenRUP.step42598 (p 2027) (p 2230) (p 2427) (p 2881) (p 3365) (p 3572) (p 3947) (p 4419) (p 4666) (derived40810 p h) (h 11669)

theorem derived42599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2963) ∨ (¬ p 3246) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3950) ∨ (¬ p 4236) ∨ (¬ p 4328) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4376) :=
  ElevenRUP.step42599 (p 2027) (p 2230) (p 2427) (p 2963) (p 3246) (p 3366) (p 3519) (p 3950) (p 4236) (p 4328) (p 4347) (p 4358) (p 4376) (derived40810 p h) (h 11670)

theorem derived42600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 2911) ∨ (¬ p 2933) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4376) ∨ (¬ p 4666) :=
  ElevenRUP.step42600 (p 2027) (p 2780) (p 2911) (p 2933) (p 3366) (p 3399) (p 3452) (p 3822) (p 4107) (p 4376) (p 4666) (derived40810 p h) (h 11671)

theorem derived42604 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3584) ∨ (¬ p 4137) ∨ (¬ p 4620) ∨ (¬ p 4710) :=
  ElevenRUP.step42604 (p 2027) (p 3201) (p 3584) (p 4137) (p 4620) (p 4710) (derived40810 p h) (h 11675)

theorem derived42605 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3172) ∨ (¬ p 3737) ∨ (¬ p 4118) ∨ (¬ p 4444) ∨ (¬ p 4789) ∨ (¬ p 5250) :=
  ElevenRUP.step42605 (p 2027) (p 2132) (p 2860) (p 3172) (p 3737) (p 4118) (p 4444) (p 4789) (p 5250) (derived40810 p h) (h 11676)

theorem derived42606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3569) ∨ (¬ p 3584) ∨ (¬ p 4140) ∨ (¬ p 5472) ∨ (¬ p 5514) :=
  ElevenRUP.step42606 (p 2027) (p 3201) (p 3569) (p 3584) (p 4140) (p 5472) (p 5514) (derived40810 p h) (h 11677)

theorem derived42607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4330) :=
  ElevenRUP.step42607 (p 2027) (p 2132) (p 2241) (p 2750) (p 2753) (p 2860) (p 3125) (p 3860) (p 4261) (p 4330) (derived40810 p h) (h 11678)

theorem derived42609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 3034) ∨ (¬ p 3399) ∨ (¬ p 3834) ∨ (¬ p 5358) :=
  ElevenRUP.step42609 (p 2027) (p 2449) (p 3034) (p 3399) (p 3834) (p 5358) (derived40810 p h) (h 11680)

theorem derived42610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3266) ∨ (¬ p 3292) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 4330) ∨ (¬ p 4789) ∨ (¬ p 5284) :=
  ElevenRUP.step42610 (p 2027) (p 2598) (p 3266) (p 3292) (p 3422) (p 3564) (p 4330) (p 4789) (p 5284) (derived40810 p h) (h 11681)

theorem derived42611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2750) ∨ (¬ p 2807) ∨ (¬ p 2996) ∨ (¬ p 3954) :=
  ElevenRUP.step42611 (p 2027) (p 2253) (p 2750) (p 2807) (p 2996) (p 3954) (derived40810 p h) (h 11682)

theorem derived42612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3027) ∨ (¬ p 3452) ∨ (¬ p 4116) ∨ (¬ p 4652) :=
  ElevenRUP.step42612 (p 2027) (p 2241) (p 3027) (p 3452) (p 4116) (p 4652) (derived40810 p h) (h 11683)

theorem derived42613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 3371) ∨ (¬ p 3556) :=
  ElevenRUP.step42613 (p 2027) (p 2241) (p 2750) (p 2891) (p 3369) (p 3371) (p 3556) (derived40810 p h) (h 11684)

theorem derived42614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3276) ∨ (¬ p 3333) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step42614 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 3276) (p 3333) (p 3414) (p 3553) (p 5123) (p 5558) (derived40810 p h) (h 11685)

theorem derived42615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2936) ∨ (¬ p 3201) ∨ (¬ p 3631) ∨ (¬ p 4636) ∨ (¬ p 5160) :=
  ElevenRUP.step42615 (p 2027) (p 2936) (p 3201) (p 3631) (p 4636) (p 5160) (derived40810 p h) (h 11686)

theorem derived42617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2972) ∨ (¬ p 3369) ∨ (¬ p 3371) ∨ (¬ p 4032) :=
  ElevenRUP.step42617 (p 2027) (p 2241) (p 2750) (p 2972) (p 3369) (p 3371) (p 4032) (derived40810 p h) (h 11688)

theorem derived42618 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2850) ∨ (¬ p 2963) ∨ (¬ p 2982) ∨ (¬ p 3324) ∨ (¬ p 4347) ∨ (¬ p 4450) :=
  ElevenRUP.step42618 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2850) (p 2963) (p 2982) (p 3324) (p 4347) (p 4450) (derived40810 p h) (h 11689)

theorem derived42619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 3276) ∨ (¬ p 3324) ∨ (¬ p 3333) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step42619 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2963) (p 3276) (p 3324) (p 3333) (p 5123) (p 5580) (derived40810 p h) (h 11690)

theorem derived42621 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 4009) ∨ (¬ p 4774) ∨ (¬ p 5514) ∨ (¬ p 5579) :=
  ElevenRUP.step42621 (p 2027) (p 2352) (p 4009) (p 4774) (p 5514) (p 5579) (derived40810 p h) (h 11692)

theorem derived42622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 3584) ∨ (¬ p 3641) ∨ (¬ p 4420) ∨ (¬ p 5190) :=
  ElevenRUP.step42622 (p 2027) (p 2573) (p 3486) (p 3555) (p 3570) (p 3584) (p 3641) (p 4420) (p 5190) (derived40810 p h) (h 11693)

theorem derived42623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2481) ∨ (¬ p 2936) ∨ (¬ p 3201) ∨ (¬ p 3527) ∨ (¬ p 3874) ∨ (¬ p 3960) :=
  ElevenRUP.step42623 (p 2027) (p 2481) (p 2936) (p 3201) (p 3527) (p 3874) (p 3960) (derived40810 p h) (h 11694)

theorem derived42624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 2946) ∨ (¬ p 4241) ∨ (¬ p 4256) ∨ (¬ p 4608) :=
  ElevenRUP.step42624 (p 2027) (p 2657) (p 2946) (p 4241) (p 4256) (p 4608) (derived40810 p h) (h 11695)

theorem derived42627 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 3684) ∨ (¬ p 3880) ∨ (¬ p 4399) ∨ (¬ p 4730) :=
  ElevenRUP.step42627 (p 2027) (p 2220) (p 3684) (p 3880) (p 4399) (p 4730) (derived40810 p h) (h 11698)

theorem derived42628 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3286) ∨ (¬ p 3414) ∨ (¬ p 3690) ∨ (¬ p 4362) ∨ (¬ p 5233) ∨ (¬ p 5454) :=
  ElevenRUP.step42628 (p 2027) (p 3286) (p 3414) (p 3690) (p 4362) (p 5233) (p 5454) (derived40810 p h) (h 11699)

theorem derived42631 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 3246) ∨ (¬ p 3554) ∨ (¬ p 3817) ∨ (¬ p 4555) :=
  ElevenRUP.step42631 (p 2027) (p 2192) (p 3246) (p 3554) (p 3817) (p 4555) (derived40810 p h) (h 11702)

theorem derived42632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2901) ∨ (¬ p 4366) ∨ (¬ p 4909) ∨ (¬ p 4957) :=
  ElevenRUP.step42632 (p 2027) (p 2210) (p 2901) (p 4366) (p 4909) (p 4957) (derived40810 p h) (h 11703)

theorem derived42633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3115) ∨ (¬ p 3834) ∨ (¬ p 4388) ∨ (¬ p 4957) :=
  ElevenRUP.step42633 (p 2027) (p 2210) (p 3115) (p 3834) (p 4388) (p 4957) (derived40810 p h) (h 11705)

theorem derived42635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3333) ∨ (¬ p 3362) ∨ (¬ p 3389) ∨ (¬ p 3876) ∨ (¬ p 4332) ∨ (¬ p 4347) ∨ (¬ p 4789) :=
  ElevenRUP.step42635 (p 2027) (p 2963) (p 3324) (p 3333) (p 3362) (p 3389) (p 3876) (p 4332) (p 4347) (p 4789) (derived40810 p h) (h 11707)

theorem derived42636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2657) ∨ (¬ p 3146) ∨ (¬ p 3574) ∨ (¬ p 4137) ∨ (¬ p 4604) ∨ (¬ p 4789) :=
  ElevenRUP.step42636 (p 2027) (p 2132) (p 2619) (p 2657) (p 3146) (p 3574) (p 4137) (p 4604) (p 4789) (derived40810 p h) (h 11709)

theorem derived42637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 3497) ∨ (¬ p 4129) ∨ (¬ p 4132) ∨ (¬ p 5564) :=
  ElevenRUP.step42637 (p 2027) (p 2901) (p 3497) (p 4129) (p 4132) (p 5564) (derived40810 p h) (h 11710)

theorem derived42638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3438) ∨ (¬ p 3449) ∨ (¬ p 3834) ∨ (¬ p 4494) :=
  ElevenRUP.step42638 (p 2027) (p 3146) (p 3438) (p 3449) (p 3834) (p 4494) (derived40810 p h) (h 11711)

theorem derived42639 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2936) ∨ (¬ p 3830) ∨ (¬ p 4278) ∨ (¬ p 4366) ∨ (¬ p 5362) :=
  ElevenRUP.step42639 (p 2027) (p 2936) (p 3830) (p 4278) (p 4366) (p 5362) (derived40810 p h) (h 11712)

theorem derived42640 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2122) ∨ (¬ p 2774) ∨ (¬ p 3537) :=
  ElevenRUP.step42640 (p 1975) (p 2027) (p 2104) (p 2114) (p 2122) (p 2774) (p 3537) (h 2135) (derived40810 p h) (derived40864 p h) (h 11730)

theorem derived42641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (p 2146) :=
  ElevenRUP.step42641 (p 1976) (p 2138) (p 2146) (p 2148) (h 2136) (derived40865 p h) (h 11748)

theorem derived42642 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2563) ∨ (¬ p 3555) ∨ (¬ p 4173) :=
  ElevenRUP.step42642 (p 1977) (p 2027) (p 2202) (p 2241) (p 2563) (p 3555) (p 4173) (h 2137) (derived40810 p h) (derived40867 p h) (h 11834)

theorem derived42643 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (p 4533) :=
  ElevenRUP.step42643 (p 1978) (p 2230) (p 2233) (p 4533) (h 2138) (derived40868 p h) (h 11887)

theorem derived42644 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3952) ∨ (p 4560) :=
  ElevenRUP.step42644 (p 1979) (p 2287) (p 3952) (p 4560) (h 2139) (derived40869 p h) (h 11939)

theorem derived42645 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2352) ∨ (¬ p 2573) ∨ (¬ p 3989) :=
  ElevenRUP.step42645 (p 1975) (p 2027) (p 2233) (p 2274) (p 2352) (p 2573) (p 3989) (h 2135) (derived40810 p h) (derived40868 p h) (h 12008)

theorem derived42646 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3568) ∨ (p 4361) :=
  ElevenRUP.step42646 (p 1980) (p 2355) (p 3568) (p 4361) (h 2140) (derived40872 p h) (h 12009)

theorem derived42647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 4347) :=
  ElevenRUP.step42647 (p 1981) (p 2027) (p 2230) (p 2233) (p 2373) (p 3146) (p 4347) (h 2141) (derived40810 p h) (derived40868 p h) (h 12027)

theorem derived42648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2230) ∨ (¬ p 2363) ∨ (¬ p 2563) :=
  ElevenRUP.step42648 (p 1982) (p 2027) (p 2187) (p 2230) (p 2233) (p 2363) (p 2563) (h 2142) (derived40810 p h) (derived40868 p h) (h 12028)

theorem derived42649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2284) ∨ (¬ p 2553) ∨ (¬ p 3956) :=
  ElevenRUP.step42649 (p 1975) (p 2027) (p 2187) (p 2284) (p 2388) (p 2553) (p 3956) (h 2135) (derived40810 p h) (derived40873 p h) (h 12063)

theorem derived42650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3238) ∨ (¬ p 3519) :=
  ElevenRUP.step42650 (p 1983) (p 2027) (p 2202) (p 2396) (p 2553) (p 2573) (p 3238) (p 3519) (h 2143) (derived40810 p h) (derived40867 p h) (h 12081)

theorem derived42651 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2406) ∨ (¬ p 2573) ∨ (¬ p 2589) ∨ (¬ p 4203) :=
  ElevenRUP.step42651 (p 1981) (p 2027) (p 2187) (p 2406) (p 2409) (p 2573) (p 2589) (p 4203) (h 2141) (derived40810 p h) (derived40874 p h) (h 12099)

theorem derived42652 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2589) ∨ (¬ p 4347) :=
  ElevenRUP.step42652 (p 1981) (p 2027) (p 2202) (p 2470) (p 2528) (p 2589) (p 4347) (h 2141) (derived40810 p h) (derived40867 p h) (h 12185)

theorem derived42653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2518) ∨ (¬ p 2553) ∨ (¬ p 2573) :=
  ElevenRUP.step42653 (p 1975) (p 2027) (p 2409) (p 2476) (p 2518) (p 2553) (p 2573) (h 2135) (derived40810 p h) (derived40874 p h) (h 12204)

theorem derived42654 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2589) :=
  ElevenRUP.step42654 (p 1975) (p 2027) (p 2542) (p 2545) (p 2553) (p 2573) (p 2589) (h 2135) (derived40810 p h) (derived40876 p h) (h 12239)

theorem derived42655 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2299) ∨ (¬ p 3568) ∨ (¬ p 4154) :=
  ElevenRUP.step42655 (p 1984) (p 2027) (p 2247) (p 2299) (p 2633) (p 3568) (p 4154) (h 2144) (derived40810 p h) (derived40879 p h) (h 12342)

theorem derived42656 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2811) ∨ (p 4790) :=
  ElevenRUP.step42656 (p 1977) (p 2241) (p 2699) (p 2811) (p 4790) (h 2137) (derived40881 p h) (h 12411)

theorem derived42659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3822) ∨ (¬ p 4107) ∨ (¬ p 4381) :=
  ElevenRUP.step42659 (p 1976) (p 2027) (p 2764) (p 2780) (p 3822) (p 4107) (p 4381) (h 2136) (derived40810 p h) (derived40882 p h) (h 12482)

theorem derived42660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (p 4556) :=
  ElevenRUP.step42660 (p 1985) (p 2274) (p 2765) (p 4556) (h 2145) (derived40883 p h) (h 12483)

theorem derived42661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2780) ∨ (¬ p 3822) ∨ (¬ p 4348) :=
  ElevenRUP.step42661 (p 1976) (p 2027) (p 2299) (p 2766) (p 2780) (p 3822) (p 4348) (h 2136) (derived40810 p h) (derived40884 p h) (h 12484)

theorem derived42663 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2396) ∨ (¬ p 2891) ∨ (¬ p 4140) ∨ (¬ p 4173) :=
  ElevenRUP.step42663 (p 1983) (p 2027) (p 2148) (p 2156) (p 2396) (p 2891) (p 4140) (p 4173) (h 2143) (derived40810 p h) (derived40865 p h) (h 12522)

theorem derived42664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2274) ∨ (¬ p 2396) :=
  ElevenRUP.step42664 (p 1983) (p 2027) (p 2192) (p 2210) (p 2274) (p 2396) (p 2699) (h 2143) (derived40810 p h) (derived40881 p h) (h 12523)

theorem derived42665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2608) ∨ (¬ p 2819) ∨ (¬ p 2829) :=
  ElevenRUP.step42665 (p 1982) (p 2027) (p 2363) (p 2608) (p 2699) (p 2819) (p 2829) (h 2142) (derived40810 p h) (derived40881 p h) (h 12541)

theorem derived42666 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 2860) :=
  ElevenRUP.step42666 (p 1982) (p 2027) (p 2132) (p 2187) (p 2363) (p 2611) (p 2860) (h 2142) (derived40810 p h) (derived40877 p h) (h 12610)

theorem derived42667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2717) :=
  ElevenRUP.step42667 (p 1982) (p 2027) (p 2459) (p 2608) (p 2699) (p 2707) (p 2717) (h 2142) (derived40810 p h) (derived40881 p h) (h 12629)

theorem derived42668 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3414) ∨ (¬ p 3644) ∨ (¬ p 3740) ∨ (¬ p 4111) :=
  ElevenRUP.step42668 (p 1977) (p 2027) (p 2633) (p 2651) (p 3414) (p 3644) (p 3740) (p 4111) (h 2137) (derived40810 p h) (derived40879 p h) (h 12698)

theorem derived42669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 2952) ∨ (¬ p 3879) ∨ (¬ p 4235) :=
  ElevenRUP.step42669 (p 1987) (p 2027) (p 2651) (p 2810) (p 2938) (p 2952) (p 3879) (p 4235) (h 2147) (derived40810 p h) (derived40888 p h) (h 12699)

theorem derived42671 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2982) ∨ (¬ p 4110) ∨ (¬ p 4363) :=
  ElevenRUP.step42671 (p 1985) (p 2027) (p 2765) (p 2891) (p 2982) (p 4110) (p 4363) (h 2145) (derived40810 p h) (derived40883 p h) (h 12718)

theorem derived42672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2952) ∨ (¬ p 3952) ∨ (¬ p 4111) :=
  ElevenRUP.step42672 (p 1977) (p 2027) (p 2651) (p 2765) (p 2952) (p 3952) (p 4111) (h 2137) (derived40810 p h) (derived40883 p h) (h 12736)

theorem derived42673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (p 4558) :=
  ElevenRUP.step42673 (p 1985) (p 2997) (p 3097) (p 4558) (h 2145) (derived40890 p h) (h 12754)

theorem derived42675 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 4110) ∨ (¬ p 4111) ∨ (¬ p 4320) ∨ (¬ p 4700) :=
  ElevenRUP.step42675 (p 1977) (p 2027) (p 2427) (p 2765) (p 4110) (p 4111) (p 4320) (p 4700) (h 2137) (derived40810 p h) (derived40883 p h) (h 12756)

theorem derived42676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2662) ∨ (¬ p 3570) ∨ (¬ p 4111) ∨ (¬ p 4235) :=
  ElevenRUP.step42676 (p 1977) (p 2027) (p 2589) (p 2633) (p 2662) (p 3570) (p 4111) (p 4235) (h 2137) (derived40810 p h) (derived40879 p h) (h 12757)

theorem derived42677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (¬ p 2891) :=
  ElevenRUP.step42677 (p 1982) (p 2027) (p 2210) (p 2459) (p 2699) (p 2881) (p 2891) (h 2142) (derived40810 p h) (derived40881 p h) (h 12758)

theorem derived42678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 4117) :=
  ElevenRUP.step42678 (p 1982) (p 2027) (p 2611) (p 2651) (p 2810) (p 3005) (p 3256) (p 4117) (h 2142) (derived40810 p h) (derived40877 p h) (h 12776)

theorem derived42679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (p 4715) :=
  ElevenRUP.step42679 (p 1990) (p 2563) (p 3008) (p 4715) (h 2150) (derived40891 p h) (h 12778)

theorem derived42681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3005) ∨ (¬ p 3172) ∨ (¬ p 4111) :=
  ElevenRUP.step42681 (p 1977) (p 2027) (p 2622) (p 2651) (p 3005) (p 3172) (p 4111) (h 2137) (derived40810 p h) (derived40878 p h) (h 12797)

theorem derived42682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3570) ∨ (¬ p 3684) ∨ (¬ p 4235) :=
  ElevenRUP.step42682 (p 1976) (p 2027) (p 2633) (p 3055) (p 3570) (p 3684) (p 4235) (h 2136) (derived40810 p h) (derived40879 p h) (h 12798)

theorem derived42683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2427) ∨ (¬ p 4244) ∨ (¬ p 4948) :=
  ElevenRUP.step42683 (p 1976) (p 2027) (p 2138) (p 2427) (p 3043) (p 4244) (p 4948) (h 2136) (derived40810 p h) (derived40893 p h) (h 12799)

theorem derived42685 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2982) ∨ (¬ p 3583) ∨ (¬ p 4110) ∨ (¬ p 4385) :=
  ElevenRUP.step42685 (p 1992) (p 2027) (p 2765) (p 2982) (p 3583) (p 4110) (p 4385) (h 2152) (derived40810 p h) (derived40883 p h) (h 12886)

theorem derived42687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2797) ∨ (¬ p 2963) ∨ (¬ p 4111) :=
  ElevenRUP.step42687 (p 1977) (p 2027) (p 2622) (p 2651) (p 2797) (p 2963) (p 4111) (h 2137) (derived40810 p h) (derived40878 p h) (h 12939)

theorem derived42688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2811) ∨ (¬ p 3568) ∨ (¬ p 4111) ∨ (¬ p 4195) :=
  ElevenRUP.step42688 (p 1977) (p 2027) (p 2651) (p 2811) (p 2997) (p 3568) (p 4111) (p 4195) (h 2137) (derived40810 p h) (derived40890 p h) (h 12991)

theorem derived42690 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2952) ∨ (¬ p 3189) ∨ (¬ p 4111) :=
  ElevenRUP.step42690 (p 1993) (p 2027) (p 2388) (p 2651) (p 2952) (p 3189) (p 4111) (h 2153) (derived40810 p h) (derived40873 p h) (h 13011)

theorem derived42692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3201) ∨ (¬ p 3684) ∨ (¬ p 4110) :=
  ElevenRUP.step42692 (p 1995) (p 2027) (p 2765) (p 2928) (p 3201) (p 3684) (p 4110) (h 2155) (derived40810 p h) (derived40883 p h) (h 13013)

theorem derived42693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3644) ∨ (¬ p 3876) ∨ (¬ p 4348) :=
  ElevenRUP.step42693 (p 1976) (p 2027) (p 2766) (p 3055) (p 3644) (p 3876) (p 4348) (h 2136) (derived40810 p h) (derived40884 p h) (h 13031)

theorem derived42694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2459) ∨ (¬ p 3692) ∨ (¬ p 3694) :=
  ElevenRUP.step42694 (p 1976) (p 2027) (p 2138) (p 2459) (p 2633) (p 3692) (p 3694) (h 2136) (derived40810 p h) (derived40879 p h) (h 13032)

theorem derived42696 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3246) ∨ (¬ p 3947) ∨ (¬ p 4110) :=
  ElevenRUP.step42696 (p 1996) (p 2027) (p 2427) (p 2765) (p 3246) (p 3947) (p 4110) (h 2156) (derived40810 p h) (derived40883 p h) (h 13052)

theorem derived42697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4235) ∨ (p 4647) :=
  ElevenRUP.step42697 (p 1997) (p 2914) (p 4235) (p 4647) (h 2157) (derived40887 p h) (h 13070)

theorem derived42698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2459) ∨ (¬ p 3093) ∨ (¬ p 3309) :=
  ElevenRUP.step42698 (p 1982) (p 2027) (p 2177) (p 2459) (p 2699) (p 3093) (p 3309) (h 2142) (derived40810 p h) (derived40881 p h) (h 13071)

theorem derived42699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2579) ∨ (¬ p 4348) :=
  ElevenRUP.step42699 (p 1998) (p 2027) (p 2470) (p 2528) (p 2579) (p 3008) (p 4348) (h 2158) (derived40810 p h) (derived40891 p h) (h 13072)

theorem derived42702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2741) ∨ (¬ p 3172) ∨ (¬ p 4111) ∨ (¬ p 4118) :=
  ElevenRUP.step42702 (p 1992) (p 2027) (p 2651) (p 2741) (p 2766) (p 3172) (p 4111) (p 4118) (h 2152) (derived40810 p h) (derived40884 p h) (h 13126)

theorem derived42703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2761) ∨ (¬ p 3319) ∨ (¬ p 3549) ∨ (¬ p 4336) ∨ (¬ p 4623) :=
  ElevenRUP.step42703 (p 1988) (p 2027) (p 2295) (p 2388) (p 2761) (p 3319) (p 3549) (p 4336) (p 4623) (h 2148) (derived40810 p h) (derived40873 p h) (h 13161)

theorem derived42704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 4347) :=
  ElevenRUP.step42704 (p 1981) (p 2027) (p 2388) (p 2952) (p 3166) (p 3256) (p 4347) (h 2141) (derived40810 p h) (derived40873 p h) (h 13213)

theorem derived42705 (p : Nat → Prop) (h : Inputs p) :
    (p 2744) ∨ (¬ p 3954) :=
  ElevenRUP.step42705 (p 1984) (p 2688) (p 2744) (p 3954) (h 2144) (derived40880 p h) (h 13215)

theorem derived42706 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2651) ∨ (¬ p 2963) ∨ (¬ p 3662) :=
  ElevenRUP.step42706 (p 1994) (p 2027) (p 2388) (p 2641) (p 2651) (p 2963) (p 3662) (h 2154) (derived40810 p h) (derived40873 p h) (h 13216)

theorem derived42707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2284) ∨ (¬ p 2396) ∨ (¬ p 2992) :=
  ElevenRUP.step42707 (p 1983) (p 2027) (p 2274) (p 2284) (p 2396) (p 2688) (p 2992) (h 2143) (derived40810 p h) (derived40880 p h) (h 13217)

theorem derived42708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2299) ∨ (¬ p 3399) ∨ (¬ p 3527) :=
  ElevenRUP.step42708 (p 1975) (p 2027) (p 2247) (p 2299) (p 2688) (p 3399) (p 3527) (h 2135) (derived40810 p h) (derived40880 p h) (h 13270)

theorem derived42709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2717) ∨ (¬ p 3399) ∨ (¬ p 3576) ∨ (¬ p 3954) :=
  ElevenRUP.step42709 (p 1975) (p 2027) (p 2114) (p 2299) (p 2717) (p 3399) (p 3576) (p 3954) (h 2135) (derived40810 p h) (derived40864 p h) (h 13271)

theorem derived42710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (¬ p 3585) ∨ (¬ p 3954) ∨ (¬ p 5214) :=
  ElevenRUP.step42710 (p 2027) (p 3379) (p 3585) (p 3954) (p 5214) (derived40810 p h) (h 13289)

theorem derived42711 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2797) ∨ (¬ p 3189) ∨ (¬ p 3877) :=
  ElevenRUP.step42711 (p 1975) (p 2027) (p 2295) (p 2688) (p 2797) (p 3189) (p 3877) (h 2135) (derived40810 p h) (derived40880 p h) (h 13307)

theorem derived42712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (p 4621) :=
  ElevenRUP.step42712 (p 1999) (p 2396) (p 2997) (p 4621) (h 2159) (derived40890 p h) (h 13308)

theorem derived42713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (p 2788) :=
  ElevenRUP.step42713 (p 1976) (p 2344) (p 2780) (p 2788) (h 2136) (derived40871 p h) (h 13309)

theorem derived42714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 3434) ∨ (¬ p 3452) ∨ (¬ p 4278) :=
  ElevenRUP.step42714 (p 1984) (p 2027) (p 2928) (p 3434) (p 3437) (p 3452) (p 4278) (h 2144) (derived40810 p h) (derived40896 p h) (h 13327)

theorem derived42716 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (¬ p 2963) ∨ (¬ p 4118) ∨ (¬ p 4360) :=
  ElevenRUP.step42716 (p 1991) (p 2027) (p 2641) (p 2766) (p 2963) (p 4118) (p 4360) (h 2151) (derived40810 p h) (derived40884 p h) (h 13329)

theorem derived42718 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 2951) ∨ (¬ p 2992) :=
  ElevenRUP.step42718 (p 1982) (p 2027) (p 2156) (p 2187) (p 2363) (p 2688) (p 2951) (p 2992) (h 2142) (derived40810 p h) (derived40880 p h) (h 13331)

theorem derived42719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4985) :=
  ElevenRUP.step42719 (p 2027) (p 2341) (p 3556) (p 3570) (p 4985) (derived40810 p h) (h 13349)

theorem derived42720 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (p 4539) :=
  ElevenRUP.step42720 (p 2000) (p 2148) (p 2589) (p 4539) (h 2160) (derived40865 p h) (h 13350)

theorem derived42721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2881) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3051) :=
  ElevenRUP.step42721 (p 1975) (p 2027) (p 2299) (p 2688) (p 2881) (p 2951) (p 2992) (p 3051) (h 2135) (derived40810 p h) (derived40880 p h) (h 13351)

theorem derived42722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 3452) ∨ (¬ p 4444) :=
  ElevenRUP.step42722 (p 1984) (p 2027) (p 2509) (p 2534) (p 2764) (p 3452) (p 4444) (h 2144) (derived40810 p h) (derived40882 p h) (h 13352)

theorem derived42723 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2951) ∨ (¬ p 2992) ∨ (¬ p 3125) ∨ (¬ p 3461) :=
  ElevenRUP.step42723 (p 1988) (p 2027) (p 2156) (p 2688) (p 2951) (p 2992) (p 3125) (p 3461) (h 2148) (derived40810 p h) (derived40880 p h) (h 13370)

theorem derived42724 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2299) ∨ (¬ p 2807) ∨ (¬ p 2963) :=
  ElevenRUP.step42724 (p 1975) (p 2027) (p 2264) (p 2287) (p 2299) (p 2807) (p 2963) (h 2135) (derived40810 p h) (derived40869 p h) (h 13371)

theorem derived42726 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2630) ∨ (¬ p 3877) ∨ (¬ p 4111) ∨ (¬ p 4437) :=
  ElevenRUP.step42726 (p 1977) (p 2027) (p 2534) (p 2630) (p 2766) (p 3877) (p 4111) (p 4437) (h 2137) (derived40810 p h) (derived40884 p h) (h 13392)

theorem derived42727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3323) ∨ (¬ p 3426) ∨ (¬ p 3570) ∨ (¬ p 3917) :=
  ElevenRUP.step42727 (p 1985) (p 2027) (p 2287) (p 2717) (p 3323) (p 3426) (p 3570) (p 3917) (h 2145) (derived40810 p h) (derived40869 p h) (h 13410)

theorem derived42728 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2299) ∨ (¬ p 2860) ∨ (¬ p 2881) ∨ (¬ p 3872) :=
  ElevenRUP.step42728 (p 1975) (p 2027) (p 2132) (p 2299) (p 2611) (p 2860) (p 2881) (p 3872) (h 2135) (derived40810 p h) (derived40877 p h) (h 13411)

theorem derived42729 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2780) ∨ (¬ p 2829) :=
  ElevenRUP.step42729 (p 2001) (p 2027) (p 2114) (p 2132) (p 2619) (p 2780) (p 2829) (h 2161) (derived40810 p h) (derived40864 p h) (h 13412)

theorem derived42730 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2860) ∨ (¬ p 3156) ∨ (¬ p 3694) :=
  ElevenRUP.step42730 (p 1975) (p 2027) (p 2274) (p 2388) (p 2860) (p 3156) (p 3694) (h 2135) (derived40810 p h) (derived40873 p h) (h 13413)

theorem derived42731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2299) ∨ (¬ p 2737) ∨ (¬ p 2797) ∨ (¬ p 4156) :=
  ElevenRUP.step42731 (p 1975) (p 2027) (p 2114) (p 2264) (p 2299) (p 2737) (p 2797) (p 4156) (h 2135) (derived40810 p h) (derived40864 p h) (h 13414)

theorem derived42732 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3172) ∨ (¬ p 3189) ∨ (¬ p 3662) :=
  ElevenRUP.step42732 (p 1994) (p 2027) (p 2388) (p 2651) (p 3172) (p 3189) (p 3662) (h 2154) (derived40810 p h) (derived40873 p h) (h 13415)

theorem derived42733 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2651) ∨ (¬ p 2952) ∨ (¬ p 3952) :=
  ElevenRUP.step42733 (p 1994) (p 2027) (p 2202) (p 2563) (p 2651) (p 2952) (p 3952) (h 2154) (derived40810 p h) (derived40867 p h) (h 13416)

theorem derived42734 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 4110) :=
  ElevenRUP.step42734 (p 1975) (p 2027) (p 2299) (p 2427) (p 2765) (p 2881) (p 4110) (h 2135) (derived40810 p h) (derived40883 p h) (h 13417)

theorem derived42735 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 2707) ∨ (¬ p 2743) ∨ (¬ p 3577) :=
  ElevenRUP.step42735 (p 1975) (p 2027) (p 2299) (p 2341) (p 2622) (p 2707) (p 2743) (p 3577) (h 2135) (derived40810 p h) (derived40878 p h) (h 13418)

theorem derived42736 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2717) ∨ (¬ p 3471) ∨ (¬ p 3570) :=
  ElevenRUP.step42736 (p 1985) (p 2027) (p 2138) (p 2717) (p 3471) (p 3474) (p 3570) (h 2145) (derived40810 p h) (derived40898 p h) (h 13419)

theorem derived42739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2992) ∨ (¬ p 3323) ∨ (¬ p 3744) ∨ (¬ p 4336) :=
  ElevenRUP.step42739 (p 1981) (p 2027) (p 2187) (p 2688) (p 2992) (p 3323) (p 3744) (p 4336) (h 2141) (derived40810 p h) (derived40880 p h) (h 13422)

theorem derived42741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 2810) ∨ (¬ p 3027) ∨ (¬ p 3414) :=
  ElevenRUP.step42741 (p 1987) (p 2027) (p 2651) (p 2688) (p 2810) (p 3027) (p 3414) (h 2147) (derived40810 p h) (derived40880 p h) (h 13441)

theorem derived42742 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2641) ∨ (¬ p 2651) ∨ (¬ p 4111) :=
  ElevenRUP.step42742 (p 1975) (p 2027) (p 2295) (p 2323) (p 2641) (p 2651) (p 4111) (h 2135) (derived40810 p h) (derived40870 p h) (h 13442)

theorem derived42743 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2563) ∨ (¬ p 2598) ∨ (¬ p 2850) :=
  ElevenRUP.step42743 (p 1975) (p 2027) (p 2274) (p 2563) (p 2598) (p 2611) (p 2850) (h 2135) (derived40810 p h) (derived40877 p h) (h 13443)

theorem derived42744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3266) :=
  ElevenRUP.step42744 (p 1988) (p 2027) (p 2363) (p 2611) (p 2774) (p 2819) (p 3266) (h 2148) (derived40810 p h) (derived40877 p h) (h 13444)

theorem derived42745 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 4444) :=
  ElevenRUP.step42745 (p 1982) (p 2027) (p 2144) (p 2156) (p 2611) (p 3125) (p 3461) (p 4444) (h 2142) (derived40810 p h) (derived40877 p h) (h 13445)

theorem derived42746 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 4256) :=
  ElevenRUP.step42746 (p 1991) (p 2027) (p 2810) (p 2952) (p 3136) (p 3498) (p 4256) (h 2151) (derived40810 p h) (derived40899 p h) (h 13446)

theorem derived42749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 2449) ∨ (¬ p 3821) :=
  ElevenRUP.step42749 (p 1975) (p 2027) (p 2299) (p 2341) (p 2355) (p 2449) (p 3821) (h 2135) (derived40810 p h) (derived40872 p h) (h 13483)

theorem derived42750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (p 2586) :=
  ElevenRUP.step42750 (p 2000) (p 2344) (p 2579) (p 2586) (h 2160) (derived40871 p h) (h 13501)

theorem derived42751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 3422) ∨ (p 5222) :=
  ElevenRUP.step42751 (p 2002) (p 2114) (p 3367) (p 3422) (p 5222) (h 2162) (derived40864 p h) (h 13502)

theorem derived42753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3572) ∨ (¬ p 3947) :=
  ElevenRUP.step42753 (p 1991) (p 2027) (p 2462) (p 2952) (p 3136) (p 3572) (p 3947) (h 2151) (derived40810 p h) (derived40875 p h) (h 13521)

theorem derived42754 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 4324) :=
  ElevenRUP.step42754 (p 1984) (p 2027) (p 2462) (p 3055) (p 3367) (p 3588) (p 3873) (p 4324) (h 2144) (derived40810 p h) (derived40875 p h) (h 13522)

theorem derived42755 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2396) ∨ (¬ p 2870) ∨ (¬ p 3758) ∨ (¬ p 4140) :=
  ElevenRUP.step42755 (p 1983) (p 2027) (p 2148) (p 2156) (p 2396) (p 2870) (p 3758) (p 4140) (h 2143) (derived40810 p h) (derived40865 p h) (h 13523)

theorem derived42756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (p 4753) :=
  ElevenRUP.step42756 (p 1994) (p 2114) (p 3367) (p 4753) (h 2154) (derived40864 p h) (h 13524)

theorem derived42759 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3989) ∨ (¬ p 4110) ∨ (¬ p 4347) :=
  ElevenRUP.step42759 (p 2000) (p 2027) (p 2589) (p 2766) (p 3989) (p 4110) (p 4347) (h 2160) (derived40810 p h) (derived40884 p h) (h 13528)

theorem derived42760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 2641) :=
  ElevenRUP.step42760 (p 1983) (p 2027) (p 2241) (p 2295) (p 2396) (p 2641) (p 2699) (h 2143) (derived40810 p h) (derived40881 p h) (h 13529)

theorem derived42762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2573) ∨ (¬ p 2850) ∨ (¬ p 3584) :=
  ElevenRUP.step42762 (p 1994) (p 2027) (p 2233) (p 2440) (p 2573) (p 2850) (p 3584) (h 2154) (derived40810 p h) (derived40868 p h) (h 13531)

theorem derived42763 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2274) ∨ (¬ p 3238) ∨ (¬ p 3540) ∨ (¬ p 3921) :=
  ElevenRUP.step42763 (p 1995) (p 2027) (p 2230) (p 2274) (p 2765) (p 3238) (p 3540) (p 3921) (h 2155) (derived40810 p h) (derived40883 p h) (h 13532)

theorem derived42765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 3201) ∨ (¬ p 3238) ∨ (¬ p 3540) ∨ (¬ p 4257) :=
  ElevenRUP.step42765 (p 1992) (p 2027) (p 2230) (p 2842) (p 3201) (p 3238) (p 3540) (p 4257) (h 2152) (derived40810 p h) (derived40885 p h) (h 13534)

theorem derived42767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2590) ∨ (¬ p 3125) ∨ (¬ p 3238) ∨ (¬ p 3989) ∨ (¬ p 4137) :=
  ElevenRUP.step42767 (p 1995) (p 2027) (p 2169) (p 2590) (p 3125) (p 3238) (p 3989) (p 4137) (h 2155) (derived40810 p h) (derived40866 p h) (h 13536)

theorem derived42770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3027) ∨ (¬ p 3662) ∨ (¬ p 4235) ∨ (¬ p 4333) :=
  ElevenRUP.step42770 (p 1997) (p 2027) (p 2323) (p 2946) (p 3027) (p 3662) (p 4235) (p 4333) (h 2157) (derived40810 p h) (derived40870 p h) (h 13540)

theorem derived42771 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2573) ∨ (¬ p 3564) ∨ (¬ p 3744) :=
  ElevenRUP.step42771 (p 1975) (p 2027) (p 2233) (p 2274) (p 2573) (p 3564) (p 3744) (h 2135) (derived40810 p h) (derived40868 p h) (h 13542)

theorem derived42773 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2608) ∨ (¬ p 2829) ∨ (¬ p 3097) :=
  ElevenRUP.step42773 (p 1990) (p 2027) (p 2122) (p 2608) (p 2699) (p 2829) (p 3097) (h 2150) (derived40810 p h) (derived40881 p h) (h 13561)

theorem derived42774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2588) ∨ (¬ p 2657) :=
  ElevenRUP.step42774 (p 2005) (p 2027) (p 2295) (p 2331) (p 2545) (p 2588) (p 2657) (h 2165) (derived40810 p h) (derived40876 p h) (h 13562)

theorem derived42775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 3146) ∨ (¬ p 3379) :=
  ElevenRUP.step42775 (p 1982) (p 2027) (p 2373) (p 2406) (p 2699) (p 3146) (p 3379) (h 2142) (derived40810 p h) (derived40881 p h) (h 13563)

theorem derived42776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2518) ∨ (¬ p 2531) ∨ (¬ p 3146) ∨ (¬ p 3238) :=
  ElevenRUP.step42776 (p 1982) (p 2027) (p 2230) (p 2233) (p 2518) (p 2531) (p 3146) (p 3238) (h 2142) (derived40810 p h) (derived40868 p h) (h 13564)

theorem derived42778 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (p 4507) :=
  ElevenRUP.step42778 (p 1981) (p 2187) (p 3578) (p 4507) (h 2141) (derived40900 p h) (h 13566)

theorem derived42779 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2459) ∨ (¬ p 3692) ∨ (¬ p 4120) :=
  ElevenRUP.step42779 (p 1978) (p 2027) (p 2177) (p 2459) (p 2997) (p 3692) (p 4120) (h 2138) (derived40810 p h) (derived40890 p h) (h 13567)

theorem derived42780 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2963) ∨ (¬ p 3324) ∨ (¬ p 3361) ∨ (¬ p 4347) :=
  ElevenRUP.step42780 (p 1992) (p 2027) (p 2743) (p 2766) (p 2963) (p 3324) (p 3361) (p 4347) (h 2152) (derived40810 p h) (derived40884 p h) (h 13568)

theorem derived42781 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2952) ∨ (¬ p 3361) ∨ (¬ p 3690) ∨ (¬ p 4320) :=
  ElevenRUP.step42781 (p 1992) (p 2027) (p 2462) (p 2743) (p 2952) (p 3361) (p 3690) (p 4320) (h 2152) (derived40810 p h) (derived40875 p h) (h 13569)

theorem derived42783 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3684) ∨ (p 4884) :=
  ElevenRUP.step42783 (p 2006) (p 2202) (p 3684) (p 4884) (h 2166) (derived40867 p h) (h 13571)

theorem derived42785 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2850) ∨ (¬ p 3584) ∨ (¬ p 4320) :=
  ElevenRUP.step42785 (p 1979) (p 2027) (p 2427) (p 2850) (p 3008) (p 3584) (p 4320) (h 2139) (derived40810 p h) (derived40891 p h) (h 13573)

theorem derived42788 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2608) ∨ (¬ p 3367) ∨ (¬ p 3641) :=
  ElevenRUP.step42788 (p 1995) (p 2027) (p 2509) (p 2608) (p 2699) (p 3367) (p 3641) (h 2155) (derived40810 p h) (derived40881 p h) (h 13576)

theorem derived42791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2657) ∨ (¬ p 2737) ∨ (¬ p 4236) ∨ (¬ p 4734) :=
  ElevenRUP.step42791 (p 2027) (p 2630) (p 2657) (p 2737) (p 4236) (p 4734) (derived40810 p h) (h 13580)

theorem derived42792 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2598) ∨ (¬ p 3585) ∨ (¬ p 3758) :=
  ElevenRUP.step42792 (p 1992) (p 2027) (p 2138) (p 2598) (p 2765) (p 3585) (p 3758) (h 2152) (derived40810 p h) (derived40883 p h) (h 13581)

theorem derived42793 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2598) ∨ (¬ p 2860) ∨ (¬ p 3582) ∨ (¬ p 3589) ∨ (¬ p 4110) :=
  ElevenRUP.step42793 (p 1985) (p 2027) (p 2427) (p 2598) (p 2699) (p 2860) (p 3582) (p 3589) (p 4110) (h 2145) (derived40810 p h) (derived40881 p h) (h 13582)

theorem derived42794 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2406) ∨ (¬ p 2563) ∨ (¬ p 3379) :=
  ElevenRUP.step42794 (p 1975) (p 2027) (p 2274) (p 2406) (p 2563) (p 2699) (p 3379) (h 2135) (derived40810 p h) (derived40881 p h) (h 13583)

theorem derived42795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2553) ∨ (¬ p 3379) ∨ (¬ p 3568) :=
  ElevenRUP.step42795 (p 1980) (p 2027) (p 2493) (p 2553) (p 2699) (p 3379) (p 3568) (h 2140) (derived40810 p h) (derived40881 p h) (h 13584)

end ElevenLogic
