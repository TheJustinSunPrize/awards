import SunPrize.Certificate.Derived011
import SunPrize.Certificate.Logic012
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived50887 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3073) ∨ (¬ p 3365) ∨ (¬ p 3449) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4736) :=
  ElevenRUP.step50887 (p 2027) (p 3073) (p 3365) (p 3449) (p 3553) (p 3572) (p 4133) (p 4347) (p 4736) (derived40810 p h) (h 23865)

theorem derived50891 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 3659) ∨ (¬ p 4366) ∨ (¬ p 4376) ∨ (¬ p 4424) ∨ (¬ p 4668) :=
  ElevenRUP.step50891 (p 2027) (p 2396) (p 2553) (p 2573) (p 2608) (p 3519) (p 3659) (p 4366) (p 4376) (p 4424) (p 4668) (derived40810 p h) (h 23869)

theorem derived50894 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 3585) ∨ (¬ p 4236) :=
  ElevenRUP.step50894 (p 1992) (p 2027) (p 2598) (p 2622) (p 2952) (p 3136) (p 3585) (p 4236) (h 2152) (derived40810 p h) (derived40878 p h) (h 23873)

theorem derived50895 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3568) ∨ (¬ p 3755) ∨ (¬ p 4195) ∨ (¬ p 4367) ∨ (¬ p 4624) :=
  ElevenRUP.step50895 (p 2027) (p 3568) (p 3755) (p 4195) (p 4367) (p 4624) (derived40810 p h) (h 23874)

theorem derived50896 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2608) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3860) ∨ (¬ p 4353) ∨ (¬ p 4376) ∨ (¬ p 5118) ∨ (¬ p 5612) :=
  ElevenRUP.step50896 (p 2027) (p 2459) (p 2608) (p 2911) (p 3389) (p 3519) (p 3860) (p 4353) (p 4376) (p 5118) (p 5612) (derived40810 p h) (h 23875)

theorem derived50901 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2241) ∨ (¬ p 3553) ∨ (¬ p 3591) ∨ (¬ p 4067) ∨ (¬ p 4319) :=
  ElevenRUP.step50901 (p 1977) (p 2027) (p 2177) (p 2241) (p 2997) (p 3553) (p 3591) (p 4067) (p 4319) (h 2137) (derived40810 p h) (derived40890 p h) (h 23880)

theorem derived50902 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3324) ∨ (¬ p 3325) ∨ (¬ p 3599) ∨ (¬ p 3688) ∨ (¬ p 4337) ∨ (¬ p 4624) ∨ (¬ p 5269) :=
  ElevenRUP.step50902 (p 2027) (p 3324) (p 3325) (p 3599) (p 3688) (p 4337) (p 4624) (p 5269) (derived40810 p h) (h 23881)

theorem derived50906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 4668) ∨ (¬ p 5190) :=
  ElevenRUP.step50906 (p 2027) (p 2247) (p 2396) (p 2553) (p 2573) (p 2996) (p 3553) (p 4668) (p 5190) (derived40810 p h) (h 23888)

theorem derived50907 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2911) ∨ (¬ p 3389) ∨ (¬ p 3519) ∨ (¬ p 3860) ∨ (¬ p 3941) ∨ (¬ p 4261) ∨ (¬ p 4376) ∨ (¬ p 5122) :=
  ElevenRUP.step50907 (p 2027) (p 2608) (p 2911) (p 3389) (p 3519) (p 3860) (p 3941) (p 4261) (p 4376) (p 5122) (derived40810 p h) (h 23889)

theorem derived50908 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2563) ∨ (¬ p 2778) ∨ (¬ p 3051) ∨ (¬ p 4019) ∨ (¬ p 4118) ∨ (¬ p 4235) ∨ (¬ p 4399) ∨ (¬ p 4419) ∨ (¬ p 4963) ∨ (¬ p 5580) :=
  ElevenRUP.step50908 (p 1990) (p 2027) (p 2387) (p 2563) (p 2766) (p 2778) (p 3051) (p 4019) (p 4118) (p 4235) (p 4399) (p 4419) (p 4963) (p 5580) (h 2150) (derived40810 p h) (derived40884 p h) (h 23890)

theorem derived50910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 3051) ∨ (¬ p 3365) ∨ (¬ p 3877) ∨ (¬ p 3941) ∨ (¬ p 4042) ∨ (¬ p 4118) ∨ (¬ p 4235) ∨ (¬ p 4399) ∨ (¬ p 4419) :=
  ElevenRUP.step50910 (p 2020) (p 2027) (p 2373) (p 2766) (p 3051) (p 3365) (p 3877) (p 3941) (p 4042) (p 4118) (p 4235) (p 4399) (p 4419) (h 2180) (derived40810 p h) (derived40884 p h) (h 23892)

theorem derived50911 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3051) ∨ (¬ p 3346) ∨ (¬ p 4235) ∨ (¬ p 4399) ∨ (¬ p 4949) :=
  ElevenRUP.step50911 (p 2027) (p 3051) (p 3346) (p 4235) (p 4399) (p 4949) (derived40810 p h) (h 23893)

theorem derived50915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3266) ∨ (¬ p 3292) ∨ (¬ p 3950) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 5284) :=
  ElevenRUP.step50915 (p 2027) (p 2396) (p 2553) (p 2573) (p 3266) (p 3292) (p 3950) (p 4236) (p 4419) (p 5284) (derived40810 p h) (h 23897)

theorem derived50916 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2518) ∨ (¬ p 2528) ∨ (¬ p 2608) ∨ (¬ p 3555) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4376) :=
  ElevenRUP.step50916 (p 2027) (p 2191) (p 2518) (p 2528) (p 2608) (p 3555) (p 4134) (p 4347) (p 4376) (derived40810 p h) (h 23898)

theorem derived50918 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3051) ∨ (¬ p 4120) ∨ (¬ p 4235) ∨ (¬ p 4507) :=
  ElevenRUP.step50918 (p 2027) (p 2563) (p 3051) (p 4120) (p 4235) (p 4507) (derived40810 p h) (h 23900)

theorem derived50919 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 3032) ∨ (¬ p 3201) ∨ (¬ p 3553) ∨ (¬ p 4366) ∨ (¬ p 4668) :=
  ElevenRUP.step50919 (p 2027) (p 2241) (p 2417) (p 2598) (p 2750) (p 2753) (p 3032) (p 3201) (p 3553) (p 4366) (p 4668) (derived40810 p h) (h 23901)

theorem derived50920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2245) ∨ (¬ p 2870) ∨ (¬ p 3027) ∨ (¬ p 3414) ∨ (¬ p 3662) ∨ (¬ p 4235) ∨ (¬ p 4705) ∨ (¬ p 4733) :=
  ElevenRUP.step50920 (p 2027) (p 2132) (p 2245) (p 2870) (p 3027) (p 3414) (p 3662) (p 4235) (p 4705) (p 4733) (derived40810 p h) (h 23902)

theorem derived50921 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2563) ∨ (¬ p 3051) ∨ (¬ p 4235) ∨ (¬ p 4399) :=
  ElevenRUP.step50921 (p 1990) (p 2027) (p 2476) (p 2563) (p 3051) (p 3498) (p 4235) (p 4399) (h 2150) (derived40810 p h) (derived40899 p h) (h 23903)

theorem derived50922 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 3055) ∨ (¬ p 3758) ∨ (¬ p 4392) ∨ (¬ p 4749) :=
  ElevenRUP.step50922 (p 2027) (p 2144) (p 2156) (p 3055) (p 3758) (p 4392) (p 4749) (derived40810 p h) (h 23904)

theorem derived50924 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2901) ∨ (¬ p 3497) ∨ (¬ p 4235) ∨ (¬ p 4507) :=
  ElevenRUP.step50924 (p 2027) (p 2563) (p 2901) (p 3497) (p 4235) (p 4507) (derived40810 p h) (h 23907)

theorem derived50925 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2598) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2963) ∨ (¬ p 3201) ∨ (¬ p 3324) ∨ (¬ p 3868) ∨ (¬ p 5560) ∨ (¬ p 5580) :=
  ElevenRUP.step50925 (p 2027) (p 2252) (p 2598) (p 2750) (p 2753) (p 2963) (p 3201) (p 3324) (p 3868) (p 5560) (p 5580) (derived40810 p h) (h 23908)

theorem derived50930 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 4042) ∨ (¬ p 4235) ∨ (¬ p 5559) ∨ (¬ p 5660) :=
  ElevenRUP.step50930 (p 2027) (p 2373) (p 4042) (p 4235) (p 5559) (p 5660) (derived40810 p h) (h 23913)

theorem derived50931 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2922) ∨ (¬ p 2963) ∨ (¬ p 3379) ∨ (¬ p 3868) ∨ (¬ p 4037) ∨ (¬ p 4191) ∨ (¬ p 4826) :=
  ElevenRUP.step50931 (p 2027) (p 2254) (p 2922) (p 2963) (p 3379) (p 3868) (p 4037) (p 4191) (p 4826) (derived40810 p h) (h 23914)

theorem derived50932 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 2982) ∨ (¬ p 3051) ∨ (¬ p 4135) ∨ (¬ p 4235) ∨ (¬ p 4399) :=
  ElevenRUP.step50932 (p 1988) (p 2027) (p 2233) (p 2761) (p 2982) (p 3051) (p 4135) (p 4235) (p 4399) (h 2148) (derived40810 p h) (derived40868 p h) (h 23915)

theorem derived50935 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2963) ∨ (¬ p 2982) ∨ (¬ p 3051) ∨ (¬ p 3324) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 4235) ∨ (¬ p 4236) ∨ (¬ p 4347) ∨ (¬ p 4376) ∨ (¬ p 4399) ∨ (¬ p 4450) :=
  ElevenRUP.step50935 (p 2027) (p 2963) (p 2982) (p 3051) (p 3324) (p 3366) (p 3519) (p 4235) (p 4236) (p 4347) (p 4376) (p 4399) (p 4450) (derived40810 p h) (h 23920)

theorem derived50936 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3093) ∨ (¬ p 3201) ∨ (¬ p 4366) ∨ (¬ p 4442) ∨ (¬ p 4870) ∨ (¬ p 5559) :=
  ElevenRUP.step50936 (p 2027) (p 2598) (p 2753) (p 2911) (p 3093) (p 3201) (p 4366) (p 4442) (p 4870) (p 5559) (derived40810 p h) (h 23921)

theorem derived50937 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3222) ∨ (¬ p 3276) ∨ (¬ p 3379) ∨ (¬ p 4358) ∨ (¬ p 4736) ∨ (¬ p 5123) ∨ (¬ p 5580) :=
  ElevenRUP.step50937 (p 2027) (p 2780) (p 3222) (p 3276) (p 3379) (p 4358) (p 4736) (p 5123) (p 5580) (derived40810 p h) (h 23922)

theorem derived50940 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2696) ∨ (¬ p 2911) ∨ (p 3366) ∨ (¬ p 3389) ∨ (¬ p 3759) ∨ (¬ p 4242) ∨ (¬ p 4749) ∨ (¬ p 5118) ∨ (¬ p 5612) :=
  ElevenRUP.step50940 (p 2027) (p 2459) (p 2696) (p 2911) (p 3366) (p 3389) (p 3759) (p 4242) (p 4749) (p 5118) (p 5612) (derived40810 p h) (h 23925)

theorem derived50941 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2459) ∨ (¬ p 2911) ∨ (¬ p 3051) ∨ (¬ p 3366) ∨ (¬ p 3954) ∨ (¬ p 4001) ∨ (¬ p 4521) ∨ (¬ p 5118) ∨ (¬ p 5612) :=
  ElevenRUP.step50941 (p 2027) (p 2104) (p 2459) (p 2911) (p 3051) (p 3366) (p 3954) (p 4001) (p 4521) (p 5118) (p 5612) (derived40810 p h) (h 23926)

theorem derived50942 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2743) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3361) ∨ (¬ p 3414) ∨ (¬ p 3947) ∨ (¬ p 4418) ∨ (¬ p 4666) ∨ (¬ p 4737) :=
  ElevenRUP.step50942 (p 2027) (p 2132) (p 2743) (p 2881) (p 2891) (p 3361) (p 3414) (p 3947) (p 4418) (p 4666) (p 4737) (derived40810 p h) (h 23928)

theorem derived50943 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2295) ∨ (¬ p 3556) ∨ (¬ p 4275) ∨ (¬ p 4560) :=
  ElevenRUP.step50943 (p 2027) (p 2156) (p 2295) (p 3556) (p 4275) (p 4560) (derived40810 p h) (h 23929)

theorem derived50944 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3483) ∨ (¬ p 3659) ∨ (¬ p 3689) ∨ (¬ p 4624) :=
  ElevenRUP.step50944 (p 2027) (p 2177) (p 3483) (p 3659) (p 3689) (p 4624) (derived40810 p h) (h 23930)

theorem derived50945 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 2963) ∨ (¬ p 4037) ∨ (¬ p 4149) ∨ (¬ p 4191) ∨ (¬ p 4787) ∨ (¬ p 5119) :=
  ElevenRUP.step50945 (p 2027) (p 2470) (p 2630) (p 2656) (p 2963) (p 4037) (p 4149) (p 4191) (p 4787) (p 5119) (derived40810 p h) (h 23931)

theorem derived50946 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 2963) ∨ (¬ p 3659) ∨ (¬ p 3689) ∨ (¬ p 4328) ∨ (¬ p 4787) ∨ (¬ p 5118) ∨ (¬ p 5558) :=
  ElevenRUP.step50946 (p 2027) (p 2470) (p 2528) (p 2630) (p 2656) (p 2963) (p 3659) (p 3689) (p 4328) (p 4787) (p 5118) (p 5558) (derived40810 p h) (h 23932)

theorem derived50947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2891) ∨ (¬ p 3957) ∨ (¬ p 4235) ∨ (¬ p 4512) ∨ (¬ p 4539) :=
  ElevenRUP.step50947 (p 2027) (p 2156) (p 2891) (p 3957) (p 4235) (p 4512) (p 4539) (derived40810 p h) (h 23935)

theorem derived50948 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2146) ∨ (¬ p 2220) ∨ (¬ p 2839) ∨ (¬ p 4242) ∨ (¬ p 4740) :=
  ElevenRUP.step50948 (p 2027) (p 2146) (p 2220) (p 2839) (p 4242) (p 4740) (derived40810 p h) (h 23936)

theorem derived50954 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 3276) ∨ (¬ p 3355) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 4787) ∨ (¬ p 5123) ∨ (¬ p 5558) :=
  ElevenRUP.step50954 (p 2027) (p 2630) (p 2656) (p 3276) (p 3355) (p 3414) (p 3553) (p 4787) (p 5123) (p 5558) (derived40810 p h) (h 23943)

theorem derived50955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4668) ∨ (¬ p 4733) :=
  ElevenRUP.step50955 (p 2027) (p 2299) (p 2417) (p 2598) (p 3201) (p 3549) (p 3591) (p 4668) (p 4733) (derived40810 p h) (h 23944)

theorem derived50956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2553) ∨ (¬ p 2598) ∨ (¬ p 3324) ∨ (¬ p 3422) ∨ (¬ p 4154) ∨ (¬ p 4501) ∨ (¬ p 4733) :=
  ElevenRUP.step50956 (p 2027) (p 2247) (p 2553) (p 2598) (p 3324) (p 3422) (p 4154) (p 4501) (p 4733) (derived40810 p h) (h 23945)

theorem derived50957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2528) ∨ (¬ p 3266) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4391) ∨ (¬ p 4777) ∨ (¬ p 4831) ∨ (¬ p 5190) :=
  ElevenRUP.step50957 (p 2027) (p 2470) (p 2528) (p 3266) (p 3588) (p 3954) (p 4391) (p 4777) (p 4831) (p 5190) (derived40810 p h) (h 23946)

theorem derived50966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2810) ∨ (¬ p 2870) ∨ (¬ p 2952) ∨ (¬ p 4313) ∨ (¬ p 4320) :=
  ElevenRUP.step50966 (p 1991) (p 2027) (p 2545) (p 2810) (p 2870) (p 2952) (p 4313) (p 4320) (h 2151) (derived40810 p h) (derived40876 p h) (h 23955)

theorem derived50968 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3654) ∨ (¬ p 3743) ∨ (¬ p 4026) ∨ (¬ p 4512) ∨ (¬ p 4558) :=
  ElevenRUP.step50968 (p 2027) (p 2891) (p 3654) (p 3743) (p 4026) (p 4512) (p 4558) (derived40810 p h) (h 23957)

theorem derived50969 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2542) ∨ (¬ p 3054) ∨ (¬ p 4244) ∨ (¬ p 4750) :=
  ElevenRUP.step50969 (p 2027) (p 2427) (p 2542) (p 3054) (p 4244) (p 4750) (derived40810 p h) (h 23958)

theorem derived50970 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2743) ∨ (¬ p 2774) ∨ (¬ p 2952) ∨ (¬ p 3063) ∨ (¬ p 3361) ∨ (¬ p 3918) ∨ (¬ p 4208) ∨ (¬ p 4737) ∨ (¬ p 5059) :=
  ElevenRUP.step50970 (p 2027) (p 2363) (p 2743) (p 2774) (p 2952) (p 3063) (p 3361) (p 3918) (p 4208) (p 4737) (p 5059) (derived40810 p h) (h 23959)

theorem derived50973 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2741) ∨ (¬ p 2928) ∨ (¬ p 3201) ∨ (¬ p 3402) ∨ (¬ p 4737) :=
  ElevenRUP.step50973 (p 2027) (p 2598) (p 2741) (p 2928) (p 3201) (p 3402) (p 4737) (derived40810 p h) (h 23962)

theorem derived50975 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2383) ∨ (¬ p 2962) ∨ (¬ p 3688) ∨ (¬ p 4358) ∨ (¬ p 4737) :=
  ElevenRUP.step50975 (p 2027) (p 2144) (p 2383) (p 2962) (p 3688) (p 4358) (p 4737) (derived40810 p h) (h 23964)

theorem derived50976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2860) ∨ (¬ p 3125) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 4330) ∨ (¬ p 4425) ∨ (¬ p 4729) :=
  ElevenRUP.step50976 (p 2027) (p 2132) (p 2860) (p 3125) (p 3266) (p 3346) (p 4330) (p 4425) (p 4729) (derived40810 p h) (h 23965)

theorem derived50977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2860) ∨ (¬ p 3696) ∨ (¬ p 4340) ∨ (¬ p 4359) ∨ (¬ p 4507) :=
  ElevenRUP.step50977 (p 2027) (p 2088) (p 2860) (p 3696) (p 4340) (p 4359) (p 4507) (derived40810 p h) (h 23966)

theorem derived50978 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2383) ∨ (¬ p 3097) ∨ (¬ p 4358) ∨ (¬ p 4489) :=
  ElevenRUP.step50978 (p 2027) (p 2122) (p 2383) (p 3097) (p 4358) (p 4489) (derived40810 p h) (h 23967)

theorem derived50979 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 2619) ∨ (¬ p 2657) ∨ (¬ p 3644) ∨ (¬ p 3742) ∨ (¬ p 3758) ∨ (¬ p 4789) ∨ (¬ p 4902) :=
  ElevenRUP.step50979 (p 2027) (p 2144) (p 2156) (p 2619) (p 2657) (p 3644) (p 3742) (p 3758) (p 4789) (p 4902) (derived40810 p h) (h 23968)

theorem derived50980 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) ∨ (¬ p 3989) ∨ (¬ p 4341) ∨ (¬ p 4347) ∨ (¬ p 4560) :=
  ElevenRUP.step50980 (p 2027) (p 3256) (p 3989) (p 4341) (p 4347) (p 4560) (derived40810 p h) (h 23970)

theorem derived50981 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2144) ∨ (¬ p 2156) ∨ (¬ p 2190) ∨ (¬ p 2437) ∨ (¬ p 3146) ∨ (¬ p 3540) ∨ (¬ p 4133) ∨ (¬ p 4256) ∨ (¬ p 4347) ∨ (¬ p 4383) ∨ (¬ p 4729) :=
  ElevenRUP.step50981 (p 2027) (p 2144) (p 2156) (p 2190) (p 2437) (p 3146) (p 3540) (p 4133) (p 4256) (p 4347) (p 4383) (p 4729) (derived40810 p h) (h 23972)

theorem derived50982 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3555) ∨ (¬ p 3609) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4861) :=
  ElevenRUP.step50982 (p 2027) (p 2191) (p 2241) (p 2750) (p 2753) (p 2774) (p 3555) (p 3609) (p 4134) (p 4347) (p 4861) (derived40810 p h) (h 23973)

theorem derived50983 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 3371) ∨ (¬ p 3379) ∨ (¬ p 3556) ∨ (¬ p 5216) :=
  ElevenRUP.step50983 (p 2027) (p 2891) (p 3369) (p 3371) (p 3379) (p 3556) (p 5216) (derived40810 p h) (h 23974)

theorem derived50985 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3555) ∨ (¬ p 3830) ∨ (¬ p 4173) ∨ (¬ p 4387) ∨ (¬ p 5046) :=
  ElevenRUP.step50985 (p 2027) (p 3555) (p 3830) (p 4173) (p 4387) (p 5046) (derived40810 p h) (h 23976)

theorem derived50989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2542) ∨ (¬ p 2829) ∨ (¬ p 3238) ∨ (¬ p 4256) ∨ (¬ p 4438) ∨ (¬ p 5216) :=
  ElevenRUP.step50989 (p 2027) (p 2122) (p 2177) (p 2542) (p 2829) (p 3238) (p 4256) (p 4438) (p 5216) (derived40810 p h) (h 23980)

theorem derived50990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2982) ∨ (¬ p 3096) ∨ (¬ p 3574) ∨ (¬ p 5046) :=
  ElevenRUP.step50990 (p 2027) (p 2542) (p 2982) (p 3096) (p 3574) (p 5046) (derived40810 p h) (h 23981)

theorem derived50991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2881) ∨ (¬ p 4138) ∨ (¬ p 4358) ∨ (¬ p 4559) :=
  ElevenRUP.step50991 (p 2027) (p 2122) (p 2881) (p 4138) (p 4358) (p 4559) (derived40810 p h) (h 23982)

theorem derived50992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3347) ∨ (¬ p 3954) ∨ (¬ p 3989) ∨ (¬ p 4110) ∨ (¬ p 4501) ∨ (¬ p 5216) :=
  ElevenRUP.step50992 (p 2027) (p 2589) (p 3093) (p 3309) (p 3347) (p 3954) (p 3989) (p 4110) (p 4501) (p 5216) (derived40810 p h) (h 23983)

theorem derived50993 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2542) ∨ (¬ p 2589) ∨ (¬ p 2717) ∨ (¬ p 3359) ∨ (¬ p 3471) ∨ (¬ p 4697) ∨ (¬ p 4729) :=
  ElevenRUP.step50993 (p 2027) (p 2459) (p 2542) (p 2589) (p 2717) (p 3359) (p 3471) (p 4697) (p 4729) (derived40810 p h) (h 23984)

theorem derived50994 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 4345) ∨ (¬ p 4358) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step50994 (p 2027) (p 3483) (p 4345) (p 4358) (p 5118) (p 5580) (derived40810 p h) (h 23985)

theorem derived50995 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2578) ∨ (¬ p 2870) ∨ (¬ p 3096) ∨ (¬ p 4114) ∨ (¬ p 4261) ∨ (¬ p 4359) ∨ (¬ p 4558) ∨ (¬ p 5315) :=
  ElevenRUP.step50995 (p 2027) (p 2088) (p 2578) (p 2870) (p 3096) (p 4114) (p 4261) (p 4359) (p 4558) (p 5315) (derived40810 p h) (h 23987)

theorem derived50996 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3461) ∨ (¬ p 3483) ∨ (¬ p 3742) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step50996 (p 2027) (p 2252) (p 2657) (p 2750) (p 2753) (p 2774) (p 3461) (p 3483) (p 3742) (p 4831) (p 5503) (derived40810 p h) (h 23988)

theorem derived50999 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2963) ∨ (¬ p 3361) ∨ (¬ p 3471) ∨ (¬ p 3527) ∨ (¬ p 3568) ∨ (¬ p 3570) ∨ (¬ p 4424) ∨ (¬ p 4556) ∨ (¬ p 4737) :=
  ElevenRUP.step50999 (p 2027) (p 2743) (p 2963) (p 3361) (p 3471) (p 3527) (p 3568) (p 3570) (p 4424) (p 4556) (p 4737) (derived40810 p h) (h 23991)

theorem derived51003 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3019) ∨ (¬ p 3584) ∨ (¬ p 3956) ∨ (¬ p 4750) :=
  ElevenRUP.step51003 (p 2027) (p 2668) (p 3019) (p 3584) (p 3956) (p 4750) (derived40810 p h) (h 23996)

theorem derived51005 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 3584) ∨ (¬ p 3585) ∨ (¬ p 3695) ∨ (¬ p 4715) :=
  ElevenRUP.step51005 (p 2027) (p 2839) (p 3584) (p 3585) (p 3695) (p 4715) (derived40810 p h) (h 23998)

theorem derived51006 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2780) ∨ (¬ p 2870) ∨ (¬ p 4428) ∨ (¬ p 4558) :=
  ElevenRUP.step51006 (p 2027) (p 2132) (p 2780) (p 2870) (p 4428) (p 4558) (derived40810 p h) (h 23999)

theorem derived51008 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2383) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2786) ∨ (¬ p 3266) ∨ (¬ p 3609) ∨ (¬ p 3742) ∨ (¬ p 4831) ∨ (¬ p 4857) ∨ (¬ p 5503) :=
  ElevenRUP.step51008 (p 2027) (p 2252) (p 2383) (p 2657) (p 2750) (p 2753) (p 2786) (p 3266) (p 3609) (p 3742) (p 4831) (p 4857) (p 5503) (derived40810 p h) (h 24001)

theorem derived51009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2363) ∨ (¬ p 2657) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 4256) ∨ (¬ p 4286) ∨ (¬ p 5118) :=
  ElevenRUP.step51009 (p 2027) (p 2252) (p 2363) (p 2657) (p 2750) (p 2753) (p 2774) (p 2819) (p 4256) (p 4286) (p 5118) (derived40810 p h) (h 24002)

theorem derived51010 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2146) ∨ (¬ p 2383) ∨ (¬ p 2962) ∨ (¬ p 3758) ∨ (¬ p 3989) :=
  ElevenRUP.step51010 (p 2027) (p 2146) (p 2383) (p 2962) (p 3758) (p 3989) (derived40810 p h) (h 24003)

theorem derived51015 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2870) ∨ (¬ p 2911) ∨ (¬ p 3548) ∨ (¬ p 3758) ∨ (¬ p 4366) ∨ (¬ p 4521) ∨ (¬ p 4647) :=
  ElevenRUP.step51015 (p 2027) (p 2156) (p 2870) (p 2911) (p 3548) (p 3758) (p 4366) (p 4521) (p 4647) (derived40810 p h) (h 24008)

theorem derived51021 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3555) ∨ (¬ p 3830) ∨ (¬ p 4385) ∨ (¬ p 4387) ∨ (¬ p 4878) :=
  ElevenRUP.step51021 (p 2027) (p 3555) (p 3830) (p 4385) (p 4387) (p 4878) (derived40810 p h) (h 24016)

theorem derived51022 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2396) ∨ (¬ p 2911) ∨ (¬ p 3690) ∨ (¬ p 4647) :=
  ElevenRUP.step51022 (p 2027) (p 2299) (p 2396) (p 2911) (p 3690) (p 4647) (derived40810 p h) (h 24017)

theorem derived51025 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2254) ∨ (¬ p 2608) ∨ (¬ p 2829) ∨ (¬ p 2952) ∨ (¬ p 3952) ∨ (¬ p 3989) ∨ (¬ p 4501) :=
  ElevenRUP.step51025 (p 2027) (p 2122) (p 2254) (p 2608) (p 2829) (p 2952) (p 3952) (p 3989) (p 4501) (derived40810 p h) (h 24020)

theorem derived51026 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3389) ∨ (¬ p 3486) ∨ (¬ p 3569) ∨ (¬ p 4243) ∨ (¬ p 4882) :=
  ElevenRUP.step51026 (p 2027) (p 2589) (p 3389) (p 3486) (p 3569) (p 4243) (p 4882) (derived40810 p h) (h 24021)

theorem derived51028 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2252) ∨ (¬ p 2299) ∨ (¬ p 2619) ∨ (¬ p 2750) ∨ (¬ p 2963) ∨ (¬ p 3568) ∨ (¬ p 3954) ∨ (¬ p 4243) ∨ (¬ p 4902) :=
  ElevenRUP.step51028 (p 2027) (p 2210) (p 2252) (p 2299) (p 2619) (p 2750) (p 2963) (p 3568) (p 3954) (p 4243) (p 4902) (derived40810 p h) (h 24023)

theorem derived51029 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2427) ∨ (¬ p 3556) ∨ (¬ p 3758) ∨ (¬ p 4882) :=
  ElevenRUP.step51029 (p 2027) (p 2156) (p 2427) (p 3556) (p 3758) (p 4882) (derived40810 p h) (h 24024)

theorem derived51030 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 3083) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3742) ∨ (¬ p 4107) ∨ (¬ p 4712) ∨ (¬ p 5193) :=
  ElevenRUP.step51030 (p 2027) (p 2476) (p 3083) (p 3399) (p 3631) (p 3742) (p 4107) (p 4712) (p 5193) (derived40810 p h) (h 24025)

theorem derived51031 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 2870) ∨ (¬ p 3688) ∨ (¬ p 4428) ∨ (¬ p 4558) :=
  ElevenRUP.step51031 (p 2027) (p 2839) (p 2870) (p 3688) (p 4428) (p 4558) (derived40810 p h) (h 24026)

theorem derived51033 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2995) ∨ (¬ p 3690) ∨ (¬ p 3952) ∨ (¬ p 4558) :=
  ElevenRUP.step51033 (p 2027) (p 2449) (p 2995) (p 3690) (p 3952) (p 4558) (derived40810 p h) (h 24028)

theorem derived51034 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 3570) ∨ (¬ p 3741) ∨ (¬ p 4110) ∨ (¬ p 4558) :=
  ElevenRUP.step51034 (p 2027) (p 2911) (p 3570) (p 3741) (p 4110) (p 4558) (derived40810 p h) (h 24029)

theorem derived51036 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2952) ∨ (¬ p 3222) ∨ (¬ p 3276) ∨ (¬ p 3379) ∨ (¬ p 4320) ∨ (¬ p 4831) ∨ (¬ p 5660) :=
  ElevenRUP.step51036 (p 2027) (p 2254) (p 2952) (p 3222) (p 3276) (p 3379) (p 4320) (p 4831) (p 5660) (derived40810 p h) (h 24031)

theorem derived51037 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2493) ∨ (¬ p 2553) ∨ (¬ p 2952) ∨ (¬ p 3379) ∨ (¬ p 3952) ∨ (¬ p 3989) ∨ (¬ p 4501) :=
  ElevenRUP.step51037 (p 2027) (p 2254) (p 2493) (p 2553) (p 2952) (p 3379) (p 3952) (p 3989) (p 4501) (derived40810 p h) (h 24036)

theorem derived51039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3136) ∨ (¬ p 3745) ∨ (¬ p 4195) ∨ (¬ p 4241) ∨ (¬ p 4558) :=
  ElevenRUP.step51039 (p 2027) (p 2427) (p 3136) (p 3745) (p 4195) (p 4241) (p 4558) (derived40810 p h) (h 24038)

theorem derived51040 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2797) ∨ (¬ p 3983) ∨ (¬ p 4787) :=
  ElevenRUP.step51040 (p 2027) (p 2295) (p 2313) (p 2797) (p 3983) (p 4787) (derived40810 p h) (h 24039)

theorem derived51042 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2493) ∨ (¬ p 3365) ∨ (¬ p 3379) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4133) ∨ (¬ p 4736) :=
  ElevenRUP.step51042 (p 2027) (p 2352) (p 2493) (p 3365) (p 3379) (p 3553) (p 3572) (p 4133) (p 4736) (derived40810 p h) (h 24041)

theorem derived51043 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 4608) :=
  ElevenRUP.step51043 (p 1985) (p 2427) (p 3498) (p 4608) (h 2145) (derived40899 p h) (h 24042)

theorem derived51044 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2499) ∨ (¬ p 2573) ∨ (¬ p 2922) ∨ (¬ p 4079) ∨ (¬ p 4710) :=
  ElevenRUP.step51044 (p 1998) (p 2027) (p 2177) (p 2499) (p 2573) (p 2699) (p 2922) (p 4079) (p 4710) (h 2158) (derived40810 p h) (derived40881 p h) (h 24043)

theorem derived51045 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 2630) ∨ (¬ p 2656) ∨ (¬ p 2952) ∨ (¬ p 3692) ∨ (¬ p 3694) ∨ (¬ p 3979) ∨ (¬ p 4157) ∨ (¬ p 4787) ∨ (¬ p 5051) ∨ (¬ p 5122) :=
  ElevenRUP.step51045 (p 2027) (p 2470) (p 2630) (p 2656) (p 2952) (p 3692) (p 3694) (p 3979) (p 4157) (p 4787) (p 5051) (p 5122) (derived40810 p h) (h 24044)

theorem derived51047 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3422) ∨ (¬ p 3475) ∨ (¬ p 3574) ∨ (¬ p 4787) :=
  ElevenRUP.step51047 (p 2027) (p 2657) (p 3422) (p 3475) (p 3574) (p 4787) (derived40810 p h) (h 24046)

theorem derived51051 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2748) ∨ (¬ p 2963) ∨ (¬ p 3055) ∨ (¬ p 3324) ∨ (¬ p 3366) ∨ (¬ p 3537) ∨ (¬ p 3609) ∨ (¬ p 4749) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step51051 (p 2027) (p 2252) (p 2748) (p 2963) (p 3055) (p 3324) (p 3366) (p 3537) (p 3609) (p 4749) (p 5118) (p 5580) (derived40810 p h) (h 24050)

theorem derived51053 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2264) ∨ (¬ p 2493) ∨ (¬ p 3379) ∨ (¬ p 3551) ∨ (¬ p 3564) ∨ (¬ p 3947) ∨ (¬ p 4621) ∨ (¬ p 4849) :=
  ElevenRUP.step51053 (p 2027) (p 2254) (p 2264) (p 2493) (p 3379) (p 3551) (p 3564) (p 3947) (p 4621) (p 4849) (derived40810 p h) (h 24052)

theorem derived51056 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2819) ∨ (¬ p 3569) ∨ (¬ p 3644) ∨ (¬ p 3822) ∨ (¬ p 4170) ∨ (¬ p 4403) ∨ (¬ p 4556) :=
  ElevenRUP.step51056 (p 2027) (p 2819) (p 3569) (p 3644) (p 3822) (p 4170) (p 4403) (p 4556) (derived40810 p h) (h 24055)

theorem derived51057 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2952) ∨ (¬ p 3475) ∨ (¬ p 3582) ∨ (¬ p 4320) ∨ (¬ p 4787) :=
  ElevenRUP.step51057 (p 2027) (p 2870) (p 2952) (p 3475) (p 3582) (p 4320) (p 4787) (derived40810 p h) (h 24057)

theorem derived51062 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2810) ∨ (¬ p 3365) ∨ (¬ p 4328) ∨ (¬ p 4975) :=
  ElevenRUP.step51062 (p 2027) (p 2774) (p 2810) (p 3365) (p 4328) (p 4975) (derived40810 p h) (h 24065)

theorem derived51064 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2829) ∨ (¬ p 4242) ∨ (¬ p 4843) ∨ (¬ p 4857) :=
  ElevenRUP.step51064 (p 2027) (p 2668) (p 2829) (p 4242) (p 4843) (p 4857) (derived40810 p h) (h 24067)

theorem derived51065 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2311) ∨ (¬ p 2995) ∨ (¬ p 3551) ∨ (¬ p 4208) ∨ (¬ p 4356) ∨ (¬ p 5043) :=
  ElevenRUP.step51065 (p 2027) (p 2264) (p 2311) (p 2995) (p 3551) (p 4208) (p 4356) (p 5043) (derived40810 p h) (h 24068)

theorem derived51066 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2717) ∨ (¬ p 2748) ∨ (¬ p 2963) ∨ (¬ p 3055) ∨ (¬ p 3471) ∨ (¬ p 3568) ∨ (¬ p 4107) ∨ (¬ p 4666) ∨ (¬ p 4749) :=
  ElevenRUP.step51066 (p 2027) (p 2252) (p 2717) (p 2748) (p 2963) (p 3055) (p 3471) (p 3568) (p 4107) (p 4666) (p 4749) (derived40810 p h) (h 24069)

theorem derived51068 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3237) ∨ (¬ p 3680) ∨ (¬ p 4425) ∨ (¬ p 5043) :=
  ElevenRUP.step51068 (p 2027) (p 2563) (p 3237) (p 3680) (p 4425) (p 5043) (derived40810 p h) (h 24071)

theorem derived51069 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2299) ∨ (¬ p 2373) ∨ (¬ p 2406) ∨ (¬ p 2963) ∨ (¬ p 3379) ∨ (¬ p 3568) ∨ (¬ p 4902) :=
  ElevenRUP.step51069 (p 2027) (p 2254) (p 2299) (p 2373) (p 2406) (p 2963) (p 3379) (p 3568) (p 4902) (derived40810 p h) (h 24072)

theorem derived51070 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2254) ∨ (¬ p 2406) ∨ (¬ p 2982) ∨ (¬ p 3379) ∨ (¬ p 3414) ∨ (¬ p 3553) ∨ (¬ p 4348) ∨ (¬ p 4450) :=
  ElevenRUP.step51070 (p 2027) (p 2254) (p 2406) (p 2982) (p 3379) (p 3414) (p 3553) (p 4348) (p 4450) (derived40810 p h) (h 24073)

theorem derived51071 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2619) ∨ (¬ p 3693) ∨ (¬ p 4256) ∨ (¬ p 4885) :=
  ElevenRUP.step51071 (p 2027) (p 2542) (p 2619) (p 3693) (p 4256) (p 4885) (derived40810 p h) (h 24076)

theorem derived51072 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3570) ∨ (¬ p 3631) ∨ (¬ p 4244) ∨ (¬ p 4376) ∨ (¬ p 4668) :=
  ElevenRUP.step51072 (p 2027) (p 2138) (p 3366) (p 3399) (p 3452) (p 3570) (p 3631) (p 4244) (p 4376) (p 4668) (derived40810 p h) (h 24077)

theorem derived51073 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3860) ∨ (¬ p 4501) ∨ (¬ p 4993) :=
  ElevenRUP.step51073 (p 2027) (p 3093) (p 3309) (p 3860) (p 4501) (p 4993) (derived40810 p h) (h 24078)

theorem derived51074 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 3246) ∨ (¬ p 3570) ∨ (¬ p 4420) ∨ (¬ p 4443) :=
  ElevenRUP.step51074 (p 2027) (p 2534) (p 3246) (p 3570) (p 4420) (p 4443) (derived40810 p h) (h 24079)

theorem derived51075 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2781) ∨ (¬ p 3365) ∨ (¬ p 3564) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 3956) ∨ (¬ p 4621) :=
  ElevenRUP.step51075 (p 2027) (p 2383) (p 2781) (p 3365) (p 3564) (p 3572) (p 3947) (p 3956) (p 4621) (derived40810 p h) (h 24080)

theorem derived51076 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3399) ∨ (¬ p 3452) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 3631) ∨ (¬ p 4376) ∨ (¬ p 4668) :=
  ElevenRUP.step51076 (p 2027) (p 3365) (p 3366) (p 3399) (p 3452) (p 3553) (p 3572) (p 3631) (p 4376) (p 4668) (derived40810 p h) (h 24081)

theorem derived51077 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 3877) ∨ (¬ p 4548) ∨ (¬ p 4668) :=
  ElevenRUP.step51077 (p 2027) (p 2449) (p 2685) (p 3877) (p 4548) (p 4668) (derived40810 p h) (h 24082)

theorem derived51079 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3572) ∨ (¬ p 3755) ∨ (¬ p 4107) ∨ (¬ p 4361) ∨ (¬ p 4660) :=
  ElevenRUP.step51079 (p 2027) (p 3572) (p 3755) (p 4107) (p 4361) (p 4660) (derived40810 p h) (h 24084)

theorem derived51080 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 3366) ∨ (¬ p 3519) ∨ (¬ p 3694) ∨ (¬ p 4376) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step51080 (p 2027) (p 2138) (p 2352) (p 2363) (p 2573) (p 3366) (p 3519) (p 3694) (p 4376) (p 5118) (p 5568) (derived40810 p h) (h 24085)

theorem derived51081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2248) ∨ (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2807) ∨ (¬ p 3555) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step51081 (p 2027) (p 2191) (p 2248) (p 2264) (p 2459) (p 2807) (p 3555) (p 5118) (p 5568) (derived40810 p h) (h 24086)

theorem derived51082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 2891) ∨ (¬ p 3556) ∨ (¬ p 3948) ∨ (¬ p 4031) ∨ (¬ p 4814) :=
  ElevenRUP.step51082 (p 2027) (p 2440) (p 2891) (p 3556) (p 3948) (p 4031) (p 4814) (derived40810 p h) (h 24087)

theorem derived51084 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2786) ∨ (¬ p 3055) ∨ (¬ p 3822) ∨ (¬ p 4749) ∨ (¬ p 4841) :=
  ElevenRUP.step51084 (p 2027) (p 2307) (p 2786) (p 3055) (p 3822) (p 4749) (p 4841) (derived40810 p h) (h 24091)

theorem derived51086 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 3422) ∨ (¬ p 3475) ∨ (¬ p 4315) ∨ (¬ p 4701) :=
  ElevenRUP.step51086 (p 2027) (p 2579) (p 2662) (p 3422) (p 3475) (p 4315) (p 4701) (derived40810 p h) (h 24093)

theorem derived51087 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2662) ∨ (¬ p 3201) ∨ (¬ p 3475) ∨ (¬ p 3540) ∨ (¬ p 4315) ∨ (¬ p 4701) :=
  ElevenRUP.step51087 (p 2027) (p 2662) (p 3201) (p 3475) (p 3540) (p 4315) (p 4701) (derived40810 p h) (h 24094)

theorem derived51092 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2528) ∨ (¬ p 2881) ∨ (¬ p 2891) ∨ (¬ p 3055) ∨ (¬ p 4340) ∨ (¬ p 4438) ∨ (¬ p 4736) ∨ (¬ p 5368) :=
  ElevenRUP.step51092 (p 2027) (p 2210) (p 2528) (p 2881) (p 2891) (p 3055) (p 4340) (p 4438) (p 4736) (p 5368) (derived40810 p h) (h 24099)

theorem derived51093 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3055) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3584) ∨ (¬ p 4137) ∨ (¬ p 4604) ∨ (¬ p 4736) :=
  ElevenRUP.step51093 (p 2027) (p 2459) (p 3055) (p 3399) (p 3527) (p 3584) (p 4137) (p 4604) (p 4736) (derived40810 p h) (h 24100)

theorem derived51094 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2542) ∨ (¬ p 4340) ∨ (¬ p 4355) ∨ (¬ p 4750) ∨ (¬ p 5368) :=
  ElevenRUP.step51094 (p 2027) (p 2528) (p 2542) (p 4340) (p 4355) (p 4750) (p 5368) (derived40810 p h) (h 24101)

theorem derived51095 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2608) ∨ (¬ p 2619) ∨ (¬ p 2839) ∨ (¬ p 4902) ∨ (¬ p 5193) :=
  ElevenRUP.step51095 (p 2027) (p 2459) (p 2476) (p 2534) (p 2608) (p 2619) (p 2839) (p 4902) (p 5193) (derived40810 p h) (h 24102)

theorem derived51098 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2952) ∨ (¬ p 3027) ∨ (¬ p 3879) ∨ (¬ p 4110) ∨ (¬ p 4333) ∨ (¬ p 4558) :=
  ElevenRUP.step51098 (p 2027) (p 2252) (p 2952) (p 3027) (p 3879) (p 4110) (p 4333) (p 4558) (derived40810 p h) (h 24105)

theorem derived51099 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2742) ∨ (¬ p 3189) ∨ (¬ p 3346) ∨ (¬ p 3363) ∨ (¬ p 3585) ∨ (¬ p 4009) ∨ (¬ p 4425) ∨ (¬ p 4737) ∨ (¬ p 5119) :=
  ElevenRUP.step51099 (p 2027) (p 2696) (p 2742) (p 3189) (p 3346) (p 3363) (p 3585) (p 4009) (p 4425) (p 4737) (p 5119) (derived40810 p h) (h 24106)

theorem derived51102 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2951) ∨ (¬ p 3212) ∨ (¬ p 4385) ∨ (¬ p 4392) ∨ (¬ p 4701) :=
  ElevenRUP.step51102 (p 2027) (p 2630) (p 2951) (p 3212) (p 4385) (p 4392) (p 4701) (derived40810 p h) (h 24109)

theorem derived51103 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2727) ∨ (¬ p 3368) ∨ (¬ p 4173) ∨ (¬ p 4701) :=
  ElevenRUP.step51103 (p 2027) (p 2284) (p 2727) (p 3368) (p 4173) (p 4701) (derived40810 p h) (h 24110)

theorem derived51105 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 2807) ∨ (¬ p 2952) ∨ (¬ p 2996) ∨ (¬ p 4701) :=
  ElevenRUP.step51105 (p 2027) (p 2727) (p 2807) (p 2952) (p 2996) (p 4701) (derived40810 p h) (h 24112)

theorem derived51107 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2598) ∨ (¬ p 2922) ∨ (¬ p 3590) ∨ (¬ p 3698) ∨ (¬ p 4646) :=
  ElevenRUP.step51107 (p 2027) (p 2138) (p 2598) (p 2922) (p 3590) (p 3698) (p 4646) (derived40810 p h) (h 24114)

theorem derived51108 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2146) ∨ (¬ p 2192) ∨ (¬ p 3051) ∨ (¬ p 3486) ∨ (¬ p 3758) :=
  ElevenRUP.step51108 (p 2027) (p 2146) (p 2192) (p 3051) (p 3486) (p 3758) (derived40810 p h) (h 24117)

theorem derived51109 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2608) ∨ (¬ p 2707) ∨ (¬ p 2717) ∨ (¬ p 3016) ∨ (¬ p 4256) ∨ (¬ p 4438) ∨ (¬ p 5193) :=
  ElevenRUP.step51109 (p 2027) (p 2579) (p 2608) (p 2707) (p 2717) (p 3016) (p 4256) (p 4438) (p 5193) (derived40810 p h) (h 24118)

theorem derived51110 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2427) ∨ (¬ p 3486) ∨ (¬ p 3758) ∨ (¬ p 4882) :=
  ElevenRUP.step51110 (p 2027) (p 2192) (p 2427) (p 3486) (p 3758) (p 4882) (derived40810 p h) (h 24119)

theorem derived51112 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2230) ∨ (¬ p 2922) ∨ (¬ p 3238) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4079) ∨ (¬ p 4276) ∨ (¬ p 4736) :=
  ElevenRUP.step51112 (p 2027) (p 2177) (p 2230) (p 2922) (p 3238) (p 3425) (p 3659) (p 4079) (p 4276) (p 4736) (derived40810 p h) (h 24121)

theorem derived51113 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2313) ∨ (¬ p 2577) ∨ (¬ p 2662) ∨ (¬ p 4315) ∨ (¬ p 4426) ∨ (¬ p 4701) :=
  ElevenRUP.step51113 (p 2027) (p 2122) (p 2313) (p 2577) (p 2662) (p 4315) (p 4426) (p 4701) (derived40810 p h) (h 24122)

theorem derived51114 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2641) ∨ (¬ p 3055) ∨ (¬ p 3323) ∨ (¬ p 3876) ∨ (¬ p 4278) ∨ (¬ p 4621) ∨ (¬ p 4736) :=
  ElevenRUP.step51114 (p 2027) (p 2241) (p 2641) (p 3055) (p 3323) (p 3876) (p 4278) (p 4621) (p 4736) (derived40810 p h) (h 24123)

theorem derived51116 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3156) ∨ (¬ p 3949) ∨ (¬ p 4208) ∨ (¬ p 4902) :=
  ElevenRUP.step51116 (p 2027) (p 2459) (p 3156) (p 3949) (p 4208) (p 4902) (derived40810 p h) (h 24125)

theorem derived51119 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3105) ∨ (¬ p 3694) ∨ (¬ p 4134) ∨ (¬ p 4347) :=
  ElevenRUP.step51119 (p 2027) (p 2532) (p 3105) (p 3694) (p 4134) (p 4347) (derived40810 p h) (h 24128)

theorem derived51121 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3105) ∨ (¬ p 3461) ∨ (¬ p 4244) ∨ (¬ p 4381) ∨ (¬ p 5045) :=
  ElevenRUP.step51121 (p 1983) (p 2027) (p 2938) (p 3105) (p 3461) (p 4244) (p 4381) (p 5045) (h 2143) (derived40810 p h) (derived40888 p h) (h 24134)

theorem derived51123 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2946) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4786) ∨ (¬ p 5118) :=
  ElevenRUP.step51123 (p 2027) (p 2946) (p 3055) (p 3146) (p 3156) (p 3874) (p 4286) (p 4786) (p 5118) (derived40810 p h) (h 24137)

theorem derived51125 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2373) ∨ (¬ p 2542) ∨ (¬ p 2651) ∨ (¬ p 3588) ∨ (¬ p 3659) ∨ (¬ p 3954) ∨ (¬ p 4902) :=
  ElevenRUP.step51125 (p 2027) (p 2248) (p 2373) (p 2542) (p 2651) (p 3588) (p 3659) (p 3954) (p 4902) (derived40810 p h) (h 24139)

theorem derived51127 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2284) ∨ (¬ p 3497) ∨ (¬ p 4363) ∨ (¬ p 5043) :=
  ElevenRUP.step51127 (p 2027) (p 2166) (p 2284) (p 3497) (p 4363) (p 5043) (derived40810 p h) (h 24142)

theorem derived51129 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2274) ∨ (¬ p 2563) ∨ (¬ p 2608) ∨ (¬ p 3519) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 4376) ∨ (¬ p 4501) :=
  ElevenRUP.step51129 (p 2027) (p 2230) (p 2274) (p 2563) (p 2608) (p 3519) (p 3591) (p 3923) (p 4376) (p 4501) (derived40810 p h) (h 24145)

theorem derived51130 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2573) ∨ (¬ p 2589) ∨ (¬ p 3574) ∨ (¬ p 4814) :=
  ElevenRUP.step51130 (p 2027) (p 2406) (p 2573) (p 2589) (p 3574) (p 4814) (derived40810 p h) (h 24148)

theorem derived51135 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2532) ∨ (¬ p 3115) ∨ (¬ p 3497) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step51135 (p 2027) (p 2532) (p 3115) (p 3497) (p 5118) (p 5568) (derived40810 p h) (h 24155)

theorem derived51136 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 4019) ∨ (¬ p 4119) ∨ (¬ p 4647) ∨ (¬ p 4800) ∨ (¬ p 5568) :=
  ElevenRUP.step51136 (p 2027) (p 2911) (p 4019) (p 4119) (p 4647) (p 4800) (p 5568) (derived40810 p h) (h 24156)

theorem derived51137 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2156) ∨ (¬ p 2459) ∨ (¬ p 2958) ∨ (¬ p 3156) ∨ (¬ p 3952) ∨ (¬ p 4340) ∨ (¬ p 4786) ∨ (¬ p 4902) :=
  ElevenRUP.step51137 (p 2027) (p 2104) (p 2156) (p 2459) (p 2958) (p 3156) (p 3952) (p 4340) (p 4786) (p 4902) (derived40810 p h) (h 24157)

theorem derived51139 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2685) ∨ (¬ p 3486) ∨ (¬ p 4066) ∨ (¬ p 4283) ∨ (¬ p 4315) ∨ (¬ p 4957) :=
  ElevenRUP.step51139 (p 2027) (p 2685) (p 3486) (p 4066) (p 4283) (p 4315) (p 4957) (derived40810 p h) (h 24159)

theorem derived51140 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2318) ∨ (¬ p 2685) ∨ (¬ p 3097) ∨ (¬ p 4066) ∨ (¬ p 4195) ∨ (¬ p 4560) :=
  ElevenRUP.step51140 (p 2027) (p 2318) (p 2685) (p 3097) (p 4066) (p 4195) (p 4560) (derived40810 p h) (h 24160)

theorem derived51141 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2373) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4110) ∨ (¬ p 4902) :=
  ElevenRUP.step51141 (p 2027) (p 2139) (p 2156) (p 2373) (p 3365) (p 3553) (p 3572) (p 4110) (p 4902) (derived40810 p h) (h 24161)

theorem derived51142 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2563) ∨ (¬ p 2761) ∨ (¬ p 3125) ∨ (¬ p 3292) ∨ (¬ p 4236) ∨ (¬ p 4419) ∨ (¬ p 4621) ∨ (¬ p 5284) :=
  ElevenRUP.step51142 (p 2027) (p 2230) (p 2563) (p 2761) (p 3125) (p 3292) (p 4236) (p 4419) (p 4621) (p 5284) (derived40810 p h) (h 24162)

theorem derived51144 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4419) ∨ (¬ p 5118) ∨ (¬ p 5558) :=
  ElevenRUP.step51144 (p 2027) (p 2230) (p 2373) (p 3146) (p 3425) (p 3659) (p 4419) (p 5118) (p 5558) (derived40810 p h) (h 24164)

theorem derived51145 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3291) ∨ (¬ p 3744) ∨ (¬ p 3755) ∨ (¬ p 4038) ∨ (¬ p 4195) ∨ (¬ p 4560) :=
  ElevenRUP.step51145 (p 2027) (p 3291) (p 3744) (p 3755) (p 4038) (p 4195) (p 4560) (derived40810 p h) (h 24165)

theorem derived51146 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2781) ∨ (¬ p 3125) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 3947) ∨ (¬ p 3989) ∨ (¬ p 4621) :=
  ElevenRUP.step51146 (p 2027) (p 2383) (p 2781) (p 3125) (p 3365) (p 3572) (p 3947) (p 3989) (p 4621) (derived40810 p h) (h 24166)

theorem derived51147 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 2608) ∨ (¬ p 3246) ∨ (¬ p 3519) ∨ (¬ p 3553) ∨ (¬ p 4366) ∨ (¬ p 4376) ∨ (¬ p 4424) ∨ (¬ p 4668) ∨ (¬ p 4777) :=
  ElevenRUP.step51147 (p 2027) (p 2230) (p 2427) (p 2608) (p 3246) (p 3519) (p 3553) (p 4366) (p 4376) (p 4424) (p 4668) (p 4777) (derived40810 p h) (h 24167)

theorem derived51152 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2737) ∨ (¬ p 3555) ∨ (¬ p 4418) ∨ (¬ p 5049) :=
  ElevenRUP.step51152 (p 2027) (p 2608) (p 2737) (p 3555) (p 4418) (p 5049) (derived40810 p h) (h 24173)

theorem derived51153 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2657) ∨ (¬ p 3146) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3584) ∨ (¬ p 3683) ∨ (¬ p 4137) ∨ (¬ p 4236) ∨ (¬ p 4377) ∨ (¬ p 4446) ∨ (¬ p 4604) :=
  ElevenRUP.step51153 (p 2027) (p 2657) (p 3146) (p 3366) (p 3449) (p 3555) (p 3584) (p 3683) (p 4137) (p 4236) (p 4377) (p 4446) (p 4604) (derived40810 p h) (h 24174)

theorem derived51154 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2578) ∨ (¬ p 3422) ∨ (¬ p 3874) ∨ (¬ p 4432) ∨ (¬ p 4501) :=
  ElevenRUP.step51154 (p 2027) (p 2307) (p 2578) (p 3422) (p 3874) (p 4432) (p 4501) (derived40810 p h) (h 24175)

theorem derived51155 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 3055) ∨ (¬ p 3125) ∨ (¬ p 3461) ∨ (¬ p 3876) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step51155 (p 2027) (p 2139) (p 2156) (p 3055) (p 3125) (p 3461) (p 3876) (p 4831) (p 5503) (derived40810 p h) (h 24176)

theorem derived51156 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2299) ∨ (¬ p 2810) ∨ (¬ p 2881) ∨ (¬ p 3051) ∨ (¬ p 3365) ∨ (¬ p 3742) ∨ (¬ p 4712) :=
  ElevenRUP.step51156 (p 2027) (p 2139) (p 2299) (p 2810) (p 2881) (p 3051) (p 3365) (p 3742) (p 4712) (derived40810 p h) (h 24177)

theorem derived51157 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 3055) ∨ (¬ p 3366) ∨ (¬ p 3370) ∨ (¬ p 3874) ∨ (¬ p 4286) ∨ (¬ p 4377) ∨ (¬ p 5118) :=
  ElevenRUP.step51157 (p 2027) (p 2156) (p 2187) (p 2363) (p 3055) (p 3366) (p 3370) (p 3874) (p 4286) (p 4377) (p 5118) (derived40810 p h) (h 24178)

theorem derived51158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2274) ∨ (¬ p 3989) ∨ (¬ p 4138) ∨ (¬ p 4361) :=
  ElevenRUP.step51158 (p 2027) (p 2264) (p 2274) (p 3989) (p 4138) (p 4361) (derived40810 p h) (h 24179)

theorem derived51160 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 3365) ∨ (¬ p 3572) ∨ (¬ p 4391) ∨ (¬ p 4831) :=
  ElevenRUP.step51160 (p 2027) (p 2139) (p 2220) (p 3146) (p 3266) (p 3365) (p 3572) (p 4391) (p 4831) (derived40810 p h) (h 24182)

theorem derived51161 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 3125) ∨ (¬ p 3365) ∨ (¬ p 3461) ∨ (¬ p 3572) ∨ (¬ p 4391) ∨ (¬ p 4831) :=
  ElevenRUP.step51161 (p 2027) (p 2139) (p 2156) (p 3125) (p 3365) (p 3461) (p 3572) (p 4391) (p 4831) (derived40810 p h) (h 24183)

theorem derived51163 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2534) ∨ (¬ p 2657) ∨ (¬ p 3366) ∨ (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3979) ∨ (¬ p 4236) ∨ (¬ p 4256) ∨ (¬ p 4318) ∨ (¬ p 4377) ∨ (¬ p 5122) :=
  ElevenRUP.step51163 (p 2027) (p 2534) (p 2657) (p 3366) (p 3449) (p 3555) (p 3979) (p 4236) (p 4256) (p 4318) (p 4377) (p 5122) (derived40810 p h) (h 24185)

theorem derived51167 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2510) ∨ (¬ p 2528) ∨ (¬ p 3989) ∨ (¬ p 4347) ∨ (¬ p 4718) :=
  ElevenRUP.step51167 (p 2027) (p 2510) (p 2528) (p 3989) (p 4347) (p 4718) (derived40810 p h) (h 24192)

theorem derived51171 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2220) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 3876) ∨ (¬ p 4831) ∨ (¬ p 5503) :=
  ElevenRUP.step51171 (p 2027) (p 2139) (p 2220) (p 3055) (p 3146) (p 3266) (p 3876) (p 4831) (p 5503) (derived40810 p h) (h 24198)

theorem derived51173 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2252) ∨ (¬ p 2741) ∨ (¬ p 2797) ∨ (¬ p 2963) ∨ (¬ p 3073) ∨ (¬ p 3449) ∨ (¬ p 3452) ∨ (¬ p 4035) ∨ (¬ p 4190) ∨ (¬ p 4376) ∨ (¬ p 4604) :=
  ElevenRUP.step51173 (p 2027) (p 2252) (p 2741) (p 2797) (p 2963) (p 3073) (p 3449) (p 3452) (p 4035) (p 4190) (p 4376) (p 4604) (derived40810 p h) (h 24201)

theorem derived51175 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 4009) ∨ (¬ p 4044) ∨ (¬ p 4361) ∨ (¬ p 5558) :=
  ElevenRUP.step51175 (p 2027) (p 2299) (p 4009) (p 4044) (p 4361) (p 5558) (derived40810 p h) (h 24204)

theorem derived51177 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4034) ∨ (¬ p 4079) ∨ (¬ p 4668) ∨ (¬ p 4736) :=
  ElevenRUP.step51177 (p 2027) (p 2230) (p 2891) (p 3246) (p 3365) (p 3553) (p 3572) (p 4034) (p 4079) (p 4668) (p 4736) (derived40810 p h) (h 24206)

theorem derived51179 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2891) ∨ (¬ p 3246) ∨ (¬ p 3365) ∨ (¬ p 3553) ∨ (¬ p 3572) ∨ (¬ p 4668) ∨ (¬ p 4736) :=
  ElevenRUP.step51179 (p 2027) (p 2210) (p 2891) (p 3246) (p 3365) (p 3553) (p 3572) (p 4668) (p 4736) (derived40810 p h) (h 24208)

theorem derived51181 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2810) ∨ (¬ p 3146) ∨ (¬ p 3359) ∨ (¬ p 3365) ∨ (¬ p 4697) ∨ (¬ p 4736) :=
  ElevenRUP.step51181 (p 2027) (p 2166) (p 2210) (p 2810) (p 3146) (p 3359) (p 3365) (p 4697) (p 4736) (derived40810 p h) (h 24210)

theorem derived51182 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2745) ∨ (¬ p 2951) ∨ (¬ p 3136) ∨ (¬ p 4238) ∨ (¬ p 4261) ∨ (¬ p 4262) :=
  ElevenRUP.step51182 (p 2027) (p 2088) (p 2745) (p 2951) (p 3136) (p 4238) (p 4261) (p 4262) (derived40810 p h) (h 24211)

theorem derived51190 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2685) ∨ (¬ p 3414) ∨ (¬ p 3877) ∨ (¬ p 4236) ∨ (¬ p 4736) ∨ (¬ p 4774) :=
  ElevenRUP.step51190 (p 2027) (p 2187) (p 2192) (p 2210) (p 2685) (p 3414) (p 3877) (p 4236) (p 4736) (p 4774) (derived40810 p h) (h 24222)

theorem derived51195 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2891) ∨ (¬ p 3743) ∨ (¬ p 4114) ∨ (¬ p 4261) ∨ (¬ p 4492) ∨ (¬ p 4558) :=
  ElevenRUP.step51195 (p 2027) (p 2088) (p 2891) (p 3743) (p 4114) (p 4261) (p 4492) (p 4558) (derived40810 p h) (h 24228)

theorem derived51197 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2295) ∨ (¬ p 2641) ∨ (¬ p 3055) ∨ (¬ p 3584) ∨ (¬ p 3956) ∨ (¬ p 4501) ∨ (¬ p 4736) :=
  ElevenRUP.step51197 (p 2027) (p 2241) (p 2295) (p 2641) (p 3055) (p 3584) (p 3956) (p 4501) (p 4736) (derived40810 p h) (h 24230)

theorem derived51198 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2284) ∨ (¬ p 2992) ∨ (¬ p 3055) ∨ (¬ p 3684) ∨ (¬ p 3880) ∨ (¬ p 4507) ∨ (¬ p 4736) :=
  ElevenRUP.step51198 (p 2027) (p 2241) (p 2284) (p 2992) (p 3055) (p 3684) (p 3880) (p 4507) (p 4736) (derived40810 p h) (h 24231)

theorem derived51200 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2819) ∨ (¬ p 2901) ∨ (¬ p 2957) ∨ (¬ p 4198) ∨ (¬ p 4428) ∨ (¬ p 4558) :=
  ElevenRUP.step51200 (p 2027) (p 2387) (p 2819) (p 2901) (p 2957) (p 4198) (p 4428) (p 4558) (derived40810 p h) (h 24233)

theorem derived51201 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 3333) ∨ (¬ p 3584) ∨ (¬ p 4331) ∨ (¬ p 4624) :=
  ElevenRUP.step51201 (p 2027) (p 2588) (p 3333) (p 3584) (p 4331) (p 4624) (derived40810 p h) (h 24234)

theorem derived51202 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2946) ∨ (¬ p 3146) ∨ (¬ p 3156) ∨ (¬ p 3591) ∨ (¬ p 3990) ∨ (¬ p 4026) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step51202 (p 2027) (p 2248) (p 2946) (p 3146) (p 3156) (p 3591) (p 3990) (p 4026) (p 5118) (p 5580) (derived40810 p h) (h 24239)

theorem derived51205 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2992) ∨ (¬ p 3156) ∨ (¬ p 4340) ∨ (¬ p 4736) ∨ (¬ p 4902) :=
  ElevenRUP.step51205 (p 2027) (p 2104) (p 2241) (p 2459) (p 2992) (p 3156) (p 4340) (p 4736) (p 4902) (derived40810 p h) (h 24243)

theorem derived51206 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 3097) ∨ (¬ p 3955) ∨ (¬ p 4114) ∨ (¬ p 4347) ∨ (¬ p 4489) :=
  ElevenRUP.step51206 (p 2027) (p 2088) (p 3097) (p 3955) (p 4114) (p 4347) (p 4489) (derived40810 p h) (h 24244)

theorem derived51211 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 3055) ∨ (¬ p 3073) ∨ (¬ p 3644) ∨ (¬ p 3692) ∨ (¬ p 3876) ∨ (¬ p 4496) ∨ (¬ p 4736) ∨ (¬ p 4902) :=
  ElevenRUP.step51211 (p 2027) (p 2210) (p 3055) (p 3073) (p 3644) (p 3692) (p 3876) (p 4496) (p 4736) (p 4902) (derived40810 p h) (h 24249)

theorem derived51212 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) ∨ (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 3201) ∨ (¬ p 3540) ∨ (¬ p 3874) ∨ (¬ p 4384) ∨ (¬ p 5193) :=
  ElevenRUP.step51212 (p 2027) (p 2187) (p 2192) (p 2210) (p 3201) (p 3540) (p 3874) (p 4384) (p 5193) (derived40810 p h) (h 24250)

theorem derived51213 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2590) ∨ (¬ p 3737) ∨ (¬ p 4539) ∨ (¬ p 5514) :=
  ElevenRUP.step51213 (p 2027) (p 2156) (p 2590) (p 3737) (p 4539) (p 5514) (derived40810 p h) (h 24251)

theorem derived51215 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2373) ∨ (¬ p 2459) ∨ (¬ p 2542) ∨ (¬ p 2651) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4902) :=
  ElevenRUP.step51215 (p 2027) (p 2248) (p 2373) (p 2459) (p 2542) (p 2651) (p 3860) (p 4261) (p 4902) (derived40810 p h) (h 24254)

theorem derived51216 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2737) ∨ (¬ p 3452) ∨ (¬ p 3590) ∨ (¬ p 4749) :=
  ElevenRUP.step51216 (p 2027) (p 2608) (p 2737) (p 3452) (p 3590) (p 4749) (derived40810 p h) (h 24257)

theorem derived51217 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2373) ∨ (¬ p 3055) ∨ (¬ p 3146) ∨ (¬ p 3695) :=
  ElevenRUP.step51217 (p 1982) (p 2027) (p 2132) (p 2373) (p 2842) (p 3055) (p 3146) (p 3695) (h 2142) (derived40810 p h) (derived40885 p h) (h 24258)

theorem derived51218 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 2668) ∨ (¬ p 3880) ∨ (¬ p 4446) ∨ (¬ p 4560) ∨ (¬ p 4993) :=
  ElevenRUP.step51218 (p 2027) (p 2563) (p 2668) (p 3880) (p 4446) (p 4560) (p 4993) (derived40810 p h) (h 24259)

theorem derived51221 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3989) ∨ (¬ p 4110) ∨ (¬ p 4140) ∨ (¬ p 4501) :=
  ElevenRUP.step51221 (p 2027) (p 2427) (p 3989) (p 4110) (p 4140) (p 4501) (derived40810 p h) (h 24262)

theorem derived51222 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2363) ∨ (¬ p 2373) ∨ (¬ p 4110) ∨ (¬ p 4399) ∨ (¬ p 4441) :=
  ElevenRUP.step51222 (p 1982) (p 2027) (p 2156) (p 2233) (p 2363) (p 2373) (p 4110) (p 4399) (p 4441) (h 2142) (derived40810 p h) (derived40868 p h) (h 24263)

theorem derived51226 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2247) ∨ (¬ p 2427) ∨ (¬ p 2996) ∨ (¬ p 3246) ∨ (¬ p 3553) ∨ (¬ p 4668) ∨ (¬ p 5190) :=
  ElevenRUP.step51226 (p 2027) (p 2230) (p 2247) (p 2427) (p 2996) (p 3246) (p 3553) (p 4668) (p 5190) (derived40810 p h) (h 24268)

theorem derived51227 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2696) ∨ (¬ p 2850) ∨ (¬ p 3905) ∨ (¬ p 4749) :=
  ElevenRUP.step51227 (p 2027) (p 2589) (p 2696) (p 2850) (p 3905) (p 4749) (derived40810 p h) (h 24269)

theorem derived51229 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2137) ∨ (¬ p 2156) ∨ (¬ p 2737) ∨ (¬ p 4173) ∨ (¬ p 4874) ∨ (¬ p 5049) :=
  ElevenRUP.step51229 (p 2027) (p 2137) (p 2156) (p 2737) (p 4173) (p 4874) (p 5049) (derived40810 p h) (h 24271)

theorem derived51230 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 3055) ∨ (¬ p 3644) ∨ (¬ p 3742) ∨ (¬ p 4343) :=
  ElevenRUP.step51230 (p 1987) (p 2027) (p 2633) (p 2696) (p 3055) (p 3644) (p 3742) (p 4343) (h 2147) (derived40810 p h) (derived40879 p h) (h 24272)

theorem derived51231 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3486) ∨ (¬ p 3644) ∨ (¬ p 4042) ∨ (¬ p 4277) :=
  ElevenRUP.step51231 (p 2027) (p 2166) (p 3486) (p 3644) (p 4042) (p 4277) (derived40810 p h) (h 24273)

theorem derived51232 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2742) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 3905) ∨ (¬ p 4281) ∨ (¬ p 5052) :=
  ElevenRUP.step51232 (p 2027) (p 2132) (p 2742) (p 2922) (p 3540) (p 3905) (p 4281) (p 5052) (derived40810 p h) (h 24274)

theorem derived51233 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3540) ∨ (¬ p 4110) ∨ (¬ p 4399) ∨ (¬ p 4644) :=
  ElevenRUP.step51233 (p 2027) (p 2156) (p 3540) (p 4110) (p 4399) (p 4644) (derived40810 p h) (h 24277)

theorem derived51234 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2742) ∨ (¬ p 2778) ∨ (¬ p 3319) ∨ (¬ p 3946) ∨ (¬ p 4759) ∨ (¬ p 5052) :=
  ElevenRUP.step51234 (p 2027) (p 2132) (p 2742) (p 2778) (p 3319) (p 3946) (p 4759) (p 5052) (derived40810 p h) (h 24278)

theorem derived51235 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4668) :=
  ElevenRUP.step51235 (p 2027) (p 2248) (p 2417) (p 2437) (p 2651) (p 3486) (p 3555) (p 3570) (p 4668) (derived40810 p h) (h 24280)

theorem derived51236 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2295) ∨ (¬ p 2331) ∨ (¬ p 2396) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4668) :=
  ElevenRUP.step51236 (p 2027) (p 2248) (p 2295) (p 2331) (p 2396) (p 3486) (p 3555) (p 3570) (p 4668) (derived40810 p h) (h 24281)

theorem derived51238 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2470) ∨ (¬ p 3343) ∨ (¬ p 3366) ∨ (¬ p 3371) ∨ (¬ p 3425) ∨ (¬ p 3555) ∨ (¬ p 4256) ∨ (¬ p 4324) ∨ (¬ p 4638) ∨ (¬ p 5190) :=
  ElevenRUP.step51238 (p 2027) (p 2470) (p 3343) (p 3366) (p 3371) (p 3425) (p 3555) (p 4256) (p 4324) (p 4638) (p 5190) (derived40810 p h) (h 24283)

theorem derived51242 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2331) ∨ (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 3694) ∨ (¬ p 4786) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step51242 (p 2027) (p 2138) (p 2331) (p 2363) (p 2668) (p 3694) (p 4786) (p 5118) (p 5568) (derived40810 p h) (h 24289)

theorem derived51243 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3564) ∨ (¬ p 3956) ∨ (¬ p 4345) ∨ (¬ p 5118) ∨ (¬ p 5580) :=
  ElevenRUP.step51243 (p 2027) (p 3564) (p 3956) (p 4345) (p 5118) (p 5580) (derived40810 p h) (h 24290)

theorem derived51244 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 3876) ∨ (¬ p 3946) ∨ (¬ p 4031) ∨ (¬ p 4198) ∨ (¬ p 4375) ∨ (¬ p 4644) :=
  ElevenRUP.step51244 (p 2027) (p 3483) (p 3876) (p 3946) (p 4031) (p 4198) (p 4375) (p 4644) (derived40810 p h) (h 24291)

theorem derived51245 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (¬ p 2542) ∨ (¬ p 3878) ∨ (¬ p 4118) ∨ (¬ p 4608) :=
  ElevenRUP.step51245 (p 2027) (p 2528) (p 2542) (p 3878) (p 4118) (p 4608) (derived40810 p h) (h 24292)

theorem derived51248 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 3212) ∨ (¬ p 3556) ∨ (¬ p 3758) ∨ (¬ p 5046) :=
  ElevenRUP.step51248 (p 2027) (p 2870) (p 3212) (p 3556) (p 3758) (p 5046) (derived40810 p h) (h 24295)

theorem derived51251 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2295) ∨ (¬ p 2573) ∨ (¬ p 3791) ∨ (¬ p 4120) ∨ (¬ p 4188) ∨ (¬ p 4340) ∨ (¬ p 4389) ∨ (¬ p 4419) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step51251 (p 2027) (p 2136) (p 2295) (p 2573) (p 3791) (p 4120) (p 4188) (p 4340) (p 4389) (p 4419) (p 4444) (p 4826) (derived40810 p h) (h 24298)

theorem derived51252 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2573) ∨ (¬ p 3343) ∨ (¬ p 3574) ∨ (¬ p 3690) ∨ (¬ p 4244) ∨ (¬ p 4419) ∨ (¬ p 4638) :=
  ElevenRUP.step51252 (p 2027) (p 2138) (p 2573) (p 3343) (p 3574) (p 3690) (p 4244) (p 4419) (p 4638) (derived40810 p h) (h 24299)

theorem derived51253 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2331) ∨ (¬ p 3506) ∨ (¬ p 3690) ∨ (¬ p 4191) ∨ (¬ p 4244) ∨ (¬ p 4421) ∨ (¬ p 4621) ∨ (¬ p 4786) :=
  ElevenRUP.step51253 (p 2027) (p 2138) (p 2331) (p 3506) (p 3690) (p 4191) (p 4244) (p 4421) (p 4621) (p 4786) (derived40810 p h) (h 24300)

theorem derived51256 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3146) ∨ (¬ p 3860) ∨ (¬ p 4261) :=
  ElevenRUP.step51256 (p 1992) (p 2027) (p 2608) (p 3146) (p 3578) (p 3860) (p 4261) (h 2152) (derived40810 p h) (derived40900 p h) (h 24304)

theorem derived51259 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2241) ∨ (¬ p 2727) ∨ (¬ p 3083) ∨ (¬ p 3570) ∨ (¬ p 4244) ∨ (¬ p 4420) ∨ (¬ p 4736) :=
  ElevenRUP.step51259 (p 2027) (p 2138) (p 2241) (p 2727) (p 3083) (p 3570) (p 4244) (p 4420) (p 4736) (derived40810 p h) (h 24309)

theorem derived51261 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3212) ∨ (¬ p 3646) ∨ (¬ p 4624) ∨ (¬ p 5045) :=
  ElevenRUP.step51261 (p 2027) (p 3097) (p 3212) (p 3646) (p 4624) (p 5045) (derived40810 p h) (h 24312)

theorem derived51262 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3744) ∨ (¬ p 4110) ∨ (¬ p 4625) ∨ (¬ p 5193) :=
  ElevenRUP.step51262 (p 2027) (p 2241) (p 2449) (p 2589) (p 3027) (p 3744) (p 4110) (p 4625) (p 5193) (derived40810 p h) (h 24313)

theorem derived51263 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3055) ∨ (¬ p 3399) ∨ (¬ p 3527) ∨ (¬ p 3941) ∨ (¬ p 4425) ∨ (¬ p 4736) ∨ (¬ p 5119) ∨ (¬ p 5160) :=
  ElevenRUP.step51263 (p 2027) (p 3055) (p 3399) (p 3527) (p 3941) (p 4425) (p 4736) (p 5119) (p 5160) (derived40810 p h) (h 24314)

theorem derived51264 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3584) ∨ (¬ p 3956) ∨ (¬ p 4501) ∨ (¬ p 4710) :=
  ElevenRUP.step51264 (p 2027) (p 3201) (p 3584) (p 3956) (p 4501) (p 4710) (derived40810 p h) (h 24315)

theorem derived51265 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3055) ∨ (¬ p 3063) ∨ (¬ p 3093) ∨ (¬ p 3684) ∨ (¬ p 4736) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step51265 (p 2027) (p 2363) (p 3055) (p 3063) (p 3093) (p 3684) (p 4736) (p 4948) (p 5059) (derived40810 p h) (h 24316)

theorem derived51266 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3222) ∨ (¬ p 3347) ∨ (¬ p 4235) ∨ (¬ p 4952) ∨ (¬ p 5104) :=
  ElevenRUP.step51266 (p 2027) (p 2589) (p 3222) (p 3347) (p 4235) (p 4952) (p 5104) (derived40810 p h) (h 24318)

theorem derived51268 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 3055) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3644) ∨ (¬ p 3876) ∨ (¬ p 4668) ∨ (¬ p 4736) :=
  ElevenRUP.step51268 (p 2027) (p 2396) (p 3055) (p 3093) (p 3309) (p 3644) (p 3876) (p 4668) (p 4736) (derived40810 p h) (h 24320)

theorem derived51273 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2319) ∨ (¬ p 2341) ∨ (¬ p 2441) ∨ (¬ p 2982) ∨ (¬ p 3644) ∨ (p 4356) ∨ (¬ p 5046) :=
  ElevenRUP.step51273 (p 2027) (p 2319) (p 2341) (p 2441) (p 2982) (p 3644) (p 4356) (p 5046) (derived40810 p h) (h 24328)

theorem derived51274 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2608) ∨ (¬ p 3537) ∨ (¬ p 4019) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 5119) ∨ (¬ p 5193) :=
  ElevenRUP.step51274 (p 2027) (p 2579) (p 2608) (p 3537) (p 4019) (p 4137) (p 4191) (p 5119) (p 5193) (derived40810 p h) (h 24329)

theorem derived51275 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 2743) ∨ (¬ p 3414) ∨ (¬ p 4325) ∨ (¬ p 4787) :=
  ElevenRUP.step51275 (p 2027) (p 2707) (p 2743) (p 3414) (p 4325) (p 4787) (derived40810 p h) (h 24330)

theorem derived51276 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3319) ∨ (¬ p 4037) ∨ (¬ p 4111) ∨ (¬ p 4759) ∨ (¬ p 4975) :=
  ElevenRUP.step51276 (p 2027) (p 3319) (p 4037) (p 4111) (p 4759) (p 4975) (derived40810 p h) (h 24331)

theorem derived51277 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2963) ∨ (¬ p 3568) ∨ (¬ p 4426) ∨ (¬ p 4787) :=
  ElevenRUP.step51277 (p 2027) (p 2122) (p 2963) (p 3568) (p 4426) (p 4787) (derived40810 p h) (h 24332)

theorem derived51279 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3365) ∨ (¬ p 3683) ∨ (¬ p 3877) ∨ (¬ p 5008) :=
  ElevenRUP.step51279 (p 2027) (p 2598) (p 3365) (p 3683) (p 3877) (p 5008) (derived40810 p h) (h 24334)

theorem derived51280 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 3365) ∨ (¬ p 3683) ∨ (¬ p 4315) ∨ (¬ p 4701) :=
  ElevenRUP.step51280 (p 2027) (p 2598) (p 3365) (p 3683) (p 4315) (p 4701) (derived40810 p h) (h 24335)

theorem derived51290 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3246) ∨ (¬ p 3588) ∨ (¬ p 3659) ∨ (¬ p 3954) ∨ (¬ p 4668) :=
  ElevenRUP.step51290 (p 2027) (p 2248) (p 2901) (p 2946) (p 3246) (p 3588) (p 3659) (p 3954) (p 4668) (derived40810 p h) (h 24348)

theorem derived51291 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3201) ∨ (¬ p 3556) ∨ (¬ p 3569) ∨ (¬ p 3684) ∨ (¬ p 4533) :=
  ElevenRUP.step51291 (p 2027) (p 3201) (p 3556) (p 3569) (p 3684) (p 4533) (derived40810 p h) (h 24349)

theorem derived51294 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2427) ∨ (¬ p 2829) ∨ (¬ p 3365) ∨ (¬ p 3366) ∨ (¬ p 3483) ∨ (¬ p 3556) ∨ (¬ p 4368) ∨ (¬ p 4948) ∨ (¬ p 5052) :=
  ElevenRUP.step51294 (p 2027) (p 2143) (p 2427) (p 2829) (p 3365) (p 3366) (p 3483) (p 3556) (p 4368) (p 4948) (p 5052) (derived40810 p h) (h 24355)

theorem derived51296 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2313) ∨ (¬ p 2742) ∨ (¬ p 2778) ∨ (¬ p 3309) ∨ (¬ p 4759) ∨ (¬ p 5052) :=
  ElevenRUP.step51296 (p 2027) (p 2132) (p 2313) (p 2742) (p 2778) (p 3309) (p 4759) (p 5052) (derived40810 p h) (h 24360)

theorem derived51297 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3583) ∨ (¬ p 3758) ∨ (¬ p 3954) :=
  ElevenRUP.step51297 (p 1984) (p 2027) (p 2997) (p 3097) (p 3583) (p 3758) (p 3954) (h 2144) (derived40810 p h) (derived40890 p h) (h 24361)

theorem derived51298 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2870) ∨ (¬ p 3556) ∨ (¬ p 4110) ∨ (¬ p 4885) :=
  ElevenRUP.step51298 (p 2027) (p 2156) (p 2870) (p 3556) (p 4110) (p 4885) (derived40810 p h) (h 24362)

theorem derived51299 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 3166) ∨ (¬ p 3256) ∨ (¬ p 3266) ∨ (¬ p 3588) ∨ (¬ p 3954) ∨ (¬ p 4423) ∨ (¬ p 4831) :=
  ElevenRUP.step51299 (p 2027) (p 2248) (p 3166) (p 3256) (p 3266) (p 3588) (p 3954) (p 4423) (p 4831) (derived40810 p h) (h 24363)

theorem derived51301 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 4117) ∨ (p 5011) :=
  ElevenRUP.step51301 (p 1993) (p 2611) (p 2651) (p 4117) (p 5011) (h 2153) (derived40877 p h) (h 24365)

theorem derived51302 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2630) ∨ (¬ p 2696) ∨ (¬ p 3083) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 4596) ∨ (¬ p 4733) ∨ (¬ p 5015) :=
  ElevenRUP.step51302 (p 2027) (p 2313) (p 2630) (p 2696) (p 3083) (p 3309) (p 3923) (p 4596) (p 4733) (p 5015) (derived40810 p h) (h 24366)

theorem derived51303 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2299) ∨ (¬ p 2373) ∨ (¬ p 2542) ∨ (¬ p 2651) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4902) :=
  ElevenRUP.step51303 (p 2027) (p 2248) (p 2299) (p 2373) (p 2542) (p 2651) (p 3549) (p 3591) (p 4902) (derived40810 p h) (h 24367)

theorem derived51304 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4433) ∨ (¬ p 4733) :=
  ElevenRUP.step51304 (p 2027) (p 2363) (p 2696) (p 3136) (p 3156) (p 3860) (p 4261) (p 4433) (p 4733) (derived40810 p h) (h 24368)

theorem derived51305 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 2753) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3950) ∨ (¬ p 3989) ∨ (¬ p 4117) ∨ (¬ p 4347) ∨ (¬ p 4877) :=
  ElevenRUP.step51305 (p 2027) (p 2417) (p 2437) (p 2651) (p 2753) (p 3645) (p 3646) (p 3950) (p 3989) (p 4117) (p 4347) (p 4877) (derived40810 p h) (h 24370)

theorem derived51306 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 2911) ∨ (¬ p 3471) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3744) ∨ (¬ p 4191) ∨ (¬ p 4253) ∨ (¬ p 4877) ∨ (¬ p 5503) :=
  ElevenRUP.step51306 (p 1998) (p 2027) (p 2753) (p 2764) (p 2911) (p 3471) (p 3645) (p 3646) (p 3744) (p 4191) (p 4253) (p 4877) (p 5503) (h 2158) (derived40810 p h) (derived40882 p h) (h 24371)

theorem derived51307 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 3201) ∨ (¬ p 3204) ∨ (¬ p 3692) ∨ (¬ p 3868) ∨ (¬ p 4441) ∨ (¬ p 4444) ∨ (¬ p 4512) ∨ (¬ p 4826) ∨ (¬ p 4877) :=
  ElevenRUP.step51307 (p 2027) (p 2387) (p 2598) (p 2753) (p 3201) (p 3204) (p 3692) (p 3868) (p 4441) (p 4444) (p 4512) (p 4826) (p 4877) (derived40810 p h) (h 24372)

theorem derived51308 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 3201) ∨ (¬ p 3645) ∨ (¬ p 3646) ∨ (¬ p 3744) ∨ (¬ p 3868) ∨ (¬ p 4191) ∨ (¬ p 4826) ∨ (¬ p 4877) :=
  ElevenRUP.step51308 (p 2027) (p 2598) (p 2753) (p 3201) (p 3645) (p 3646) (p 3744) (p 3868) (p 4191) (p 4826) (p 4877) (derived40810 p h) (h 24373)

theorem derived51309 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2264) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) ∨ (¬ p 4877) :=
  ElevenRUP.step51309 (p 2027) (p 2210) (p 2264) (p 2685) (p 2696) (p 2753) (p 3817) (p 4366) (p 4666) (p 4877) (derived40810 p h) (h 24374)

theorem derived51311 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2753) ∨ (¬ p 3093) ∨ (¬ p 3286) ∨ (¬ p 3506) ∨ (¬ p 3817) ∨ (¬ p 4117) ∨ (¬ p 4366) ∨ (¬ p 4425) ∨ (¬ p 4512) ∨ (¬ p 4638) ∨ (¬ p 4877) :=
  ElevenRUP.step51311 (p 2027) (p 2753) (p 3093) (p 3286) (p 3506) (p 3817) (p 4117) (p 4366) (p 4425) (p 4512) (p 4638) (p 4877) (derived40810 p h) (h 24376)

theorem derived51314 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 3201) ∨ (¬ p 3860) ∨ (¬ p 3950) ∨ (¬ p 4261) ∨ (¬ p 4877) :=
  ElevenRUP.step51314 (p 2027) (p 2210) (p 2417) (p 2598) (p 2753) (p 3201) (p 3860) (p 3950) (p 4261) (p 4877) (derived40810 p h) (h 24379)

theorem derived51316 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2960) ∨ (¬ p 3051) ∨ (¬ p 3136) ∨ (¬ p 3572) ∨ (¬ p 3699) :=
  ElevenRUP.step51316 (p 2027) (p 2960) (p 3051) (p 3136) (p 3572) (p 3699) (derived40810 p h) (h 24381)

theorem derived51317 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2870) ∨ (¬ p 3742) ∨ (¬ p 4001) ∨ (¬ p 4885) :=
  ElevenRUP.step51317 (p 2027) (p 2542) (p 2870) (p 3742) (p 4001) (p 4885) (derived40810 p h) (h 24382)

theorem derived51318 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 3422) ∨ (¬ p 3684) ∨ (¬ p 3989) :=
  ElevenRUP.step51318 (p 1990) (p 2027) (p 2202) (p 2352) (p 3422) (p 3684) (p 3989) (h 2150) (derived40810 p h) (derived40867 p h) (h 24384)

theorem derived51320 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2901) ∨ (¬ p 2946) ∨ (¬ p 3954) ∨ (¬ p 4129) ∨ (¬ p 4379) ∨ (¬ p 4826) ∨ (¬ p 5387) :=
  ElevenRUP.step51320 (p 2027) (p 2248) (p 2901) (p 2946) (p 3954) (p 4129) (p 4379) (p 4826) (p 5387) (derived40810 p h) (h 24386)

theorem derived51321 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2437) ∨ (¬ p 2651) ∨ (¬ p 3555) ∨ (¬ p 3868) ∨ (¬ p 4322) ∨ (¬ p 4363) ∨ (¬ p 4826) :=
  ElevenRUP.step51321 (p 2027) (p 2248) (p 2437) (p 2651) (p 3555) (p 3868) (p 4322) (p 4363) (p 4826) (derived40810 p h) (h 24387)

theorem derived51322 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2505) ∨ (¬ p 2590) ∨ (¬ p 2928) ∨ (¬ p 3063) ∨ (¬ p 3956) ∨ (¬ p 4644) :=
  ElevenRUP.step51322 (p 2027) (p 2505) (p 2590) (p 2928) (p 3063) (p 3956) (p 4644) (derived40810 p h) (h 24388)

theorem derived51323 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 2952) ∨ (¬ p 3136) ∨ (¬ p 4236) ∨ (¬ p 4734) :=
  ElevenRUP.step51323 (p 2027) (p 2737) (p 2952) (p 3136) (p 4236) (p 4734) (derived40810 p h) (h 24389)

theorem derived51324 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2749) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4108) ∨ (¬ p 4281) ∨ (¬ p 4877) :=
  ElevenRUP.step51324 (p 2027) (p 2210) (p 2749) (p 2922) (p 3540) (p 4108) (p 4281) (p 4877) (derived40810 p h) (h 24390)

theorem derived51325 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 4210) ∨ (¬ p 4644) :=
  ElevenRUP.step51325 (p 2027) (p 2210) (p 2928) (p 3452) (p 4210) (p 4644) (derived40810 p h) (h 24391)

theorem derived51327 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2749) ∨ (¬ p 3027) ∨ (¬ p 3379) ∨ (¬ p 3414) ∨ (¬ p 5216) :=
  ElevenRUP.step51327 (p 2027) (p 2245) (p 2749) (p 3027) (p 3379) (p 3414) (p 5216) (derived40810 p h) (h 24394)

theorem derived51329 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2696) ∨ (¬ p 3136) ∨ (¬ p 3156) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 4733) ∨ (¬ p 4902) :=
  ElevenRUP.step51329 (p 2027) (p 2299) (p 2696) (p 3136) (p 3156) (p 3549) (p 3591) (p 4733) (p 4902) (derived40810 p h) (h 24396)

theorem derived51330 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2386) ∨ (¬ p 2387) ∨ (¬ p 2505) ∨ (¬ p 3063) ∨ (¬ p 3574) ∨ (¬ p 4814) :=
  ElevenRUP.step51330 (p 2027) (p 2386) (p 2387) (p 2505) (p 3063) (p 3574) (p 4814) (derived40810 p h) (h 24397)

theorem derived51331 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2499) ∨ (¬ p 2588) ∨ (¬ p 2668) ∨ (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 3055) ∨ (¬ p 4030) ∨ (¬ p 4405) ∨ (¬ p 4734) :=
  ElevenRUP.step51331 (p 2027) (p 2331) (p 2499) (p 2588) (p 2668) (p 2737) (p 2811) (p 3055) (p 4030) (p 4405) (p 4734) (derived40810 p h) (h 24398)

theorem derived51332 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2780) ∨ (¬ p 3016) ∨ (¬ p 4342) ∨ (¬ p 4750) :=
  ElevenRUP.step51332 (p 2027) (p 2598) (p 2780) (p 3016) (p 4342) (p 4750) (derived40810 p h) (h 24399)

theorem derived51333 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 3055) ∨ (¬ p 3695) ∨ (¬ p 3876) ∨ (¬ p 4644) :=
  ElevenRUP.step51333 (p 2027) (p 2132) (p 3055) (p 3695) (p 3876) (p 4644) (derived40810 p h) (h 24400)

theorem derived51334 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (¬ p 3527) ∨ (¬ p 3551) ∨ (¬ p 3687) ∨ (¬ p 5206) ∨ (¬ p 5216) :=
  ElevenRUP.step51334 (p 2027) (p 3379) (p 3527) (p 3551) (p 3687) (p 5206) (p 5216) (derived40810 p h) (h 24401)

theorem derived51335 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2870) ∨ (¬ p 3246) ∨ (¬ p 3452) ∨ (¬ p 3950) ∨ (¬ p 4733) :=
  ElevenRUP.step51335 (p 2027) (p 2132) (p 2509) (p 2534) (p 2870) (p 3246) (p 3452) (p 3950) (p 4733) (derived40810 p h) (h 24402)

theorem derived51337 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3591) ∨ (¬ p 3923) ∨ (¬ p 3950) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step51337 (p 2027) (p 2449) (p 2685) (p 2696) (p 3591) (p 3923) (p 3950) (p 4347) (p 4733) (derived40810 p h) (h 24404)

theorem derived51340 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2753) ∨ (¬ p 2870) ∨ (¬ p 2881) ∨ (¬ p 3379) ∨ (¬ p 3817) ∨ (¬ p 4366) ∨ (¬ p 4666) ∨ (¬ p 5216) :=
  ElevenRUP.step51340 (p 2027) (p 2132) (p 2753) (p 2870) (p 2881) (p 3379) (p 3817) (p 4366) (p 4666) (p 5216) (derived40810 p h) (h 24407)

theorem derived51344 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2753) ∨ (¬ p 2761) ∨ (¬ p 3347) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 3880) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5568) :=
  ElevenRUP.step51344 (p 2027) (p 2589) (p 2753) (p 2761) (p 3347) (p 3434) (p 3471) (p 3880) (p 5123) (p 5216) (p 5568) (derived40810 p h) (h 24411)

theorem derived51345 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2753) ∨ (¬ p 2807) ∨ (¬ p 3266) ∨ (¬ p 3379) ∨ (¬ p 3572) ∨ (¬ p 3834) ∨ (¬ p 4117) ∨ (¬ p 4321) ∨ (¬ p 5216) :=
  ElevenRUP.step51345 (p 1994) (p 2027) (p 2630) (p 2753) (p 2766) (p 2807) (p 3266) (p 3379) (p 3572) (p 3834) (p 4117) (p 4321) (p 5216) (h 2154) (derived40810 p h) (derived40884 p h) (h 24412)

theorem derived51346 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2696) ∨ (¬ p 3506) ∨ (¬ p 3755) ∨ (¬ p 3880) ∨ (¬ p 4729) ∨ (¬ p 5123) ∨ (¬ p 5568) :=
  ElevenRUP.step51346 (p 2027) (p 2589) (p 2696) (p 3506) (p 3755) (p 3880) (p 4729) (p 5123) (p 5568) (derived40810 p h) (h 24413)

theorem derived51347 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3692) ∨ (¬ p 3860) ∨ (¬ p 3906) ∨ (¬ p 3950) ∨ (¬ p 4877) :=
  ElevenRUP.step51347 (p 2027) (p 2210) (p 2449) (p 2685) (p 2696) (p 2753) (p 3692) (p 3860) (p 3906) (p 3950) (p 4877) (derived40810 p h) (h 24415)

theorem derived51349 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2807) ∨ (¬ p 3266) ∨ (¬ p 3346) ∨ (¬ p 3572) ∨ (¬ p 3755) ∨ (¬ p 4117) ∨ (¬ p 4425) ∨ (¬ p 4729) ∨ (¬ p 5109) :=
  ElevenRUP.step51349 (p 2027) (p 2807) (p 3266) (p 3346) (p 3572) (p 3755) (p 4117) (p 4425) (p 4729) (p 5109) (derived40810 p h) (h 24417)

theorem derived51350 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3347) ∨ (¬ p 3506) ∨ (¬ p 3755) ∨ (¬ p 3956) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5580) :=
  ElevenRUP.step51350 (p 2027) (p 2579) (p 2696) (p 2753) (p 3347) (p 3506) (p 3755) (p 3956) (p 5123) (p 5216) (p 5580) (derived40810 p h) (h 24418)

theorem derived51351 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2579) ∨ (¬ p 2753) ∨ (¬ p 3105) ∨ (¬ p 3347) ∨ (¬ p 3680) ∨ (¬ p 3956) ∨ (¬ p 5123) ∨ (¬ p 5216) ∨ (¬ p 5580) :=
  ElevenRUP.step51351 (p 2027) (p 2132) (p 2579) (p 2753) (p 3105) (p 3347) (p 3680) (p 3956) (p 5123) (p 5216) (p 5580) (derived40810 p h) (h 24419)

theorem derived51352 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2685) ∨ (¬ p 2753) ∨ (¬ p 2946) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4117) ∨ (¬ p 4315) ∨ (¬ p 4570) ∨ (¬ p 5216) :=
  ElevenRUP.step51352 (p 2027) (p 2177) (p 2685) (p 2753) (p 2946) (p 3347) (p 3540) (p 3644) (p 4117) (p 4315) (p 4570) (p 5216) (derived40810 p h) (h 24420)

theorem derived51353 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2901) ∨ (¬ p 3136) ∨ (¬ p 3347) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4556) ∨ (¬ p 5216) :=
  ElevenRUP.step51353 (p 2027) (p 2177) (p 2696) (p 2753) (p 2901) (p 3136) (p 3347) (p 3540) (p 3644) (p 4556) (p 5216) (derived40810 p h) (h 24421)

theorem derived51354 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2246) ∨ (¬ p 2579) ∨ (¬ p 2749) ∨ (¬ p 2946) ∨ (¬ p 3347) ∨ (¬ p 3755) ∨ (¬ p 3956) ∨ (¬ p 4039) ∨ (¬ p 4315) ∨ (¬ p 4347) ∨ (¬ p 4450) ∨ (¬ p 5216) :=
  ElevenRUP.step51354 (p 2027) (p 2246) (p 2579) (p 2749) (p 2946) (p 3347) (p 3755) (p 3956) (p 4039) (p 4315) (p 4347) (p 4450) (p 5216) (derived40810 p h) (h 24422)

theorem derived51357 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2579) ∨ (¬ p 2972) ∨ (¬ p 3347) ∨ (¬ p 3954) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 4450) ∨ (¬ p 5216) :=
  ElevenRUP.step51357 (p 2027) (p 2210) (p 2579) (p 2972) (p 3347) (p 3954) (p 3956) (p 4347) (p 4450) (p 5216) (derived40810 p h) (h 24426)

theorem derived51360 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3005) ∨ (¬ p 3256) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 4026) ∨ (¬ p 4604) ∨ (¬ p 5216) :=
  ElevenRUP.step51360 (p 2027) (p 2696) (p 2753) (p 3005) (p 3256) (p 3379) (p 3591) (p 4026) (p 4604) (p 5216) (derived40810 p h) (h 24431)

theorem derived51361 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2493) ∨ (¬ p 2579) ∨ (¬ p 2928) ∨ (¬ p 3921) ∨ (¬ p 4108) :=
  ElevenRUP.step51361 (p 1984) (p 2027) (p 2299) (p 2493) (p 2579) (p 2633) (p 2928) (p 3921) (p 4108) (h 2144) (derived40810 p h) (derived40879 p h) (h 24432)

theorem derived51362 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3323) ∨ (¬ p 3553) ∨ (¬ p 4067) ∨ (¬ p 4624) :=
  ElevenRUP.step51362 (p 2027) (p 2177) (p 3323) (p 3553) (p 4067) (p 4624) (derived40810 p h) (h 24433)

theorem derived51364 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2946) ∨ (¬ p 3156) ∨ (¬ p 3969) ∨ (¬ p 4117) ∨ (¬ p 4137) ∨ (¬ p 4191) ∨ (¬ p 4729) ∨ (¬ p 5119) :=
  ElevenRUP.step51364 (p 2027) (p 2579) (p 2946) (p 3156) (p 3969) (p 4117) (p 4137) (p 4191) (p 4729) (p 5119) (derived40810 p h) (h 24435)

theorem derived51365 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2630) ∨ (¬ p 3551) ∨ (¬ p 3572) ∨ (¬ p 4155) :=
  ElevenRUP.step51365 (p 1994) (p 2027) (p 2177) (p 2630) (p 2997) (p 3551) (p 3572) (p 4155) (h 2154) (derived40810 p h) (derived40890 p h) (h 24436)

theorem derived51367 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2619) ∨ (¬ p 2753) ∨ (¬ p 3146) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4286) ∨ (¬ p 4370) ∨ (¬ p 5118) ∨ (¬ p 5216) :=
  ElevenRUP.step51367 (p 2027) (p 2132) (p 2619) (p 2753) (p 3146) (p 3379) (p 3860) (p 4286) (p 4370) (p 5118) (p 5216) (derived40810 p h) (h 24438)

theorem derived51368 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 3369) ∨ (¬ p 3371) ∨ (¬ p 3379) ∨ (¬ p 4120) ∨ (¬ p 5216) :=
  ElevenRUP.step51368 (p 2027) (p 2166) (p 3369) (p 3371) (p 3379) (p 4120) (p 5216) (derived40810 p h) (h 24439)

theorem derived51370 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2459) ∨ (¬ p 2753) ∨ (¬ p 2807) ∨ (¬ p 3379) ∨ (¬ p 3591) ∨ (¬ p 4026) ∨ (¬ p 4117) ∨ (¬ p 4604) ∨ (¬ p 5216) :=
  ElevenRUP.step51370 (p 2027) (p 2264) (p 2459) (p 2753) (p 2807) (p 3379) (p 3591) (p 4026) (p 4117) (p 4604) (p 5216) (derived40810 p h) (h 24441)

theorem derived51373 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2440) ∨ (¬ p 2922) ∨ (¬ p 3540) ∨ (¬ p 4814) :=
  ElevenRUP.step51373 (p 2027) (p 2230) (p 2440) (p 2922) (p 3540) (p 4814) (derived40810 p h) (h 24444)

theorem derived51374 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2449) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3555) ∨ (¬ p 3744) ∨ (¬ p 4173) ∨ (¬ p 4625) ∨ (¬ p 4733) :=
  ElevenRUP.step51374 (p 2027) (p 2449) (p 2685) (p 2696) (p 3555) (p 3744) (p 4173) (p 4625) (p 4733) (derived40810 p h) (h 24445)

theorem derived51378 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3097) ∨ (¬ p 3591) ∨ (¬ p 3830) ∨ (¬ p 3957) ∨ (¬ p 4624) ∨ (¬ p 5152) :=
  ElevenRUP.step51378 (p 2027) (p 3097) (p 3591) (p 3830) (p 3957) (p 4624) (p 5152) (derived40810 p h) (h 24449)

theorem derived51379 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2753) ∨ (¬ p 3193) ∨ (¬ p 3434) ∨ (¬ p 3461) ∨ (¬ p 3659) ∨ (¬ p 3819) ∨ (¬ p 4425) ∨ (¬ p 4625) ∨ (¬ p 5216) :=
  ElevenRUP.step51379 (p 2027) (p 2341) (p 2753) (p 3193) (p 3434) (p 3461) (p 3659) (p 3819) (p 4425) (p 4625) (p 5216) (derived40810 p h) (h 24451)

theorem derived51380 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2588) ∨ (¬ p 2717) ∨ (¬ p 3452) ∨ (¬ p 3471) ∨ (¬ p 3570) ∨ (¬ p 4556) ∨ (¬ p 4733) :=
  ElevenRUP.step51380 (p 2027) (p 2499) (p 2588) (p 2717) (p 3452) (p 3471) (p 3570) (p 4556) (p 4733) (derived40810 p h) (h 24453)

theorem derived51382 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2630) ∨ (p 2957) ∨ (¬ p 3758) ∨ (¬ p 4392) ∨ (¬ p 4701) :=
  ElevenRUP.step51382 (p 2027) (p 2156) (p 2630) (p 2957) (p 3758) (p 4392) (p 4701) (derived40810 p h) (h 24455)

theorem derived51383 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2780) ∨ (¬ p 3969) ∨ (¬ p 4347) ∨ (¬ p 4358) ∨ (¬ p 4736) ∨ (¬ p 5122) :=
  ElevenRUP.step51383 (p 2027) (p 2166) (p 2210) (p 2780) (p 3969) (p 4347) (p 4358) (p 4736) (p 5122) (derived40810 p h) (h 24456)

theorem derived51384 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2608) ∨ (¬ p 2839) ∨ (¬ p 3105) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 4450) ∨ (¬ p 5193) :=
  ElevenRUP.step51384 (p 2027) (p 2579) (p 2608) (p 2839) (p 3105) (p 3956) (p 4347) (p 4450) (p 5193) (derived40810 p h) (h 24458)

theorem derived51392 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2518) ∨ (¬ p 3379) ∨ (¬ p 4149) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 4736) ∨ (¬ p 5119) :=
  ElevenRUP.step51392 (p 2027) (p 2138) (p 2518) (p 3379) (p 4149) (p 4322) (p 4385) (p 4736) (p 5119) (derived40810 p h) (h 24472)

theorem derived51399 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2928) ∨ (¬ p 2972) ∨ (¬ p 3948) ∨ (¬ p 4644) ∨ (¬ p 4948) :=
  ElevenRUP.step51399 (p 2027) (p 2928) (p 2972) (p 3948) (p 4644) (p 4948) (derived40810 p h) (h 24483)

theorem derived51406 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2579) ∨ (¬ p 2588) ∨ (¬ p 2641) ∨ (¬ p 2946) ∨ (¬ p 3662) ∨ (¬ p 4107) ∨ (¬ p 4381) ∨ (¬ p 5193) :=
  ElevenRUP.step51406 (p 1980) (p 2027) (p 2253) (p 2579) (p 2588) (p 2641) (p 2764) (p 2946) (p 3662) (p 4107) (p 4381) (p 5193) (h 2140) (derived40810 p h) (derived40882 p h) (h 24492)

theorem derived51407 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2579) ∨ (¬ p 2696) ∨ (¬ p 3434) ∨ (¬ p 3589) ∨ (¬ p 3947) ∨ (¬ p 3956) ∨ (¬ p 4347) ∨ (¬ p 4781) ∨ (¬ p 5193) :=
  ElevenRUP.step51407 (p 1998) (p 2027) (p 2264) (p 2579) (p 2696) (p 2766) (p 3434) (p 3589) (p 3947) (p 3956) (p 4347) (p 4781) (p 5193) (h 2158) (derived40810 p h) (derived40884 p h) (h 24493)

theorem derived51409 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2589) ∨ (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 3880) ∨ (¬ p 5123) ∨ (¬ p 5193) ∨ (¬ p 5568) :=
  ElevenRUP.step51409 (p 2027) (p 2241) (p 2589) (p 3506) (p 3842) (p 3880) (p 5123) (p 5193) (p 5568) (derived40810 p h) (h 24495)

theorem derived51410 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3097) ∨ (¬ p 3941) ∨ (¬ p 4110) ∨ (¬ p 5193) :=
  ElevenRUP.step51410 (p 2020) (p 2027) (p 2241) (p 2264) (p 2589) (p 2997) (p 3027) (p 3097) (p 3941) (p 4110) (p 5193) (h 2180) (derived40810 p h) (derived40890 p h) (h 24496)

theorem derived51411 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2449) ∨ (¬ p 2589) ∨ (¬ p 3027) ∨ (¬ p 3692) ∨ (¬ p 3880) ∨ (¬ p 3950) ∨ (¬ p 5193) :=
  ElevenRUP.step51411 (p 2027) (p 2241) (p 2449) (p 2589) (p 3027) (p 3692) (p 3880) (p 3950) (p 5193) (derived40810 p h) (h 24497)

theorem derived51412 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2255) ∨ (¬ p 2579) ∨ (¬ p 2662) ∨ (¬ p 3286) ∨ (¬ p 3707) ∨ (¬ p 3847) ∨ (¬ p 4111) ∨ (¬ p 4137) ∨ (¬ p 4381) ∨ (¬ p 4625) :=
  ElevenRUP.step51412 (p 2027) (p 2255) (p 2579) (p 2662) (p 3286) (p 3707) (p 3847) (p 4111) (p 4137) (p 4381) (p 4625) (derived40810 p h) (h 24498)

theorem derived51415 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2992) ∨ (¬ p 3742) ∨ (¬ p 4111) ∨ (¬ p 4241) ∨ (¬ p 4644) :=
  ElevenRUP.step51415 (p 2027) (p 2992) (p 3742) (p 4111) (p 4241) (p 4644) (derived40810 p h) (h 24501)

theorem derived51416 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2437) ∨ (¬ p 2727) ∨ (¬ p 2911) :=
  ElevenRUP.step51416 (p 1998) (p 2027) (p 2241) (p 2437) (p 2699) (p 2727) (p 2911) (h 2158) (derived40810 p h) (derived40881 p h) (h 24503)

theorem derived51417 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 3422) ∨ (¬ p 3876) ∨ (¬ p 3921) ∨ (¬ p 4107) :=
  ElevenRUP.step51417 (p 2000) (p 2027) (p 2462) (p 2579) (p 3422) (p 3876) (p 3921) (p 4107) (h 2160) (derived40810 p h) (derived40875 p h) (h 24505)

theorem derived51421 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2960) ∨ (¬ p 3516) ∨ (¬ p 3690) ∨ (¬ p 3952) ∨ (¬ p 4204) ∨ (¬ p 4988) :=
  ElevenRUP.step51421 (p 2027) (p 2960) (p 3516) (p 3690) (p 3952) (p 4204) (p 4988) (derived40810 p h) (h 24512)

theorem derived51423 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2839) ∨ (¬ p 3585) ∨ (¬ p 3695) ∨ (¬ p 4949) ∨ (¬ p 5160) :=
  ElevenRUP.step51423 (p 2027) (p 2839) (p 3585) (p 3695) (p 4949) (p 5160) (derived40810 p h) (h 24514)

theorem derived51424 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2241) ∨ (¬ p 2264) ∨ (¬ p 3027) ∨ (¬ p 3744) ∨ (¬ p 3758) ∨ (¬ p 4191) ∨ (¬ p 4736) :=
  ElevenRUP.step51424 (p 1998) (p 2027) (p 2138) (p 2241) (p 2264) (p 2764) (p 3027) (p 3744) (p 3758) (p 4191) (p 4736) (h 2158) (derived40810 p h) (derived40882 p h) (h 24516)

theorem derived51425 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 2829) ∨ (¬ p 3452) ∨ (¬ p 3590) ∨ (¬ p 5224) :=
  ElevenRUP.step51425 (p 2027) (p 2608) (p 2829) (p 3452) (p 3590) (p 5224) (derived40810 p h) (h 24517)

theorem derived51429 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3548) ∨ (¬ p 3707) ∨ (¬ p 4668) ∨ (¬ p 5233) ∨ (¬ p 5363) ∨ (¬ p 5387) :=
  ElevenRUP.step51429 (p 2027) (p 3548) (p 3707) (p 4668) (p 5233) (p 5363) (p 5387) (derived40810 p h) (h 24521)

theorem derived51430 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 3506) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 3842) ∨ (¬ p 5123) ∨ (¬ p 5193) ∨ (¬ p 5558) :=
  ElevenRUP.step51430 (p 2027) (p 2241) (p 3506) (p 3540) (p 3644) (p 3842) (p 5123) (p 5193) (p 5558) (derived40810 p h) (h 24522)

theorem derived51431 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3537) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4019) ∨ (¬ p 4348) ∨ (¬ p 5122) ∨ (¬ p 5193) :=
  ElevenRUP.step51431 (p 2027) (p 2608) (p 3537) (p 3540) (p 3644) (p 4019) (p 4348) (p 5122) (p 5193) (derived40810 p h) (h 24523)

theorem derived51432 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2630) ∨ (¬ p 2641) ∨ (¬ p 3540) ∨ (¬ p 3644) ∨ (¬ p 4195) ∨ (¬ p 4348) ∨ (¬ p 5193) :=
  ElevenRUP.step51432 (p 1994) (p 2027) (p 2241) (p 2630) (p 2641) (p 2766) (p 3540) (p 3644) (p 4195) (p 4348) (p 5193) (h 2154) (derived40810 p h) (derived40884 p h) (h 24524)

theorem derived51436 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 3093) ∨ (¬ p 3309) ∨ (¬ p 3791) ∨ (¬ p 4385) ∨ (¬ p 4425) ∨ (¬ p 4736) ∨ (¬ p 4826) ∨ (¬ p 4952) :=
  ElevenRUP.step51436 (p 2027) (p 2138) (p 3093) (p 3309) (p 3791) (p 4385) (p 4425) (p 4736) (p 4826) (p 4952) (derived40810 p h) (h 24528)

theorem derived51437 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2459) ∨ (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 3347) ∨ (¬ p 3954) ∨ (¬ p 4902) ∨ (¬ p 5216) :=
  ElevenRUP.step51437 (p 2027) (p 2166) (p 2210) (p 2459) (p 2476) (p 2534) (p 3347) (p 3954) (p 4902) (p 5216) (derived40810 p h) (h 24529)

theorem derived51439 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 2608) ∨ (¬ p 2737) ∨ (¬ p 3005) ∨ (¬ p 3570) ∨ (¬ p 4235) ∨ (¬ p 4550) ∨ (¬ p 5193) :=
  ElevenRUP.step51439 (p 2027) (p 2589) (p 2608) (p 2737) (p 3005) (p 3570) (p 4235) (p 4550) (p 5193) (derived40810 p h) (h 24531)

theorem derived51440 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2373) ∨ (¬ p 2590) ∨ (¬ p 2870) ∨ (¬ p 3096) ∨ (¬ p 3694) ∨ (¬ p 4558) :=
  ElevenRUP.step51440 (p 2027) (p 2373) (p 2590) (p 2870) (p 3096) (p 3694) (p 4558) (derived40810 p h) (h 24533)

theorem derived51441 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3051) ∨ (¬ p 3646) ∨ (¬ p 4244) ∨ (¬ p 4882) :=
  ElevenRUP.step51441 (p 2027) (p 2563) (p 3051) (p 3646) (p 4244) (p 4882) (derived40810 p h) (h 24534)

theorem derived51442 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2630) ∨ (¬ p 2641) ∨ (¬ p 3540) ∨ (¬ p 4195) ∨ (¬ p 4278) ∨ (¬ p 4381) ∨ (¬ p 5193) :=
  ElevenRUP.step51442 (p 1994) (p 2027) (p 2241) (p 2630) (p 2641) (p 2764) (p 3540) (p 4195) (p 4278) (p 4381) (p 5193) (h 2154) (derived40810 p h) (derived40882 p h) (h 24535)

theorem derived51443 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3570) ∨ (¬ p 4235) ∨ (¬ p 4348) :=
  ElevenRUP.step51443 (p 1994) (p 2027) (p 2440) (p 2766) (p 3570) (p 4235) (p 4348) (h 2154) (derived40810 p h) (derived40884 p h) (h 24536)

theorem derived51444 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2417) ∨ (¬ p 3922) ∨ (¬ p 4026) ∨ (¬ p 4396) ∨ (¬ p 4712) :=
  ElevenRUP.step51444 (p 2027) (p 2295) (p 2417) (p 3922) (p 4026) (p 4396) (p 4712) (derived40810 p h) (h 24537)

theorem derived51446 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 3564) ∨ (¬ p 4032) ∨ (¬ p 4033) ∨ (¬ p 4718) :=
  ElevenRUP.step51446 (p 2027) (p 2156) (p 3564) (p 4032) (p 4033) (p 4718) (derived40810 p h) (h 24539)

theorem derived51447 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2210) ∨ (¬ p 2534) ∨ (¬ p 3055) ∨ (¬ p 3125) ∨ (¬ p 3874) ∨ (¬ p 4330) ∨ (¬ p 4736) :=
  ElevenRUP.step51447 (p 2027) (p 2192) (p 2210) (p 2534) (p 3055) (p 3125) (p 3874) (p 4330) (p 4736) (derived40810 p h) (h 24541)

theorem derived51448 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) ∨ (¬ p 3363) ∨ (¬ p 3551) ∨ (¬ p 3585) ∨ (¬ p 4278) ∨ (¬ p 5197) :=
  ElevenRUP.step51448 (p 1992) (p 2027) (p 2462) (p 2911) (p 3363) (p 3551) (p 3585) (p 4278) (p 5197) (h 2152) (derived40810 p h) (derived40875 p h) (h 24542)

theorem derived51449 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 3471) ∨ (¬ p 4733) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step51449 (p 2027) (p 2459) (p 2717) (p 3238) (p 3452) (p 3471) (p 4733) (p 4948) (p 5059) (derived40810 p h) (h 24543)

theorem derived51450 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2248) ∨ (¬ p 2331) ∨ (¬ p 3688) ∨ (¬ p 3954) ∨ (¬ p 4337) :=
  ElevenRUP.step51450 (p 2027) (p 2248) (p 2331) (p 3688) (p 3954) (p 4337) (derived40810 p h) (h 24544)

theorem derived51452 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2396) ∨ (¬ p 2761) ∨ (¬ p 2774) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 4733) ∨ (¬ p 4948) :=
  ElevenRUP.step51452 (p 1988) (p 2027) (p 2122) (p 2396) (p 2761) (p 2774) (p 3043) (p 3238) (p 3452) (p 4733) (p 4948) (h 2148) (derived40810 p h) (derived40893 p h) (h 24546)

theorem derived51453 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2748) ∨ (¬ p 2779) ∨ (¬ p 2829) ∨ (¬ p 3365) ∨ (¬ p 3497) ∨ (¬ p 3662) ∨ (¬ p 4114) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4734) :=
  ElevenRUP.step51453 (p 2027) (p 2088) (p 2748) (p 2779) (p 2829) (p 3365) (p 3497) (p 3662) (p 4114) (p 4134) (p 4347) (p 4734) (derived40810 p h) (h 24549)

theorem derived51457 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (¬ p 3292) ∨ (¬ p 3755) ∨ (¬ p 4315) ∨ (¬ p 4701) :=
  ElevenRUP.step51457 (p 2027) (p 2651) (p 3292) (p 3755) (p 4315) (p 4701) (derived40810 p h) (h 24555)

theorem derived51458 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2246) ∨ (¬ p 2331) ∨ (¬ p 2749) ∨ (¬ p 3256) ∨ (¬ p 3379) ∨ (¬ p 3555) ∨ (¬ p 4134) ∨ (¬ p 4341) ∨ (¬ p 4347) ∨ (¬ p 5216) :=
  ElevenRUP.step51458 (p 2027) (p 2191) (p 2246) (p 2331) (p 2749) (p 3256) (p 3379) (p 3555) (p 4134) (p 4341) (p 4347) (p 5216) (derived40810 p h) (h 24558)

theorem derived51460 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2177) ∨ (¬ p 2774) ∨ (¬ p 2928) ∨ (¬ p 3452) ∨ (¬ p 4278) ∨ (¬ p 4666) ∨ (¬ p 4733) :=
  ElevenRUP.step51460 (p 2027) (p 2122) (p 2177) (p 2774) (p 2928) (p 3452) (p 4278) (p 4666) (p 4733) (derived40810 p h) (h 24560)

theorem derived51463 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2139) ∨ (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2476) ∨ (¬ p 3791) ∨ (¬ p 3905) ∨ (¬ p 4340) ∨ (¬ p 4444) ∨ (¬ p 4826) ∨ (¬ p 5373) :=
  ElevenRUP.step51463 (p 2027) (p 2139) (p 2156) (p 2274) (p 2476) (p 3791) (p 3905) (p 4340) (p 4444) (p 4826) (p 5373) (derived40810 p h) (h 24566)

theorem derived51466 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2797) ∨ (¬ p 3877) ∨ (¬ p 4584) ∨ (¬ p 4769) :=
  ElevenRUP.step51466 (p 2027) (p 2383) (p 2797) (p 3877) (p 4584) (p 4769) (derived40810 p h) (h 24569)

theorem derived51467 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2717) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3471) ∨ (¬ p 3860) ∨ (¬ p 5118) ∨ (¬ p 5216) ∨ (¬ p 5693) :=
  ElevenRUP.step51467 (p 2027) (p 2459) (p 2717) (p 2753) (p 3379) (p 3471) (p 3860) (p 5118) (p 5216) (p 5693) (derived40810 p h) (h 24570)

theorem derived51468 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2749) ∨ (¬ p 3073) ∨ (¬ p 3379) ∨ (¬ p 3857) ∨ (¬ p 3859) ∨ (¬ p 4416) ∨ (¬ p 5216) :=
  ElevenRUP.step51468 (p 2027) (p 2749) (p 3073) (p 3379) (p 3857) (p 3859) (p 4416) (p 5216) (derived40810 p h) (h 24571)

theorem derived51469 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3136) ∨ (¬ p 3379) ∨ (¬ p 3564) ∨ (¬ p 3834) ∨ (¬ p 3956) ∨ (¬ p 5148) ∨ (¬ p 5216) :=
  ElevenRUP.step51469 (p 1990) (p 2027) (p 2169) (p 2284) (p 2696) (p 2753) (p 3136) (p 3379) (p 3564) (p 3834) (p 3956) (p 5148) (p 5216) (h 2150) (derived40810 p h) (derived40866 p h) (h 24572)

theorem derived51470 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2166) ∨ (¬ p 2210) ∨ (¬ p 2498) ∨ (¬ p 3096) ∨ (¬ p 3591) ∨ (¬ p 4509) :=
  ElevenRUP.step51470 (p 2027) (p 2166) (p 2210) (p 2498) (p 3096) (p 3591) (p 4509) (derived40810 p h) (h 24573)

theorem derived51471 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 2753) ∨ (¬ p 3379) ∨ (¬ p 3471) ∨ (¬ p 3860) ∨ (¬ p 3979) ∨ (¬ p 4138) ∨ (¬ p 4261) ∨ (¬ p 5122) ∨ (¬ p 5216) :=
  ElevenRUP.step51471 (p 2027) (p 2717) (p 2753) (p 3379) (p 3471) (p 3860) (p 3979) (p 4138) (p 4261) (p 5122) (p 5216) (derived40810 p h) (h 24574)

theorem derived51473 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3860) ∨ (¬ p 4261) ∨ (¬ p 4330) ∨ (¬ p 4877) :=
  ElevenRUP.step51473 (p 2027) (p 2210) (p 2696) (p 2753) (p 2797) (p 3323) (p 3860) (p 4261) (p 4330) (p 4877) (derived40810 p h) (h 24576)

theorem derived51475 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2927) ∨ (¬ p 3222) ∨ (¬ p 3379) ∨ (¬ p 4366) ∨ (¬ p 4640) :=
  ElevenRUP.step51475 (p 2027) (p 2927) (p 3222) (p 3379) (p 4366) (p 4640) (derived40810 p h) (h 24578)

theorem derived51476 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 2753) ∨ (¬ p 3834) ∨ (¬ p 3931) ∨ (¬ p 4321) ∨ (¬ p 4826) ∨ (¬ p 4877) :=
  ElevenRUP.step51476 (p 2027) (p 2210) (p 2685) (p 2696) (p 2753) (p 3834) (p 3931) (p 4321) (p 4826) (p 4877) (derived40810 p h) (h 24579)

theorem derived51481 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2476) ∨ (¬ p 2534) ∨ (¬ p 2685) ∨ (¬ p 2696) ∨ (¬ p 3931) ∨ (¬ p 4444) ∨ (¬ p 4729) ∨ (¬ p 4826) :=
  ElevenRUP.step51481 (p 2027) (p 2476) (p 2534) (p 2685) (p 2696) (p 3931) (p 4444) (p 4729) (p 4826) (derived40810 p h) (h 24584)

theorem derived51482 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3516) ∨ (¬ p 4066) ∨ (¬ p 4360) ∨ (¬ p 4548) ∨ (¬ p 4668) :=
  ElevenRUP.step51482 (p 2027) (p 3027) (p 3516) (p 4066) (p 4360) (p 4548) (p 4668) (derived40810 p h) (h 24585)

theorem derived51484 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 3027) ∨ (¬ p 3552) ∨ (¬ p 4154) ∨ (¬ p 4976) :=
  ElevenRUP.step51484 (p 2027) (p 2588) (p 3027) (p 3552) (p 4154) (p 4976) (derived40810 p h) (h 24587)

theorem derived51485 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2187) ∨ (¬ p 2459) ∨ (¬ p 2860) ∨ (¬ p 3860) ∨ (¬ p 4133) ∨ (¬ p 4261) ∨ (¬ p 4733) :=
  ElevenRUP.step51485 (p 2027) (p 2132) (p 2187) (p 2459) (p 2860) (p 3860) (p 4133) (p 4261) (p 4733) (derived40810 p h) (h 24588)

theorem derived51486 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2499) ∨ (¬ p 3055) ∨ (¬ p 3695) ∨ (¬ p 4030) ∨ (¬ p 4715) :=
  ElevenRUP.step51486 (p 2027) (p 2132) (p 2499) (p 3055) (p 3695) (p 4030) (p 4715) (derived40810 p h) (h 24589)

theorem derived51487 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2331) ∨ (¬ p 2668) ∨ (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4244) ∨ (¬ p 4734) :=
  ElevenRUP.step51487 (p 2027) (p 2138) (p 2331) (p 2668) (p 2737) (p 2811) (p 3570) (p 4133) (p 4244) (p 4734) (derived40810 p h) (h 24591)

theorem derived51489 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2598) ∨ (¬ p 2753) ∨ (¬ p 3422) ∨ (¬ p 3564) ∨ (¬ p 3690) ∨ (¬ p 4366) ∨ (¬ p 4621) ∨ (¬ p 4877) ∨ (¬ p 4909) :=
  ElevenRUP.step51489 (p 2027) (p 2210) (p 2598) (p 2753) (p 3422) (p 3564) (p 3690) (p 4366) (p 4621) (p 4877) (p 4909) (derived40810 p h) (h 24593)

theorem derived51491 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 3556) ∨ (¬ p 3690) ∨ (¬ p 3741) ∨ (¬ p 4533) :=
  ElevenRUP.step51491 (p 2027) (p 2417) (p 3556) (p 3690) (p 3741) (p 4533) (derived40810 p h) (h 24595)

theorem derived51492 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2780) ∨ (¬ p 3471) ∨ (¬ p 4358) ∨ (¬ p 4475) ∨ (¬ p 4501) :=
  ElevenRUP.step51492 (p 2027) (p 2780) (p 3471) (p 4358) (p 4475) (p 4501) (derived40810 p h) (h 24598)

theorem derived51494 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2870) ∨ (¬ p 2996) ∨ (¬ p 3246) ∨ (¬ p 3553) ∨ (¬ p 4668) ∨ (¬ p 4733) :=
  ElevenRUP.step51494 (p 2027) (p 2132) (p 2247) (p 2870) (p 2996) (p 3246) (p 3553) (p 4668) (p 4733) (derived40810 p h) (h 24600)

theorem derived51495 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2247) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 3609) ∨ (¬ p 4133) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step51495 (p 2027) (p 2098) (p 2247) (p 2996) (p 3553) (p 3609) (p 4133) (p 4347) (p 4733) (derived40810 p h) (h 24602)

theorem derived51496 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2247) ∨ (¬ p 2996) ∨ (¬ p 3146) ∨ (¬ p 3266) ∨ (¬ p 4391) ∨ (¬ p 4521) ∨ (¬ p 4831) :=
  ElevenRUP.step51496 (p 2027) (p 2220) (p 2247) (p 2996) (p 3146) (p 3266) (p 4391) (p 4521) (p 4831) (derived40810 p h) (h 24603)

theorem derived51497 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2563) ∨ (¬ p 3246) ∨ (¬ p 3872) ∨ (¬ p 4107) :=
  ElevenRUP.step51497 (p 1998) (p 2027) (p 2177) (p 2202) (p 2563) (p 3246) (p 3872) (p 4107) (h 2158) (derived40810 p h) (derived40867 p h) (h 24604)

theorem derived51499 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 4733) ∨ (¬ p 4948) ∨ (¬ p 5059) :=
  ElevenRUP.step51499 (p 2027) (p 2363) (p 2774) (p 2819) (p 3238) (p 3452) (p 4733) (p 4948) (p 5059) (derived40810 p h) (h 24606)

theorem derived51506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2187) ∨ (¬ p 2387) ∨ (¬ p 2870) ∨ (¬ p 4198) ∨ (¬ p 4558) :=
  ElevenRUP.step51506 (p 2027) (p 2143) (p 2187) (p 2387) (p 2870) (p 4198) (p 4558) (derived40810 p h) (h 24614)

theorem derived51507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2493) ∨ (¬ p 2542) ∨ (¬ p 3238) ∨ (¬ p 3584) ∨ (¬ p 4750) :=
  ElevenRUP.step51507 (p 2027) (p 2493) (p 2542) (p 3238) (p 3584) (p 4750) (derived40810 p h) (h 24615)

theorem derived51508 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2247) ∨ (¬ p 2996) ∨ (¬ p 3553) ∨ (¬ p 3609) ∨ (¬ p 3692) ∨ (¬ p 4733) ∨ (¬ p 4902) :=
  ElevenRUP.step51508 (p 2027) (p 2098) (p 2247) (p 2996) (p 3553) (p 3609) (p 3692) (p 4733) (p 4902) (derived40810 p h) (h 24616)

theorem derived51509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 3426) ∨ (¬ p 3434) ∨ (¬ p 3821) ∨ (¬ p 3905) ∨ (¬ p 4734) ∨ (¬ p 5197) :=
  ElevenRUP.step51509 (p 2027) (p 2829) (p 3426) (p 3434) (p 3821) (p 3905) (p 4734) (p 5197) (derived40810 p h) (h 24617)

theorem derived51510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2247) ∨ (¬ p 3497) ∨ (¬ p 3609) ∨ (¬ p 3662) ∨ (¬ p 4134) ∨ (¬ p 4347) ∨ (¬ p 4733) :=
  ElevenRUP.step51510 (p 2027) (p 2098) (p 2247) (p 3497) (p 3609) (p 3662) (p 4134) (p 4347) (p 4733) (derived40810 p h) (h 24618)

theorem derived51511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3097) ∨ (¬ p 3552) ∨ (¬ p 4154) ∨ (¬ p 4560) :=
  ElevenRUP.step51511 (p 2027) (p 3027) (p 3097) (p 3552) (p 4154) (p 4560) (derived40810 p h) (h 24619)

theorem derived51513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2590) ∨ (¬ p 3737) ∨ (¬ p 4558) ∨ (¬ p 5514) :=
  ElevenRUP.step51513 (p 2027) (p 2427) (p 2590) (p 3737) (p 4558) (p 5514) (derived40810 p h) (h 24622)

theorem derived51514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 3237) ∨ (¬ p 3680) ∨ (¬ p 4334) ∨ (¬ p 4425) ∨ (¬ p 4558) :=
  ElevenRUP.step51514 (p 2027) (p 2427) (p 3237) (p 3680) (p 4334) (p 4425) (p 4558) (derived40810 p h) (h 24623)

theorem derived51516 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 3550) ∨ (¬ p 3742) ∨ (¬ p 4157) ∨ (¬ p 5503) ∨ (¬ p 5559) :=
  ElevenRUP.step51516 (p 2027) (p 3083) (p 3550) (p 3742) (p 4157) (p 5503) (p 5559) (derived40810 p h) (h 24625)

theorem derived51517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2248) ∨ (¬ p 2427) ∨ (¬ p 2542) ∨ (¬ p 2651) ∨ (¬ p 3537) ∨ (¬ p 3588) ∨ (¬ p 3873) ∨ (¬ p 4898) :=
  ElevenRUP.step51517 (p 2027) (p 2104) (p 2248) (p 2427) (p 2542) (p 2651) (p 3537) (p 3588) (p 3873) (p 4898) (derived40810 p h) (h 24626)

theorem derived51520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2177) ∨ (¬ p 2245) ∨ (¬ p 2274) ∨ (¬ p 2657) ∨ (¬ p 2727) ∨ (¬ p 4041) ∨ (¬ p 4360) ∨ (¬ p 4521) :=
  ElevenRUP.step51520 (p 2027) (p 2156) (p 2177) (p 2245) (p 2274) (p 2657) (p 2727) (p 4041) (p 4360) (p 4521) (derived40810 p h) (h 24630)

theorem derived51521 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3171) ∨ (¬ p 3189) ∨ (¬ p 4113) ∨ (¬ p 4154) ∨ (¬ p 4358) ∨ (¬ p 4843) :=
  ElevenRUP.step51521 (p 2027) (p 3171) (p 3189) (p 4113) (p 4154) (p 4358) (p 4843) (derived40810 p h) (h 24632)

theorem derived51522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 2911) ∨ (¬ p 3548) ∨ (¬ p 4366) ∨ (¬ p 4712) ∨ (¬ p 4733) :=
  ElevenRUP.step51522 (p 2027) (p 2295) (p 2696) (p 2797) (p 2911) (p 3548) (p 4366) (p 4712) (p 4733) (derived40810 p h) (h 24633)

theorem derived51523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2509) ∨ (¬ p 2534) ∨ (¬ p 2696) ∨ (¬ p 2797) ∨ (¬ p 3323) ∨ (¬ p 3452) ∨ (¬ p 4330) ∨ (¬ p 4733) :=
  ElevenRUP.step51523 (p 2027) (p 2509) (p 2534) (p 2696) (p 2797) (p 3323) (p 3452) (p 4330) (p 4733) (derived40810 p h) (h 24634)

theorem derived51526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2656) ∨ (¬ p 2727) ∨ (¬ p 4154) ∨ (¬ p 4389) ∨ (¬ p 4715) :=
  ElevenRUP.step51526 (p 2027) (p 2230) (p 2656) (p 2727) (p 4154) (p 4389) (p 4715) (derived40810 p h) (h 24640)

theorem derived51527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2143) ∨ (¬ p 2499) ∨ (¬ p 2934) ∨ (¬ p 3631) ∨ (¬ p 3695) ∨ (¬ p 3821) ∨ (¬ p 4715) ∨ (¬ p 4984) :=
  ElevenRUP.step51527 (p 2027) (p 2143) (p 2499) (p 2934) (p 3631) (p 3695) (p 3821) (p 4715) (p 4984) (derived40810 p h) (h 24641)

theorem derived51528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (¬ p 2241) ∨ (¬ p 2750) ∨ (¬ p 2753) ∨ (¬ p 2774) ∨ (¬ p 3791) ∨ (¬ p 3834) ∨ (¬ p 4321) ∨ (¬ p 4826) :=
  ElevenRUP.step51528 (p 2027) (p 2122) (p 2241) (p 2750) (p 2753) (p 2774) (p 3791) (p 3834) (p 4321) (p 4826) (derived40810 p h) (h 24644)

theorem derived51529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3550) ∨ (¬ p 4244) ∨ (¬ p 4441) ∨ (¬ p 5559) ∨ (¬ p 5660) :=
  ElevenRUP.step51529 (p 2027) (p 2619) (p 3550) (p 4244) (p 4441) (p 5559) (p 5660) (derived40810 p h) (h 24645)

theorem derived51531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2449) ∨ (¬ p 4026) ∨ (¬ p 4361) ∨ (¬ p 4396) ∨ (¬ p 4516) :=
  ElevenRUP.step51531 (p 2027) (p 2274) (p 2449) (p 4026) (p 4361) (p 4396) (p 4516) (derived40810 p h) (h 24647)

theorem derived51532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2437) ∨ (¬ p 3359) ∨ (¬ p 3950) ∨ (¬ p 4440) :=
  ElevenRUP.step51532 (p 2027) (p 2417) (p 2437) (p 3359) (p 3950) (p 4440) (derived40810 p h) (h 24648)

theorem derived51533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2619) ∨ (¬ p 3051) ∨ (¬ p 3880) ∨ (¬ p 4244) ∨ (¬ p 4539) :=
  ElevenRUP.step51533 (p 2027) (p 2619) (p 3051) (p 3880) (p 4244) (p 4539) (derived40810 p h) (h 24649)

theorem derived51534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3979) ∨ (¬ p 4197) ∨ (¬ p 4581) ∨ (¬ p 5590) :=
  ElevenRUP.step51534 (p 2027) (p 2668) (p 3979) (p 4197) (p 4581) (p 5590) (derived40810 p h) (h 24650)

theorem derived51535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2748) ∨ (¬ p 3585) ∨ (¬ p 3954) ∨ (¬ p 4749) :=
  ElevenRUP.step51535 (p 2027) (p 2241) (p 2748) (p 3585) (p 3954) (p 4749) (derived40810 p h) (h 24651)

theorem derived51537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2104) ∨ (¬ p 2230) ∨ (¬ p 2427) ∨ (¬ p 4129) ∨ (¬ p 4340) ∨ (¬ p 4419) ∨ (¬ p 4444) ∨ (¬ p 4826) :=
  ElevenRUP.step51537 (p 2027) (p 2104) (p 2230) (p 2427) (p 4129) (p 4340) (p 4419) (p 4444) (p 4826) (derived40810 p h) (h 24653)

theorem derived51538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (¬ p 3989) ∨ (¬ p 4195) ∨ (¬ p 4417) ∨ (¬ p 4560) :=
  ElevenRUP.step51538 (p 2027) (p 3005) (p 3989) (p 4195) (p 4417) (p 4560) (derived40810 p h) (h 24654)

theorem derived51539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3568) ∨ (¬ p 3979) ∨ (¬ p 5558) :=
  ElevenRUP.step51539 (p 1998) (p 2027) (p 2668) (p 2997) (p 3568) (p 3979) (p 5558) (h 2158) (derived40810 p h) (derived40890 p h) (h 24655)

theorem derived51541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 3323) ∨ (¬ p 3834) ∨ (¬ p 4024) ∨ (¬ p 4843) ∨ (¬ p 5148) :=
  ElevenRUP.step51541 (p 2027) (p 3093) (p 3323) (p 3834) (p 4024) (p 4843) (p 5148) (derived40810 p h) (h 24657)

theorem derived51542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (¬ p 5117) ∨ (p 5123) :=
  ElevenRUP.step51542 (p 1987) (p 2611) (p 2696) (p 5117) (p 5123) (h 2147) (derived40877 p h) (h 24658)

theorem derived51544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3232) ∨ (¬ p 3452) ∨ (¬ p 3830) ∨ (¬ p 5160) ∨ (¬ p 5217) :=
  ElevenRUP.step51544 (p 2027) (p 3232) (p 3452) (p 3830) (p 5160) (p 5217) (derived40810 p h) (h 24660)

theorem derived51546 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3233) ∨ (¬ p 3707) ∨ (¬ p 4425) ∨ (¬ p 5160) ∨ (¬ p 5217) :=
  ElevenRUP.step51546 (p 2027) (p 3233) (p 3707) (p 4425) (p 5160) (p 5217) (derived40810 p h) (h 24662)

theorem derived51547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2088) ∨ (¬ p 2484) ∨ (¬ p 3641) ∨ (¬ p 4440) ∨ (¬ p 5160) :=
  ElevenRUP.step51547 (p 2027) (p 2088) (p 2484) (p 3641) (p 4440) (p 5160) (derived40810 p h) (h 24663)

theorem derived51548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2870) ∨ (¬ p 2963) ∨ (¬ p 3362) ∨ (¬ p 3698) ∨ (¬ p 4037) ∨ (¬ p 4129) ∨ (¬ p 4191) ∨ (¬ p 4789) ∨ (¬ p 4826) :=
  ElevenRUP.step51548 (p 2027) (p 2230) (p 2870) (p 2963) (p 3362) (p 3698) (p 4037) (p 4129) (p 4191) (p 4789) (p 4826) (derived40810 p h) (h 24664)

theorem derived51550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2761) ∨ (¬ p 3434) ∨ (¬ p 3471) ∨ (¬ p 4154) ∨ (¬ p 4733) ∨ (¬ p 5254) ∨ (¬ p 5717) :=
  ElevenRUP.step51550 (p 2027) (p 2247) (p 2761) (p 3434) (p 3471) (p 4154) (p 4733) (p 5254) (p 5717) (derived40810 p h) (h 24666)

theorem derived51551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (¬ p 2685) ∨ (¬ p 3552) ∨ (¬ p 4195) ∨ (¬ p 4976) :=
  ElevenRUP.step51551 (p 2027) (p 2588) (p 2685) (p 3552) (p 4195) (p 4976) (derived40810 p h) (h 24667)

theorem derived51553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2727) ∨ (¬ p 3016) ∨ (¬ p 4154) ∨ (¬ p 4976) :=
  ElevenRUP.step51553 (p 2027) (p 2727) (p 3016) (p 4154) (p 4976) (derived40810 p h) (h 24669)

theorem derived51554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2598) ∨ (¬ p 3422) ∨ (¬ p 3486) ∨ (¬ p 3555) ∨ (¬ p 3570) ∨ (¬ p 4133) ∨ (¬ p 4733) :=
  ElevenRUP.step51554 (p 2027) (p 2352) (p 2598) (p 3422) (p 3486) (p 3555) (p 3570) (p 4133) (p 4733) (derived40810 p h) (h 24670)

theorem derived51556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2373) ∨ (¬ p 2598) ∨ (¬ p 2850) ∨ (¬ p 3309) ∨ (¬ p 3923) ∨ (¬ p 4433) ∨ (¬ p 4733) ∨ (¬ p 5015) :=
  ElevenRUP.step51556 (p 2027) (p 2313) (p 2373) (p 2598) (p 2850) (p 3309) (p 3923) (p 4433) (p 4733) (p 5015) (derived40810 p h) (h 24672)

theorem derived51557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2299) ∨ (¬ p 2528) ∨ (¬ p 3549) ∨ (¬ p 3591) ∨ (¬ p 3692) ∨ (¬ p 4355) ∨ (¬ p 4902) ∨ (¬ p 5190) :=
  ElevenRUP.step51557 (p 2027) (p 2230) (p 2299) (p 2528) (p 3549) (p 3591) (p 3692) (p 4355) (p 4902) (p 5190) (derived40810 p h) (h 24673)

theorem derived51558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2668) ∨ (¬ p 3692) ∨ (¬ p 3988) ∨ (¬ p 4560) :=
  ElevenRUP.step51558 (p 2027) (p 2363) (p 2668) (p 3692) (p 3988) (p 4560) (derived40810 p h) (h 24674)

theorem derived51559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2417) ∨ (¬ p 2598) ∨ (¬ p 3201) ∨ (¬ p 3555) ∨ (¬ p 3744) ∨ (¬ p 4173) ∨ (¬ p 4625) ∨ (¬ p 4733) :=
  ElevenRUP.step51559 (p 2027) (p 2417) (p 2598) (p 3201) (p 3555) (p 3744) (p 4173) (p 4625) (p 4733) (derived40810 p h) (h 24675)

theorem derived51560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3568) ∨ (¬ p 4111) ∨ (¬ p 4759) ∨ (¬ p 4975) :=
  ElevenRUP.step51560 (p 2027) (p 3309) (p 3568) (p 4111) (p 4759) (p 4975) (derived40810 p h) (h 24676)

theorem derived51562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2819) ∨ (¬ p 3555) ∨ (¬ p 3979) ∨ (¬ p 4322) ∨ (¬ p 4363) ∨ (¬ p 4733) ∨ (¬ p 5119) :=
  ElevenRUP.step51562 (p 2027) (p 2774) (p 2819) (p 3555) (p 3979) (p 4322) (p 4363) (p 4733) (p 5119) (derived40810 p h) (h 24678)

theorem derived51563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2528) ∨ (¬ p 2598) ∨ (¬ p 3555) ∨ (¬ p 3641) ∨ (¬ p 4733) ∨ (¬ p 5118) ∨ (¬ p 5568) :=
  ElevenRUP.step51563 (p 2027) (p 2191) (p 2528) (p 2598) (p 3555) (p 3641) (p 4733) (p 5118) (p 5568) (derived40810 p h) (h 24679)

theorem derived51565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2299) ∨ (¬ p 2717) ∨ (¬ p 3471) ∨ (¬ p 3662) ∨ (¬ p 4320) ∨ (¬ p 4559) ∨ (¬ p 4733) :=
  ElevenRUP.step51565 (p 2027) (p 2247) (p 2299) (p 2717) (p 3471) (p 3662) (p 4320) (p 4559) (p 4733) (derived40810 p h) (h 24681)

theorem derived51566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2245) ∨ (¬ p 2299) ∨ (¬ p 2717) ∨ (¬ p 2952) ∨ (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3471) ∨ (¬ p 4361) ∨ (¬ p 4733) :=
  ElevenRUP.step51566 (p 2027) (p 2245) (p 2299) (p 2717) (p 2952) (p 2992) (p 2996) (p 3471) (p 4361) (p 4733) (derived40810 p h) (h 24682)

theorem derived51567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 2881) ∨ (¬ p 3201) ∨ (¬ p 3362) ∨ (¬ p 3548) ∨ (¬ p 3584) ∨ (¬ p 4277) ∨ (¬ p 4366) ∨ (¬ p 4733) :=
  ElevenRUP.step51567 (p 2027) (p 2573) (p 2881) (p 3201) (p 3362) (p 3548) (p 3584) (p 4277) (p 4366) (p 4733) (derived40810 p h) (h 24683)

theorem derived51569 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3583) ∨ (¬ p 3952) ∨ (¬ p 4316) ∨ (¬ p 4344) ∨ (¬ p 4558) :=
  ElevenRUP.step51569 (p 2027) (p 2707) (p 3583) (p 3952) (p 4316) (p 4344) (p 4558) (derived40810 p h) (h 24687)

theorem derived51570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3584) ∨ (p 5225) :=
  ElevenRUP.step51570 (p 1986) (p 3584) (p 3586) (p 5225) (h 2146) (derived40901 p h) (h 24688)

theorem derived51571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 3422) ∨ (¬ p 3876) ∨ (¬ p 3921) ∨ (¬ p 4976) :=
  ElevenRUP.step51571 (p 2027) (p 2295) (p 3422) (p 3876) (p 3921) (p 4976) (derived40810 p h) (h 24689)

theorem derived51572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2761) ∨ (¬ p 3471) ∨ (¬ p 3516) ∨ (¬ p 3591) ∨ (¬ p 3737) ∨ (¬ p 3744) ∨ (¬ p 4066) ∨ (¬ p 4325) ∨ (¬ p 4435) ∨ (¬ p 4733) :=
  ElevenRUP.step51572 (p 1988) (p 2027) (p 2761) (p 3128) (p 3471) (p 3516) (p 3591) (p 3737) (p 3744) (p 4066) (p 4325) (p 4435) (p 4733) (h 2148) (derived40810 p h) (derived40894 p h) (h 24690)

theorem derived51575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2619) ∨ (¬ p 3949) ∨ (¬ p 4385) ∨ (¬ p 4902) :=
  ElevenRUP.step51575 (p 2027) (p 2459) (p 2619) (p 3949) (p 4385) (p 4902) (derived40810 p h) (h 24695)

theorem derived51576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 3946) ∨ (p 4330) :=
  ElevenRUP.step51576 (p 2003) (p 2169) (p 2363) (p 3946) (p 4330) (h 2163) (derived40866 p h) (h 24696)

theorem derived51578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2952) ∨ (¬ p 3201) ∨ (¬ p 3868) ∨ (¬ p 4208) ∨ (¬ p 4322) ∨ (¬ p 4789) ∨ (¬ p 4826) :=
  ElevenRUP.step51578 (p 2027) (p 2598) (p 2952) (p 3201) (p 3868) (p 4208) (p 4322) (p 4789) (p 4826) (derived40810 p h) (h 24698)

theorem derived51579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3641) ∨ (¬ p 3876) ∨ (¬ p 4404) ∨ (¬ p 5503) ∨ (¬ p 5559) :=
  ElevenRUP.step51579 (p 2027) (p 3641) (p 3876) (p 4404) (p 5503) (p 5559) (derived40810 p h) (h 24699)

theorem derived51580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2504) ∨ (¬ p 3093) ∨ (¬ p 3452) ∨ (¬ p 3584) ∨ (¬ p 5217) :=
  ElevenRUP.step51580 (p 2027) (p 2504) (p 3093) (p 3452) (p 3584) (p 5217) (derived40810 p h) (h 24700)

theorem derived51581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2191) ∨ (¬ p 2220) ∨ (¬ p 3954) ∨ (¬ p 4172) ∨ (¬ p 4877) :=
  ElevenRUP.step51581 (p 2027) (p 2191) (p 2220) (p 3954) (p 4172) (p 4877) (derived40810 p h) (h 24701)

theorem derived51582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 3449) ∨ (¬ p 4366) ∨ (¬ p 4391) ∨ (¬ p 5307) ∨ (¬ p 5559) :=
  ElevenRUP.step51582 (p 2027) (p 3032) (p 3449) (p 4366) (p 4391) (p 5307) (p 5559) (derived40810 p h) (h 24702)

theorem derived51583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2911) ∨ (¬ p 3201) ∨ (¬ p 4636) ∨ (¬ p 5160) :=
  ElevenRUP.step51583 (p 1998) (p 2027) (p 2396) (p 2911) (p 2997) (p 3201) (p 4636) (p 5160) (h 2158) (derived40810 p h) (derived40890 p h) (h 24703)

theorem derived51584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2138) ∨ (¬ p 2553) ∨ (¬ p 2573) ∨ (¬ p 3791) ∨ (¬ p 4322) ∨ (¬ p 4385) ∨ (¬ p 4419) ∨ (¬ p 4826) :=
  ElevenRUP.step51584 (p 2027) (p 2138) (p 2553) (p 2573) (p 3791) (p 4322) (p 4385) (p 4419) (p 4826) (derived40810 p h) (h 24704)

theorem derived51586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2995) ∨ (¬ p 3551) ∨ (¬ p 3952) ∨ (¬ p 4283) ∨ (¬ p 4558) :=
  ElevenRUP.step51586 (p 2027) (p 2264) (p 2995) (p 3551) (p 3952) (p 4283) (p 4558) (derived40810 p h) (h 24706)

theorem derived51587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 3172) ∨ (p 4771) :=
  ElevenRUP.step51587 (p 1991) (p 2287) (p 2668) (p 3172) (p 4771) (h 2151) (derived40869 p h) (h 24707)

theorem derived51589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3694) ∨ (¬ p 4181) ∨ (¬ p 4496) ∨ (¬ p 4878) ∨ (¬ p 5568) :=
  ElevenRUP.step51589 (p 2027) (p 3694) (p 4181) (p 4496) (p 4878) (p 5568) (derived40810 p h) (h 24709)

theorem derived51590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3449) ∨ (¬ p 3555) ∨ (¬ p 3694) ∨ (¬ p 4446) ∨ (¬ p 4878) :=
  ElevenRUP.step51590 (p 2027) (p 3449) (p 3555) (p 3694) (p 4446) (p 4878) (derived40810 p h) (h 24710)

theorem derived51591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3032) ∨ (¬ p 3553) ∨ (¬ p 3830) ∨ (¬ p 4366) ∨ (¬ p 4668) ∨ (¬ p 5362) :=
  ElevenRUP.step51591 (p 2027) (p 3032) (p 3553) (p 3830) (p 4366) (p 4668) (p 5362) (derived40810 p h) (h 24711)

theorem derived51592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 2299) ∨ (¬ p 3646) ∨ (¬ p 4275) ∨ (¬ p 4320) :=
  ElevenRUP.step51592 (p 1978) (p 2027) (p 2284) (p 2299) (p 2633) (p 3646) (p 4275) (p 4320) (h 2138) (derived40810 p h) (derived40879 p h) (h 24714)

theorem derived51593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2573) ∨ (¬ p 2996) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 5190) :=
  ElevenRUP.step51593 (p 2027) (p 2247) (p 2352) (p 2363) (p 2573) (p 2996) (p 3947) (p 4669) (p 5190) (derived40810 p h) (h 24715)

theorem derived51594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (¬ p 2247) ∨ (¬ p 2619) ∨ (¬ p 2996) ∨ (¬ p 3146) ∨ (¬ p 3947) ∨ (¬ p 4669) ∨ (¬ p 4733) :=
  ElevenRUP.step51594 (p 2027) (p 2132) (p 2247) (p 2619) (p 2996) (p 3146) (p 3947) (p 4669) (p 4733) (derived40810 p h) (h 24716)

theorem derived51595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 2750) ∨ (¬ p 3954) ∨ (¬ p 4111) :=
  ElevenRUP.step51595 (p 2027) (p 2253) (p 2651) (p 2750) (p 3954) (p 4111) (derived40810 p h) (h 24717)

theorem derived51596 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2745) ∨ (¬ p 2870) ∨ (¬ p 4111) ∨ (¬ p 4313) ∨ (¬ p 4320) ∨ (¬ p 4700) :=
  ElevenRUP.step51596 (p 2027) (p 2745) (p 2870) (p 4111) (p 4313) (p 4320) (p 4700) (derived40810 p h) (h 24719)

theorem derived51597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2761) ∨ (¬ p 3093) ∨ (¬ p 3309) :=
  ElevenRUP.step51597 (p 1988) (p 2027) (p 2396) (p 2699) (p 2761) (p 3093) (p 3309) (h 2148) (derived40810 p h) (derived40881 p h) (h 24720)

theorem derived51598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2696) ∨ (p 2744) ∨ (¬ p 2749) :=
  ElevenRUP.step51598 (p 1987) (p 2611) (p 2696) (p 2744) (p 2749) (h 2147) (derived40877 p h) (h 24722)

theorem derived51599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2741) ∨ (¬ p 2797) ∨ (¬ p 3367) ∨ (¬ p 4154) ∨ (¬ p 4752) :=
  ElevenRUP.step51599 (p 2027) (p 2741) (p 2797) (p 3367) (p 4154) (p 4752) (derived40810 p h) (h 24723)

theorem derived51600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 3486) ∨ (¬ p 3570) ∨ (¬ p 4525) ∨ (¬ p 4988) :=
  ElevenRUP.step51600 (p 2027) (p 2341) (p 3486) (p 3570) (p 4525) (p 4988) (derived40810 p h) (h 24724)

theorem derived51603 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2499) ∨ (¬ p 3956) ∨ (¬ p 4347) :=
  ElevenRUP.step51603 (p 1995) (p 2027) (p 2459) (p 2499) (p 2633) (p 3956) (p 4347) (h 2155) (derived40810 p h) (derived40879 p h) (h 24727)

theorem derived51607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2737) ∨ (¬ p 3005) ∨ (¬ p 3583) ∨ (¬ p 4316) ∨ (¬ p 5065) :=
  ElevenRUP.step51607 (p 2027) (p 2737) (p 3005) (p 3583) (p 4316) (p 5065) (derived40810 p h) (h 24731)

theorem derived51608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2098) ∨ (¬ p 2341) ∨ (¬ p 3425) ∨ (¬ p 3659) ∨ (¬ p 4242) :=
  ElevenRUP.step51608 (p 1992) (p 2027) (p 2098) (p 2341) (p 3360) (p 3425) (p 3659) (p 4242) (h 2152) (derived40810 p h) (derived40895 p h) (h 24732)

theorem derived51609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2493) ∨ (¬ p 3379) :=
  ElevenRUP.step51609 (p 1982) (p 2027) (p 2352) (p 2363) (p 2493) (p 2699) (p 3379) (h 2142) (derived40810 p h) (derived40881 p h) (h 24733)

theorem derived51610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2499) ∨ (¬ p 2584) ∨ (¬ p 2588) ∨ (¬ p 5194) :=
  ElevenRUP.step51610 (p 2027) (p 2307) (p 2499) (p 2584) (p 2588) (p 5194) (derived40810 p h) (h 24734)

theorem derived51611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2312) ∨ (¬ p 2341) ∨ (¬ p 3319) ∨ (¬ p 3548) ∨ (¬ p 4105) ∨ (¬ p 4624) :=
  ElevenRUP.step51611 (p 2027) (p 2312) (p 2341) (p 3319) (p 3548) (p 4105) (p 4624) (derived40810 p h) (h 24736)

theorem derived51612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3556) ∨ (¬ p 3569) ∨ (¬ p 4524) :=
  ElevenRUP.step51612 (p 2027) (p 2922) (p 3379) (p 3556) (p 3569) (p 4524) (derived40810 p h) (h 24737)

theorem derived51613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2584) ∨ (¬ p 2588) ∨ (¬ p 2665) ∨ (¬ p 3574) :=
  ElevenRUP.step51613 (p 2027) (p 2307) (p 2584) (p 2588) (p 2665) (p 3574) (derived40810 p h) (h 24739)

theorem derived51614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2230) ∨ (¬ p 2579) ∨ (¬ p 2901) ∨ (¬ p 3096) ∨ (¬ p 3879) ∨ (¬ p 4558) :=
  ElevenRUP.step51614 (p 2027) (p 2230) (p 2579) (p 2901) (p 3096) (p 3879) (p 4558) (derived40810 p h) (h 24740)

theorem derived51616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2254) ∨ (¬ p 2534) ∨ (¬ p 2619) ∨ (¬ p 2657) ∨ (¬ p 3125) ∨ (¬ p 3917) ∨ (¬ p 4172) ∨ (¬ p 4193) ∨ (¬ p 4256) :=
  ElevenRUP.step51616 (p 2001) (p 2027) (p 2156) (p 2254) (p 2534) (p 2619) (p 2657) (p 2766) (p 3125) (p 3917) (p 4172) (p 4193) (p 4256) (h 2161) (derived40810 p h) (derived40884 p h) (h 24742)

theorem derived51620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2584) ∨ (¬ p 2590) ∨ (¬ p 3540) ∨ (¬ p 3654) ∨ (¬ p 4137) ∨ (¬ p 4644) :=
  ElevenRUP.step51620 (p 2027) (p 2584) (p 2590) (p 3540) (p 3654) (p 4137) (p 4644) (derived40810 p h) (h 24747)

theorem derived51624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 2373) ∨ (¬ p 2588) ∨ (¬ p 2590) :=
  ElevenRUP.step51624 (p 2001) (p 2027) (p 2148) (p 2156) (p 2274) (p 2373) (p 2588) (p 2590) (h 2161) (derived40810 p h) (derived40865 p h) (h 24753)

theorem derived51634 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2584) ∨ (¬ p 2589) ∨ (¬ p 3654) ∨ (¬ p 4137) ∨ (¬ p 4717) :=
  ElevenRUP.step51634 (p 2027) (p 2584) (p 2589) (p 3654) (p 4137) (p 4717) (derived40810 p h) (h 24763)

theorem derived51637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 3742) :=
  ElevenRUP.step51637 (p 1994) (p 2027) (p 2247) (p 2688) (p 2922) (p 3379) (p 3742) (h 2154) (derived40810 p h) (derived40880 p h) (h 24766)

theorem derived51638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 3055) ∨ (¬ p 3367) ∨ (¬ p 3471) :=
  ElevenRUP.step51638 (p 2008) (p 2027) (p 2622) (p 2743) (p 3055) (p 3367) (p 3471) (h 2168) (derived40810 p h) (derived40878 p h) (h 24767)

theorem derived51643 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2459) ∨ (¬ p 2727) ∨ (¬ p 3343) ∨ (¬ p 3556) ∨ (¬ p 3692) ∨ (¬ p 4045) ∨ (¬ p 4119) ∨ (¬ p 4420) ∨ (¬ p 4524) :=
  ElevenRUP.step51643 (p 2027) (p 2241) (p 2459) (p 2727) (p 3343) (p 3556) (p 3692) (p 4045) (p 4119) (p 4420) (p 4524) (derived40810 p h) (h 24773)

theorem derived51658 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2470) ∨ (¬ p 2509) ∨ (¬ p 2563) :=
  ElevenRUP.step51658 (p 1990) (p 2027) (p 2233) (p 2406) (p 2470) (p 2509) (p 2563) (h 2150) (derived40810 p h) (derived40868 p h) (h 24794)

theorem derived51660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2298) ∨ (¬ p 2331) ∨ (¬ p 3414) ∨ (¬ p 4107) ∨ (¬ p 4154) :=
  ElevenRUP.step51660 (p 1977) (p 2027) (p 2298) (p 2331) (p 2462) (p 3414) (p 4107) (p 4154) (h 2137) (derived40810 p h) (derived40875 p h) (h 24797)

theorem derived51667 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2187) ∨ (¬ p 2363) ∨ (¬ p 3585) ∨ (¬ p 3954) ∨ (¬ p 4521) ∨ (¬ p 4697) ∨ (¬ p 5160) :=
  ElevenRUP.step51667 (p 2027) (p 2156) (p 2187) (p 2363) (p 3585) (p 3954) (p 4521) (p 4697) (p 5160) (derived40810 p h) (h 24804)

theorem derived51669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3425) ∨ (¬ p 3516) ∨ (¬ p 3873) ∨ (¬ p 4324) ∨ (¬ p 5207) :=
  ElevenRUP.step51669 (p 2027) (p 3425) (p 3516) (p 3873) (p 4324) (p 5207) (derived40810 p h) (h 24806)

theorem derived51670 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2341) ∨ (¬ p 2396) ∨ (¬ p 3238) ∨ (¬ p 3452) ∨ (¬ p 3951) ∨ (¬ p 4948) ∨ (¬ p 5207) :=
  ElevenRUP.step51670 (p 2027) (p 2299) (p 2341) (p 2396) (p 3238) (p 3452) (p 3951) (p 4948) (p 5207) (derived40810 p h) (h 24807)

theorem derived51673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3591) ∨ (¬ p 4111) ∨ (¬ p 4756) :=
  ElevenRUP.step51673 (p 2027) (p 2253) (p 2651) (p 3591) (p 4111) (p 4756) (derived40810 p h) (h 24810)

theorem derived51674 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2707) ∨ (¬ p 3540) ∨ (¬ p 3585) ∨ (¬ p 3658) ∨ (¬ p 4727) :=
  ElevenRUP.step51674 (p 2027) (p 2707) (p 3540) (p 3585) (p 3658) (p 4727) (derived40810 p h) (h 24812)

theorem derived51676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3555) ∨ (¬ p 4111) ∨ (¬ p 4448) :=
  ElevenRUP.step51676 (p 2027) (p 2253) (p 2651) (p 3555) (p 4111) (p 4448) (derived40810 p h) (h 24814)

theorem derived51678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) ∨ (¬ p 2737) ∨ (¬ p 2750) ∨ (¬ p 2811) ∨ (¬ p 4154) :=
  ElevenRUP.step51678 (p 2027) (p 2331) (p 2737) (p 2750) (p 2811) (p 4154) (derived40810 p h) (h 24816)

theorem derived51680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3506) ∨ (¬ p 3842) ∨ (¬ p 4111) :=
  ElevenRUP.step51680 (p 1988) (p 2027) (p 2253) (p 2651) (p 2699) (p 3506) (p 3842) (p 4111) (h 2148) (derived40810 p h) (derived40881 p h) (h 24818)

theorem derived51681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3461) ∨ (¬ p 3564) ∨ (¬ p 4204) ∨ (¬ p 4322) ∨ (¬ p 4402) ∨ (¬ p 4718) :=
  ElevenRUP.step51681 (p 2027) (p 3461) (p 3564) (p 4204) (p 4322) (p 4402) (p 4718) (derived40810 p h) (h 24820)

theorem derived51687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2255) ∨ (¬ p 2946) ∨ (¬ p 3125) ∨ (¬ p 3266) ∨ (¬ p 3297) ∨ (¬ p 3412) ∨ (¬ p 3773) ∨ (¬ p 3848) ∨ (¬ p 4330) :=
  ElevenRUP.step51687 (p 2027) (p 2192) (p 2255) (p 2946) (p 3125) (p 3266) (p 3297) (p 3412) (p 3773) (p 3848) (p 4330) (derived40810 p h) (h 24828)

theorem derived51688 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2210) ∨ (¬ p 2972) ∨ (¬ p 3680) ∨ (¬ p 4191) :=
  ElevenRUP.step51688 (p 1999) (p 2027) (p 2210) (p 2699) (p 2972) (p 3680) (p 4191) (h 2159) (derived40810 p h) (derived40881 p h) (h 24829)

theorem derived51694 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2499) ∨ (¬ p 2542) ∨ (¬ p 2573) ∨ (¬ p 3487) ∨ (¬ p 4079) :=
  ElevenRUP.step51694 (p 1997) (p 2027) (p 2247) (p 2499) (p 2542) (p 2573) (p 2688) (p 3487) (p 4079) (h 2157) (derived40810 p h) (derived40880 p h) (h 24836)

theorem derived51697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3189) ∨ (¬ p 3256) ∨ (¬ p 4111) :=
  ElevenRUP.step51697 (p 1982) (p 2027) (p 2253) (p 2651) (p 2699) (p 3189) (p 3256) (p 4111) (h 2142) (derived40810 p h) (derived40881 p h) (h 24840)

theorem derived51699 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3707) ∨ (¬ p 3833) ∨ (¬ p 4111) ∨ (¬ p 4425) :=
  ElevenRUP.step51699 (p 2012) (p 2027) (p 2253) (p 2651) (p 2699) (p 3707) (p 3833) (p 4111) (p 4425) (h 2172) (derived40810 p h) (derived40881 p h) (h 24842)

theorem derived51700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2459) ∨ (¬ p 2651) ∨ (¬ p 3189) ∨ (¬ p 3556) ∨ (¬ p 3692) ∨ (¬ p 4111) ∨ (¬ p 4119) ∨ (¬ p 4524) ∨ (¬ p 4550) :=
  ElevenRUP.step51700 (p 2027) (p 2253) (p 2459) (p 2651) (p 3189) (p 3556) (p 3692) (p 4111) (p 4119) (p 4524) (p 4550) (derived40810 p h) (h 24843)

theorem derived51707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3146) ∨ (¬ p 3919) ∨ (¬ p 4132) ∨ (¬ p 4261) ∨ (¬ p 4288) ∨ (¬ p 4570) :=
  ElevenRUP.step51707 (p 2027) (p 2177) (p 3146) (p 3919) (p 4132) (p 4261) (p 4288) (p 4570) (derived40810 p h) (h 24850)

theorem derived51708 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 3027) ∨ (¬ p 3556) ∨ (¬ p 3570) ∨ (¬ p 4111) ∨ (¬ p 4524) ∨ (¬ p 4570) :=
  ElevenRUP.step51708 (p 2027) (p 2177) (p 2253) (p 2651) (p 3027) (p 3556) (p 3570) (p 4111) (p 4524) (p 4570) (derived40810 p h) (h 24851)

theorem derived51710 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2651) ∨ (¬ p 2860) ∨ (¬ p 3027) ∨ (¬ p 3646) ∨ (¬ p 4111) ∨ (¬ p 4244) ∨ (¬ p 4280) ∨ (¬ p 4524) :=
  ElevenRUP.step51710 (p 2027) (p 2253) (p 2651) (p 2860) (p 3027) (p 3646) (p 4111) (p 4244) (p 4280) (p 4524) (derived40810 p h) (h 24853)

theorem derived51714 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2588) ∨ (¬ p 2881) ∨ (¬ p 3872) ∨ (¬ p 3958) :=
  ElevenRUP.step51714 (p 2027) (p 2299) (p 2588) (p 2881) (p 3872) (p 3958) (derived40810 p h) (h 24857)

theorem derived51719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2299) ∨ (¬ p 2651) ∨ (¬ p 3097) ∨ (¬ p 3189) ∨ (¬ p 3646) ∨ (¬ p 4111) ∨ (¬ p 4524) ∨ (¬ p 4550) :=
  ElevenRUP.step51719 (p 2027) (p 2253) (p 2299) (p 2651) (p 3097) (p 3189) (p 3646) (p 4111) (p 4524) (p 4550) (derived40810 p h) (h 24862)

theorem derived51723 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (¬ p 3027) ∨ (¬ p 4280) ∨ (¬ p 4360) ∨ (¬ p 4548) :=
  ElevenRUP.step51723 (p 2027) (p 2881) (p 3027) (p 4280) (p 4360) (p 4548) (derived40810 p h) (h 24866)

theorem derived51725 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2253) ∨ (¬ p 2528) ∨ (¬ p 2651) ∨ (¬ p 3083) ∨ (¬ p 3097) ∨ (¬ p 3646) ∨ (¬ p 4107) ∨ (¬ p 4524) ∨ (¬ p 4669) :=
  ElevenRUP.step51725 (p 2027) (p 2253) (p 2528) (p 2651) (p 3083) (p 3097) (p 3646) (p 4107) (p 4524) (p 4669) (derived40810 p h) (h 24868)

theorem derived51727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2992) ∨ (¬ p 2996) ∨ (¬ p 3699) ∨ (¬ p 4702) :=
  ElevenRUP.step51727 (p 2027) (p 2427) (p 2992) (p 2996) (p 3699) (p 4702) (derived40810 p h) (h 24871)

theorem derived51729 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2298) ∨ (¬ p 2331) ∨ (¬ p 3414) ∨ (¬ p 4564) :=
  ElevenRUP.step51729 (p 2027) (p 2274) (p 2298) (p 2331) (p 3414) (p 4564) (derived40810 p h) (h 24873)

theorem derived51730 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2608) ∨ (¬ p 3097) ∨ (¬ p 3367) ∨ (¬ p 3641) ∨ (¬ p 3646) ∨ (¬ p 4420) ∨ (¬ p 4524) :=
  ElevenRUP.step51730 (p 2027) (p 2299) (p 2608) (p 3097) (p 3367) (p 3641) (p 3646) (p 4420) (p 4524) (derived40810 p h) (h 24874)

theorem derived51731 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2298) ∨ (¬ p 2641) ∨ (¬ p 2996) ∨ (¬ p 3958) ∨ (¬ p 3984) :=
  ElevenRUP.step51731 (p 2027) (p 2274) (p 2298) (p 2641) (p 2996) (p 3958) (p 3984) (derived40810 p h) (h 24875)

theorem derived51733 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2962) ∨ (¬ p 3097) ∨ (¬ p 3370) ∨ (¬ p 3758) ∨ (¬ p 4878) :=
  ElevenRUP.step51733 (p 2027) (p 2307) (p 2962) (p 3097) (p 3370) (p 3758) (p 4878) (derived40810 p h) (h 24877)

theorem derived51734 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2651) ∨ (¬ p 3983) ∨ (¬ p 4972) :=
  ElevenRUP.step51734 (p 2027) (p 2295) (p 2313) (p 2651) (p 3983) (p 4972) (derived40810 p h) (h 24879)

theorem derived51735 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2577) ∨ (¬ p 2743) ∨ (¬ p 3309) ∨ (¬ p 3363) ∨ (¬ p 4752) ∨ (¬ p 4869) :=
  ElevenRUP.step51735 (p 2027) (p 2313) (p 2577) (p 2743) (p 3309) (p 3363) (p 4752) (p 4869) (derived40810 p h) (h 24880)

theorem derived51737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 2427) ∨ (¬ p 4110) ∨ (¬ p 4140) ∨ (¬ p 4486) :=
  ElevenRUP.step51737 (p 2027) (p 2313) (p 2427) (p 4110) (p 4140) (p 4486) (derived40810 p h) (h 24882)

theorem derived51739 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2295) ∨ (¬ p 2313) ∨ (¬ p 2641) ∨ (¬ p 3983) :=
  ElevenRUP.step51739 (p 2027) (p 2249) (p 2295) (p 2313) (p 2641) (p 3983) (derived40810 p h) (h 24885)

theorem derived51741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2598) ∨ (¬ p 2742) ∨ (¬ p 2778) ∨ (¬ p 3063) ∨ (¬ p 4752) ∨ (¬ p 4759) :=
  ElevenRUP.step51741 (p 2027) (p 2387) (p 2598) (p 2742) (p 2778) (p 3063) (p 4752) (p 4759) (derived40810 p h) (h 24887)

theorem derived51743 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 3038) ∨ (¬ p 3414) ∨ (¬ p 3527) ∨ (¬ p 3553) :=
  ElevenRUP.step51743 (p 2027) (p 2249) (p 3038) (p 3414) (p 3527) (p 3553) (derived40810 p h) (h 24889)

theorem derived51746 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3172) ∨ (¬ p 3568) ∨ (¬ p 3987) ∨ (¬ p 4153) ∨ (¬ p 5062) :=
  ElevenRUP.step51746 (p 2027) (p 2307) (p 3172) (p 3568) (p 3987) (p 4153) (p 5062) (derived40810 p h) (h 24892)

theorem derived51748 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (¬ p 2797) ∨ (¬ p 2963) ∨ (¬ p 4236) ∨ (¬ p 4752) :=
  ElevenRUP.step51748 (p 2027) (p 2598) (p 2797) (p 2963) (p 4236) (p 4752) (derived40810 p h) (h 24894)

theorem derived51749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2655) ∨ (¬ p 2992) ∨ (¬ p 3115) ∨ (¬ p 3904) ∨ (¬ p 4032) :=
  ElevenRUP.step51749 (p 2027) (p 2249) (p 2655) (p 2992) (p 3115) (p 3904) (p 4032) (derived40810 p h) (h 24895)

theorem derived51751 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2655) ∨ (¬ p 2901) ∨ (¬ p 2992) ∨ (¬ p 3556) ∨ (¬ p 3904) :=
  ElevenRUP.step51751 (p 2027) (p 2249) (p 2655) (p 2901) (p 2992) (p 3556) (p 3904) (derived40810 p h) (h 24897)

theorem derived51752 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2963) ∨ (¬ p 3309) ∨ (¬ p 3568) ∨ (¬ p 4759) :=
  ElevenRUP.step51752 (p 2027) (p 2249) (p 2963) (p 3309) (p 3568) (p 4759) (derived40810 p h) (h 24898)

theorem derived51753 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 3166) ∨ (¬ p 3292) ∨ (¬ p 3877) :=
  ElevenRUP.step51753 (p 1994) (p 2027) (p 2630) (p 3166) (p 3292) (p 3871) (p 3877) (h 2154) (derived40810 p h) (derived40906 p h) (h 24899)

theorem derived51756 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2449) ∨ (¬ p 2499) ∨ (¬ p 3452) ∨ (¬ p 3553) ∨ (¬ p 4137) ∨ (¬ p 4625) ∨ (¬ p 5207) :=
  ElevenRUP.step51756 (p 2027) (p 2341) (p 2449) (p 2499) (p 3452) (p 3553) (p 4137) (p 4625) (p 5207) (derived40810 p h) (h 24902)

theorem derived51761 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2249) ∨ (¬ p 2952) ∨ (¬ p 3952) ∨ (¬ p 4365) :=
  ElevenRUP.step51761 (p 2027) (p 2192) (p 2249) (p 2952) (p 3952) (p 4365) (derived40810 p h) (h 24907)

theorem derived51762 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2383) ∨ (¬ p 2528) ∨ (¬ p 3693) ∨ (¬ p 3946) ∨ (¬ p 4134) ∨ (¬ p 4171) :=
  ElevenRUP.step51762 (p 2027) (p 2383) (p 2528) (p 3693) (p 3946) (p 4134) (p 4171) (derived40810 p h) (h 24908)

theorem derived51765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2406) ∨ (¬ p 2440) ∨ (¬ p 2657) ∨ (¬ p 4281) :=
  ElevenRUP.step51765 (p 2027) (p 2249) (p 2406) (p 2440) (p 2657) (p 4281) (derived40810 p h) (h 24911)

theorem derived51766 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2589) ∨ (¬ p 3948) ∨ (¬ p 4110) ∨ (¬ p 5191) :=
  ElevenRUP.step51766 (p 2027) (p 2192) (p 2589) (p 3948) (p 4110) (p 5191) (derived40810 p h) (h 24912)

theorem derived51767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2249) ∨ (¬ p 2499) ∨ (¬ p 2657) ∨ (¬ p 3189) ∨ (¬ p 3487) ∨ (¬ p 3506) ∨ (¬ p 4137) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 5111) :=
  ElevenRUP.step51767 (p 2027) (p 2249) (p 2499) (p 2657) (p 3189) (p 3487) (p 3506) (p 4137) (p 4444) (p 4604) (p 5111) (derived40810 p h) (h 24914)

theorem derived51769 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2341) ∨ (¬ p 2499) ∨ (¬ p 3246) ∨ (¬ p 3452) ∨ (¬ p 3570) ∨ (¬ p 4137) ∨ (¬ p 4443) ∨ (¬ p 4604) ∨ (¬ p 5207) :=
  ElevenRUP.step51769 (p 2027) (p 2341) (p 2499) (p 3246) (p 3452) (p 3570) (p 4137) (p 4443) (p 4604) (p 5207) (derived40810 p h) (h 24916)

theorem derived51772 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 3125) ∨ (¬ p 4037) ∨ (¬ p 4153) ∨ (¬ p 4960) :=
  ElevenRUP.step51772 (p 2027) (p 2192) (p 3125) (p 4037) (p 4153) (p 4960) (derived40810 p h) (h 24920)

theorem derived51774 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 3941) ∨ (¬ p 3961) ∨ (¬ p 4851) ∨ (¬ p 5590) :=
  ElevenRUP.step51774 (p 2027) (p 2264) (p 3941) (p 3961) (p 4851) (p 5590) (derived40810 p h) (h 24922)

theorem derived51775 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2311) ∨ (¬ p 2427) ∨ (¬ p 2881) ∨ (¬ p 3551) ∨ (¬ p 4198) ∨ (¬ p 4533) :=
  ElevenRUP.step51775 (p 2027) (p 2311) (p 2427) (p 2881) (p 3551) (p 4198) (p 4533) (derived40810 p h) (h 24923)

theorem derived51776 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2136) ∨ (¬ p 2598) ∨ (¬ p 2619) ∨ (¬ p 4120) ∨ (¬ p 4313) ∨ (¬ p 4752) :=
  ElevenRUP.step51776 (p 2027) (p 2136) (p 2598) (p 2619) (p 4120) (p 4313) (p 4752) (derived40810 p h) (h 24926)

theorem derived51778 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2220) ∨ (¬ p 2284) ∨ (¬ p 2313) ∨ (¬ p 2598) ∨ (¬ p 2778) ∨ (¬ p 2811) ∨ (¬ p 2958) ∨ (¬ p 3309) ∨ (¬ p 3497) ∨ (¬ p 3923) ∨ (¬ p 4752) :=
  ElevenRUP.step51778 (p 1990) (p 2027) (p 2169) (p 2220) (p 2284) (p 2313) (p 2598) (p 2778) (p 2811) (p 2958) (p 3309) (p 3497) (p 3923) (p 4752) (h 2150) (derived40810 p h) (derived40866 p h) (h 24928)

theorem derived51784 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2928) ∨ (¬ p 3580) ∨ (¬ p 3644) ∨ (¬ p 4811) :=
  ElevenRUP.step51784 (p 2027) (p 2264) (p 2928) (p 3580) (p 3644) (p 4811) (derived40810 p h) (h 24938)

theorem derived51787 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3027) ∨ (¬ p 3166) ∨ (¬ p 3572) ∨ (¬ p 4360) :=
  ElevenRUP.step51787 (p 1987) (p 2027) (p 2323) (p 3027) (p 3166) (p 3572) (p 4360) (h 2147) (derived40810 p h) (derived40870 p h) (h 24942)

theorem derived51790 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 2761) ∨ (¬ p 3452) ∨ (¬ p 3516) ∨ (¬ p 4137) ∨ (¬ p 4444) ∨ (¬ p 4604) ∨ (¬ p 5207) :=
  ElevenRUP.step51790 (p 2027) (p 2499) (p 2761) (p 3452) (p 3516) (p 4137) (p 4444) (p 4604) (p 5207) (derived40810 p h) (h 24946)

theorem derived51791 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2459) ∨ (¬ p 2881) ∨ (¬ p 3266) :=
  ElevenRUP.step51791 (p 1988) (p 2027) (p 2202) (p 2427) (p 2459) (p 2881) (p 3266) (h 2148) (derived40810 p h) (derived40867 p h) (h 24947)

theorem derived51795 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2247) ∨ (¬ p 2761) ∨ (¬ p 3516) ∨ (¬ p 4037) ∨ (¬ p 4154) ∨ (¬ p 4444) ∨ (¬ p 4521) ∨ (¬ p 4604) ∨ (¬ p 4988) :=
  ElevenRUP.step51795 (p 2027) (p 2247) (p 2761) (p 3516) (p 4037) (p 4154) (p 4444) (p 4521) (p 4604) (p 4988) (derived40810 p h) (h 24954)

theorem derived51797 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2542) ∨ (¬ p 2598) ∨ (¬ p 2737) ∨ (¬ p 3365) ∨ (¬ p 3683) :=
  ElevenRUP.step51797 (p 1997) (p 2027) (p 2114) (p 2542) (p 2598) (p 2737) (p 3365) (p 3683) (h 2157) (derived40810 p h) (derived40864 p h) (h 24956)

theorem derived51799 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2589) ∨ (¬ p 3347) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3692) ∨ (¬ p 3880) ∨ (¬ p 3950) ∨ (¬ p 3954) ∨ (¬ p 5216) :=
  ElevenRUP.step51799 (p 2027) (p 2589) (p 3347) (p 3399) (p 3631) (p 3692) (p 3880) (p 3950) (p 3954) (p 5216) (derived40810 p h) (h 24958)

theorem derived51800 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3204) ∨ (¬ p 3266) ∨ (¬ p 3399) ∨ (¬ p 3631) ∨ (¬ p 3946) ∨ (¬ p 3950) ∨ (¬ p 3954) ∨ (¬ p 4191) ∨ (¬ p 4870) :=
  ElevenRUP.step51800 (p 2027) (p 3204) (p 3266) (p 3399) (p 3631) (p 3946) (p 3950) (p 3954) (p 4191) (p 4870) (derived40810 p h) (h 24959)

theorem derived51801 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2274) ∨ (¬ p 3414) ∨ (¬ p 3553) :=
  ElevenRUP.step51801 (p 1991) (p 2027) (p 2177) (p 2274) (p 2765) (p 3414) (p 3553) (h 2151) (derived40810 p h) (derived40883 p h) (h 24960)

theorem derived51803 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2743) ∨ (¬ p 2922) ∨ (¬ p 3363) ∨ (¬ p 3540) ∨ (¬ p 3541) ∨ (¬ p 4752) :=
  ElevenRUP.step51803 (p 2027) (p 2743) (p 2922) (p 3363) (p 3540) (p 3541) (p 4752) (derived40810 p h) (h 24963)

theorem derived51805 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2192) ∨ (¬ p 2751) ∨ (¬ p 3952) ∨ (¬ p 4315) ∨ (¬ p 4365) :=
  ElevenRUP.step51805 (p 2027) (p 2192) (p 2751) (p 3952) (p 4315) (p 4365) (derived40810 p h) (h 24965)

theorem derived51808 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2110) ∨ (¬ p 2138) ∨ (¬ p 3246) ∨ (¬ p 3998) ∨ (¬ p 4119) ∨ (¬ p 5568) :=
  ElevenRUP.step51808 (p 1983) (p 2027) (p 2110) (p 2138) (p 3246) (p 3474) (p 3998) (p 4119) (p 5568) (h 2143) (derived40810 p h) (derived40898 p h) (h 24969)

end ElevenLogic
