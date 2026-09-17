import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory012
import SunPrize.Certificate.Theory013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule12958 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p3692) ∨ (((¬ p3949) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p5056) ∨ (¬ p4450))) := by
  classical
  tauto

theorem initial12958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (meaning t m 5995) := by
  exact rule12958 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule12959 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p4335) ∨ (((¬ p3949) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p5056) ∨ (¬ p4450))) := by
  classical
  tauto

theorem initial12959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4335) ∨ (meaning t m 5995) := by
  exact rule12959 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule12960 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p5056) ∨ (((¬ p3949) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p5056) ∨ (¬ p4450))) := by
  classical
  tauto

theorem initial12960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5056) ∨ (meaning t m 5995) := by
  exact rule12960 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule12961 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p4450) ∨ (((¬ p3949) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p5056) ∨ (¬ p4450))) := by
  classical
  tauto

theorem initial12961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4450) ∨ (meaning t m 5995) := by
  exact rule12961 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule12963 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p2532) ∨ (((¬ p2532) ∨ (¬ p2533) ∨ (¬ p3146) ∨ (¬ p5058) ∨ (¬ p5059))) := by
  classical
  tauto

theorem initial12963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2532) ∨ (meaning t m 5996) := by
  exact rule12963 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule12964 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p2533) ∨ (((¬ p2532) ∨ (¬ p2533) ∨ (¬ p3146) ∨ (¬ p5058) ∨ (¬ p5059))) := by
  classical
  tauto

theorem initial12964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2533) ∨ (meaning t m 5996) := by
  exact rule12964 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule12965 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p3146) ∨ (((¬ p2532) ∨ (¬ p2533) ∨ (¬ p3146) ∨ (¬ p5058) ∨ (¬ p5059))) := by
  classical
  tauto

theorem initial12965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3146) ∨ (meaning t m 5996) := by
  exact rule12965 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule12967 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p5059) ∨ (((¬ p2532) ∨ (¬ p2533) ∨ (¬ p3146) ∨ (¬ p5058) ∨ (¬ p5059))) := by
  classical
  tauto

theorem initial12967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5059) ∨ (meaning t m 5996) := by
  exact rule12967 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule12971 (p5995 p5996 : Prop) : (¬ ((¬ p5995) ∨ (¬ p5996))) ∨ (¬ p5995) ∨ (¬ p5996) := by
  classical
  tauto

theorem initial12971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5994)) ∨ (¬ (meaning t m 5995)) ∨ (¬ (meaning t m 5996)) := by
  exact rule12971 (meaning t m 5995) (meaning t m 5996)

theorem rule12972 (p5054 p5994 : Prop) (h : (p5054 ↔ p5994)) : (¬ p5054) ∨ (p5994) := by
  classical
  tauto

theorem initial12972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5054)) ∨ (meaning t m 5994) := by
  have source := ElevenTheory.theory3333 t (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule12972 (meaning t m 5054) (meaning t m 5994) source

theorem rule12974 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p4312) ∨ (((¬ p4312) ∨ (¬ p3497) ∨ (¬ p3661) ∨ (¬ p5062) ∨ (¬ p5063))) := by
  classical
  tauto

theorem initial12974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4312) ∨ (meaning t m 5998) := by
  exact rule12974 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule12975 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p3497) ∨ (((¬ p4312) ∨ (¬ p3497) ∨ (¬ p3661) ∨ (¬ p5062) ∨ (¬ p5063))) := by
  classical
  tauto

theorem initial12975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3497) ∨ (meaning t m 5998) := by
  exact rule12975 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule12976 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p3661) ∨ (((¬ p4312) ∨ (¬ p3497) ∨ (¬ p3661) ∨ (¬ p5062) ∨ (¬ p5063))) := by
  classical
  tauto

theorem initial12976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3661) ∨ (meaning t m 5998) := by
  exact rule12976 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule12977 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p5062) ∨ (((¬ p4312) ∨ (¬ p3497) ∨ (¬ p3661) ∨ (¬ p5062) ∨ (¬ p5063))) := by
  classical
  tauto

theorem initial12977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5062) ∨ (meaning t m 5998) := by
  exact rule12977 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule12980 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p4311) ∨ (((¬ p4311) ∨ (¬ p4237) ∨ (¬ p3156) ∨ (¬ p5065) ∨ (¬ p4043))) := by
  classical
  tauto

theorem initial12980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4311) ∨ (meaning t m 5999) := by
  exact rule12980 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule12981 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p4237) ∨ (((¬ p4311) ∨ (¬ p4237) ∨ (¬ p3156) ∨ (¬ p5065) ∨ (¬ p4043))) := by
  classical
  tauto

theorem initial12981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4237) ∨ (meaning t m 5999) := by
  exact rule12981 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule12982 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p3156) ∨ (((¬ p4311) ∨ (¬ p4237) ∨ (¬ p3156) ∨ (¬ p5065) ∨ (¬ p4043))) := by
  classical
  tauto

theorem initial12982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3156) ∨ (meaning t m 5999) := by
  exact rule12982 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule12983 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p5065) ∨ (((¬ p4311) ∨ (¬ p4237) ∨ (¬ p3156) ∨ (¬ p5065) ∨ (¬ p4043))) := by
  classical
  tauto

theorem initial12983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5065) ∨ (meaning t m 5999) := by
  exact rule12983 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule12984 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p4043) ∨ (((¬ p4311) ∨ (¬ p4237) ∨ (¬ p3156) ∨ (¬ p5065) ∨ (¬ p4043))) := by
  classical
  tauto

theorem initial12984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4043) ∨ (meaning t m 5999) := by
  exact rule12984 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule12988 (p5998 p5999 : Prop) : (¬ ((¬ p5998) ∨ (¬ p5999))) ∨ (¬ p5998) ∨ (¬ p5999) := by
  classical
  tauto

theorem initial12988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5997)) ∨ (¬ (meaning t m 5998)) ∨ (¬ (meaning t m 5999)) := by
  exact rule12988 (meaning t m 5998) (meaning t m 5999)

theorem rule12989 (p5060 p5997 : Prop) (h : (p5060 ↔ p5997)) : (¬ p5060) ∨ (p5997) := by
  classical
  tauto

theorem initial12989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5060)) ∨ (meaning t m 5997) := by
  have source := ElevenTheory.theory3334 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule12989 (meaning t m 5060) (meaning t m 5997) source

theorem rule12991 (p1977 p2027 p2651 p2811 p2997 p3568 p4111 p4195 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p2811) ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p4195) ∨ (¬ p3568) ∨ p2997) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2811) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4111) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial12991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2811)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory3335 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule12991 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2811) (meaning t m 2997) (meaning t m 3568) (meaning t m 4111) (meaning t m 4195) source

theorem rule12993 (p2252 p2963 p3922 p4759 : Prop) (h : (¬ p2963) ∨ (¬ p4759) ∨ (¬ p2252) ∨ (¬ p3922)) : (¬ p2252) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial12993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory3337 (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule12993 (meaning t m 2252) (meaning t m 2963) (meaning t m 3922) (meaning t m 4759) source

theorem rule12994 (p4262 p4360 p5074 p5075 p5076 : Prop) : (p4360) ∨ (((¬ p4360) ∨ (¬ p5075) ∨ (¬ p4262) ∨ (¬ p5074) ∨ (¬ p5076))) := by
  classical
  tauto

theorem initial12994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4360) ∨ (meaning t m 6001) := by
  exact rule12994 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule12996 (p4262 p4360 p5074 p5075 p5076 : Prop) : (p4262) ∨ (((¬ p4360) ∨ (¬ p5075) ∨ (¬ p4262) ∨ (¬ p5074) ∨ (¬ p5076))) := by
  classical
  tauto

theorem initial12996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4262) ∨ (meaning t m 6001) := by
  exact rule12996 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule12997 (p4262 p4360 p5074 p5075 p5076 : Prop) : (p5074) ∨ (((¬ p4360) ∨ (¬ p5075) ∨ (¬ p4262) ∨ (¬ p5074) ∨ (¬ p5076))) := by
  classical
  tauto

theorem initial12997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5074) ∨ (meaning t m 6001) := by
  exact rule12997 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule13000 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p4288) ∨ (((¬ p4288) ∨ (¬ p3859) ∨ (¬ p3189) ∨ (¬ p5078) ∨ (¬ p5079))) := by
  classical
  tauto

theorem initial13000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4288) ∨ (meaning t m 6002) := by
  exact rule13000 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule13001 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p3859) ∨ (((¬ p4288) ∨ (¬ p3859) ∨ (¬ p3189) ∨ (¬ p5078) ∨ (¬ p5079))) := by
  classical
  tauto

theorem initial13001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3859) ∨ (meaning t m 6002) := by
  exact rule13001 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule13002 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p3189) ∨ (((¬ p4288) ∨ (¬ p3859) ∨ (¬ p3189) ∨ (¬ p5078) ∨ (¬ p5079))) := by
  classical
  tauto

theorem initial13002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3189) ∨ (meaning t m 6002) := by
  exact rule13002 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule13003 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p5078) ∨ (((¬ p4288) ∨ (¬ p3859) ∨ (¬ p3189) ∨ (¬ p5078) ∨ (¬ p5079))) := by
  classical
  tauto

theorem initial13003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5078) ∨ (meaning t m 6002) := by
  exact rule13003 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule13008 (p6001 p6002 : Prop) : (¬ ((¬ p6001) ∨ (¬ p6002))) ∨ (¬ p6001) ∨ (¬ p6002) := by
  classical
  tauto

theorem initial13008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6000)) ∨ (¬ (meaning t m 6001)) ∨ (¬ (meaning t m 6002)) := by
  exact rule13008 (meaning t m 6001) (meaning t m 6002)

theorem rule13009 (p5072 p6000 : Prop) (h : (p5072 ↔ p6000)) : (¬ p5072) ∨ (p6000) := by
  classical
  tauto

theorem initial13009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5072)) ∨ (meaning t m 6000) := by
  have source := ElevenTheory.theory3338 t (m.theta 1 3) (m.theta 1 8) (m.theta 3 8)
  exact rule13009 (meaning t m 5072) (meaning t m 6000) source

theorem rule13011 (p1993 p2027 p2388 p2651 p2952 p3189 p4111 : Prop) (h : (¬ p1993) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p3189) ∨ p2027) : (¬ p1993) ∨ (p2027) ∨ (p2388) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3189) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial13011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3339 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule13011 (meaning t m 1993) (meaning t m 2027) (meaning t m 2388) (meaning t m 2651) (meaning t m 2952) (meaning t m 3189) (meaning t m 4111) source

theorem rule13013 (p1995 p2027 p2765 p2928 p3201 p3684 p4110 : Prop) (h : (¬ p1995) ∨ (¬ p2928) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3201) ∨ p2765) : (¬ p1995) ∨ (p2027) ∨ (p2765) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3341 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule13013 (meaning t m 1995) (meaning t m 2027) (meaning t m 2765) (meaning t m 2928) (meaning t m 3201) (meaning t m 3684) (meaning t m 4110) source

theorem rule13014 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p4106) ∨ (((¬ p4106) ∨ (¬ p3876) ∨ (¬ p3686) ∨ (¬ p5082) ∨ (¬ p5083))) := by
  classical
  tauto

theorem initial13014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4106) ∨ (meaning t m 6004) := by
  exact rule13014 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule13015 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p3876) ∨ (((¬ p4106) ∨ (¬ p3876) ∨ (¬ p3686) ∨ (¬ p5082) ∨ (¬ p5083))) := by
  classical
  tauto

theorem initial13015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3876) ∨ (meaning t m 6004) := by
  exact rule13015 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule13016 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p3686) ∨ (((¬ p4106) ∨ (¬ p3876) ∨ (¬ p3686) ∨ (¬ p5082) ∨ (¬ p5083))) := by
  classical
  tauto

theorem initial13016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3686) ∨ (meaning t m 6004) := by
  exact rule13016 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule13017 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p5082) ∨ (((¬ p4106) ∨ (¬ p3876) ∨ (¬ p3686) ∨ (¬ p5082) ∨ (¬ p5083))) := by
  classical
  tauto

theorem initial13017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5082) ∨ (meaning t m 6004) := by
  exact rule13017 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule13018 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p5083) ∨ (((¬ p4106) ∨ (¬ p3876) ∨ (¬ p3686) ∨ (¬ p5082) ∨ (¬ p5083))) := by
  classical
  tauto

theorem initial13018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5083) ∨ (meaning t m 6004) := by
  exact rule13018 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule13020 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p3658) ∨ (((¬ p3658) ∨ (¬ p5085) ∨ (¬ p3201) ∨ (¬ p5086) ∨ (¬ p5087))) := by
  classical
  tauto

theorem initial13020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3658) ∨ (meaning t m 6005) := by
  exact rule13020 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule13021 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p5085) ∨ (((¬ p3658) ∨ (¬ p5085) ∨ (¬ p3201) ∨ (¬ p5086) ∨ (¬ p5087))) := by
  classical
  tauto

theorem initial13021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5085) ∨ (meaning t m 6005) := by
  exact rule13021 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule13022 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p3201) ∨ (((¬ p3658) ∨ (¬ p5085) ∨ (¬ p3201) ∨ (¬ p5086) ∨ (¬ p5087))) := by
  classical
  tauto

theorem initial13022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3201) ∨ (meaning t m 6005) := by
  exact rule13022 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule13023 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p5086) ∨ (((¬ p3658) ∨ (¬ p5085) ∨ (¬ p3201) ∨ (¬ p5086) ∨ (¬ p5087))) := by
  classical
  tauto

theorem initial13023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5086) ∨ (meaning t m 6005) := by
  exact rule13023 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule13024 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p5087) ∨ (((¬ p3658) ∨ (¬ p5085) ∨ (¬ p3201) ∨ (¬ p5086) ∨ (¬ p5087))) := by
  classical
  tauto

theorem initial13024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5087) ∨ (meaning t m 6005) := by
  exact rule13024 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule13028 (p6004 p6005 : Prop) : (¬ ((¬ p6004) ∨ (¬ p6005))) ∨ (¬ p6004) ∨ (¬ p6005) := by
  classical
  tauto

theorem initial13028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6003)) ∨ (¬ (meaning t m 6004)) ∨ (¬ (meaning t m 6005)) := by
  exact rule13028 (meaning t m 6004) (meaning t m 6005)

theorem rule13029 (p5080 p6003 : Prop) (h : (p5080 ↔ p6003)) : (¬ p5080) ∨ (p6003) := by
  classical
  tauto

theorem initial13029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5080)) ∨ (meaning t m 6003) := by
  have source := ElevenTheory.theory3342 t (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule13029 (meaning t m 5080) (meaning t m 6003) source

theorem rule13031 (p1976 p2027 p2766 p3055 p3644 p3876 p4348 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3876) ∨ (¬ p3644) ∨ (¬ p1976) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial13031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3343 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13031 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) (meaning t m 4348) source

theorem rule13032 (p1976 p2027 p2138 p2459 p2633 p3692 p3694 : Prop) (h : (¬ p1976) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3692) ∨ (¬ p2459) ∨ p2633) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial13032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory3344 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule13032 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2459) (meaning t m 2633) (meaning t m 3692) (meaning t m 3694) source

theorem rule13033 (p2220 p2533 p4323 p4380 : Prop) (h : (¬ p2220) ∨ (¬ p4323) ∨ (¬ p4380) ∨ (¬ p2533)) : (¬ p2220) ∨ (¬ p2533) ∨ (¬ p4323) ∨ (¬ p4380) := by
  classical
  tauto

theorem initial13033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 4323)) ∨ (¬ (meaning t m 4380)) := by
  have source := ElevenTheory.theory3345 (m.theta 0 5) (m.theta 0 9) (m.theta 5 8) (m.theta 5 9)
  exact rule13033 (meaning t m 2220) (meaning t m 2533) (meaning t m 4323) (meaning t m 4380) source

theorem rule13040 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p4209) ∨ (((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4209) ∨ (meaning t m 6008) := by
  exact rule13040 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13041 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p4207) ∨ (((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4207) ∨ (meaning t m 6008) := by
  exact rule13041 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13042 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p3212) ∨ (((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3212) ∨ (meaning t m 6008) := by
  exact rule13042 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13043 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p5093) ∨ (((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5093) ∨ (meaning t m 6008) := by
  exact rule13043 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13044 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p5094) ∨ (((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5094) ∨ (meaning t m 6008) := by
  exact rule13044 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13045 (p3212 p4207 p4209 p5093 p5094 : Prop) : (¬ p3212) ∨ (¬ p4207) ∨ (¬ p4209) ∨ (¬ p5093) ∨ (¬ p5094) ∨ (¬ ((¬ p4209) ∨ (¬ p4207) ∨ (¬ p3212) ∨ (¬ p5093) ∨ (¬ p5094))) := by
  classical
  tauto

theorem initial13045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4209)) ∨ (¬ (meaning t m 5093)) ∨ (¬ (meaning t m 5094)) ∨ (¬ (meaning t m 6008)) := by
  exact rule13045 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule13052 (p1996 p2027 p2427 p2765 p3246 p3947 p4110 : Prop) (h : (¬ p4110) ∨ p2765 ∨ p2027 ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p1996) ∨ (¬ p2427)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3348 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule13052 (meaning t m 1996) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3246) (meaning t m 3947) (meaning t m 4110) source

theorem rule13053 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4382) ∨ (((¬ p4382) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p5102) ∨ (¬ p4395))) := by
  classical
  tauto

theorem initial13053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4382) ∨ (meaning t m 6010) := by
  exact rule13053 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule13054 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p3690) ∨ (((¬ p4382) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p5102) ∨ (¬ p4395))) := by
  classical
  tauto

theorem initial13054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3690) ∨ (meaning t m 6010) := by
  exact rule13054 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule13055 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4402) ∨ (((¬ p4382) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p5102) ∨ (¬ p4395))) := by
  classical
  tauto

theorem initial13055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4402) ∨ (meaning t m 6010) := by
  exact rule13055 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule13056 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p5102) ∨ (((¬ p4382) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p5102) ∨ (¬ p4395))) := by
  classical
  tauto

theorem initial13056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5102) ∨ (meaning t m 6010) := by
  exact rule13056 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule13057 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4395) ∨ (((¬ p4382) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p5102) ∨ (¬ p4395))) := by
  classical
  tauto

theorem initial13057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4395) ∨ (meaning t m 6010) := by
  exact rule13057 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule13059 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p4135) ∨ (((¬ p4135) ∨ (¬ p4192) ∨ (¬ p3246) ∨ (¬ p5104) ∨ (¬ p3951))) := by
  classical
  tauto

theorem initial13059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4135) ∨ (meaning t m 6011) := by
  exact rule13059 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule13060 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p4192) ∨ (((¬ p4135) ∨ (¬ p4192) ∨ (¬ p3246) ∨ (¬ p5104) ∨ (¬ p3951))) := by
  classical
  tauto

theorem initial13060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4192) ∨ (meaning t m 6011) := by
  exact rule13060 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule13061 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p3246) ∨ (((¬ p4135) ∨ (¬ p4192) ∨ (¬ p3246) ∨ (¬ p5104) ∨ (¬ p3951))) := by
  classical
  tauto

theorem initial13061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3246) ∨ (meaning t m 6011) := by
  exact rule13061 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule13062 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p5104) ∨ (((¬ p4135) ∨ (¬ p4192) ∨ (¬ p3246) ∨ (¬ p5104) ∨ (¬ p3951))) := by
  classical
  tauto

theorem initial13062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5104) ∨ (meaning t m 6011) := by
  exact rule13062 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule13067 (p6010 p6011 : Prop) : (¬ ((¬ p6010) ∨ (¬ p6011))) ∨ (¬ p6010) ∨ (¬ p6011) := by
  classical
  tauto

theorem initial13067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6009)) ∨ (¬ (meaning t m 6010)) ∨ (¬ (meaning t m 6011)) := by
  exact rule13067 (meaning t m 6010) (meaning t m 6011)

theorem rule13068 (p5100 p6009 : Prop) (h : (p5100 ↔ p6009)) : (¬ p5100) ∨ (p6009) := by
  classical
  tauto

theorem initial13068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5100)) ∨ (meaning t m 6009) := by
  have source := ElevenTheory.theory3349 t (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule13068 (meaning t m 5100) (meaning t m 6009) source

theorem rule13070 (p1997 p2914 p4235 p4647 : Prop) (h : (¬ p1997) ∨ p4647 ∨ (¬ p4235) ∨ p2914) : (¬ p1997) ∨ (p2914) ∨ (¬ p4235) ∨ (p4647) := by
  classical
  tauto

theorem initial13070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 4235)) ∨ (meaning t m 4647) := by
  have source := ElevenTheory.theory3350 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule13070 (meaning t m 1997) (meaning t m 2914) (meaning t m 4235) (meaning t m 4647) source

theorem rule13071 (p1982 p2027 p2177 p2459 p2699 p3093 p3309 : Prop) (h : p2699 ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p2177)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial13071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory3351 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13071 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2459) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) source

theorem rule13072 (p1998 p2027 p2470 p2528 p2579 p3008 p4348 : Prop) (h : p2027 ∨ p3008 ∨ (¬ p4348) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2528) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (p3008) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial13072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3352 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule13072 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2579) (meaning t m 3008) (meaning t m 4348) source

theorem rule13073 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p5107) ∨ (((¬ p5107) ∨ (¬ p4118) ∨ (¬ p4349) ∨ (¬ p5108) ∨ (¬ p5109))) := by
  classical
  tauto

theorem initial13073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5107) ∨ (meaning t m 6013) := by
  exact rule13073 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule13074 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p4118) ∨ (((¬ p5107) ∨ (¬ p4118) ∨ (¬ p4349) ∨ (¬ p5108) ∨ (¬ p5109))) := by
  classical
  tauto

theorem initial13074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4118) ∨ (meaning t m 6013) := by
  exact rule13074 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule13075 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p4349) ∨ (((¬ p5107) ∨ (¬ p4118) ∨ (¬ p4349) ∨ (¬ p5108) ∨ (¬ p5109))) := by
  classical
  tauto

theorem initial13075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4349) ∨ (meaning t m 6013) := by
  exact rule13075 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule13077 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p5109) ∨ (((¬ p5107) ∨ (¬ p4118) ∨ (¬ p4349) ∨ (¬ p5108) ∨ (¬ p5109))) := by
  classical
  tauto

theorem initial13077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5109) ∨ (meaning t m 6013) := by
  exact rule13077 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule13079 (p3256 p4350 p5111 p5112 p5113 : Prop) : (p4350) ∨ (((¬ p4350) ∨ (¬ p5111) ∨ (¬ p3256) ∨ (¬ p5112) ∨ (¬ p5113))) := by
  classical
  tauto

theorem initial13079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4350) ∨ (meaning t m 6014) := by
  exact rule13079 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule13080 (p3256 p4350 p5111 p5112 p5113 : Prop) : (p5111) ∨ (((¬ p4350) ∨ (¬ p5111) ∨ (¬ p3256) ∨ (¬ p5112) ∨ (¬ p5113))) := by
  classical
  tauto

theorem initial13080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5111) ∨ (meaning t m 6014) := by
  exact rule13080 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule13081 (p3256 p4350 p5111 p5112 p5113 : Prop) : (p3256) ∨ (((¬ p4350) ∨ (¬ p5111) ∨ (¬ p3256) ∨ (¬ p5112) ∨ (¬ p5113))) := by
  classical
  tauto

theorem initial13081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3256) ∨ (meaning t m 6014) := by
  exact rule13081 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule13087 (p6013 p6014 : Prop) : (¬ ((¬ p6013) ∨ (¬ p6014))) ∨ (¬ p6013) ∨ (¬ p6014) := by
  classical
  tauto

theorem initial13087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6012)) ∨ (¬ (meaning t m 6013)) ∨ (¬ (meaning t m 6014)) := by
  exact rule13087 (meaning t m 6013) (meaning t m 6014)

theorem rule13088 (p5105 p6012 : Prop) (h : (p5105 ↔ p6012)) : (¬ p5105) ∨ (p6012) := by
  classical
  tauto

theorem initial13088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5105)) ∨ (meaning t m 6012) := by
  have source := ElevenTheory.theory3353 t (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule13088 (meaning t m 5105) (meaning t m 6012) source

theorem rule13091 (p4444 p5116 p5117 p5118 p5119 : Prop) : (p5117) ∨ (((¬ p5117) ∨ (¬ p4444) ∨ (¬ p5116) ∨ (¬ p5118) ∨ (¬ p5119))) := by
  classical
  tauto

theorem initial13091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5117) ∨ (meaning t m 6016) := by
  exact rule13091 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule13092 (p4444 p5116 p5117 p5118 p5119 : Prop) : (p4444) ∨ (((¬ p5117) ∨ (¬ p4444) ∨ (¬ p5116) ∨ (¬ p5118) ∨ (¬ p5119))) := by
  classical
  tauto

theorem initial13092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4444) ∨ (meaning t m 6016) := by
  exact rule13092 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule13093 (p4444 p5116 p5117 p5118 p5119 : Prop) : (p5116) ∨ (((¬ p5117) ∨ (¬ p4444) ∨ (¬ p5116) ∨ (¬ p5118) ∨ (¬ p5119))) := by
  classical
  tauto

theorem initial13093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5116) ∨ (meaning t m 6016) := by
  exact rule13093 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule13095 (p4444 p5116 p5117 p5118 p5119 : Prop) : (p5119) ∨ (((¬ p5117) ∨ (¬ p4444) ∨ (¬ p5116) ∨ (¬ p5118) ∨ (¬ p5119))) := by
  classical
  tauto

theorem initial13095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5119) ∨ (meaning t m 6016) := by
  exact rule13095 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule13097 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p5121) ∨ (((¬ p5121) ∨ (¬ p4200) ∨ (¬ p3266) ∨ (¬ p5122) ∨ (¬ p5123))) := by
  classical
  tauto

theorem initial13097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5121) ∨ (meaning t m 6017) := by
  exact rule13097 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule13098 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p4200) ∨ (((¬ p5121) ∨ (¬ p4200) ∨ (¬ p3266) ∨ (¬ p5122) ∨ (¬ p5123))) := by
  classical
  tauto

theorem initial13098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4200) ∨ (meaning t m 6017) := by
  exact rule13098 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule13099 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p3266) ∨ (((¬ p5121) ∨ (¬ p4200) ∨ (¬ p3266) ∨ (¬ p5122) ∨ (¬ p5123))) := by
  classical
  tauto

theorem initial13099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3266) ∨ (meaning t m 6017) := by
  exact rule13099 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule13101 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p5123) ∨ (((¬ p5121) ∨ (¬ p4200) ∨ (¬ p3266) ∨ (¬ p5122) ∨ (¬ p5123))) := by
  classical
  tauto

theorem initial13101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5123) ∨ (meaning t m 6017) := by
  exact rule13101 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule13105 (p6016 p6017 : Prop) : (¬ ((¬ p6016) ∨ (¬ p6017))) ∨ (¬ p6016) ∨ (¬ p6017) := by
  classical
  tauto

theorem initial13105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6015)) ∨ (¬ (meaning t m 6016)) ∨ (¬ (meaning t m 6017)) := by
  exact rule13105 (meaning t m 6016) (meaning t m 6017)

theorem rule13106 (p5114 p6015 : Prop) (h : (p5114 ↔ p6015)) : (¬ p5114) ∨ (p6015) := by
  classical
  tauto

theorem initial13106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5114)) ∨ (meaning t m 6015) := by
  have source := ElevenTheory.theory3355 t (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule13106 (meaning t m 5114) (meaning t m 6015) source

theorem rule13108 (p4425 p5126 p5127 p5128 p5129 : Prop) : (p5127) ∨ (((¬ p5127) ∨ (¬ p4425) ∨ (¬ p5126) ∨ (¬ p5128) ∨ (¬ p5129))) := by
  classical
  tauto

theorem initial13108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5127) ∨ (meaning t m 6019) := by
  exact rule13108 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule13109 (p4425 p5126 p5127 p5128 p5129 : Prop) : (p4425) ∨ (((¬ p5127) ∨ (¬ p4425) ∨ (¬ p5126) ∨ (¬ p5128) ∨ (¬ p5129))) := by
  classical
  tauto

theorem initial13109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4425) ∨ (meaning t m 6019) := by
  exact rule13109 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule13110 (p4425 p5126 p5127 p5128 p5129 : Prop) : (p5126) ∨ (((¬ p5127) ∨ (¬ p4425) ∨ (¬ p5126) ∨ (¬ p5128) ∨ (¬ p5129))) := by
  classical
  tauto

theorem initial13110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5126) ∨ (meaning t m 6019) := by
  exact rule13110 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule13112 (p4425 p5126 p5127 p5128 p5129 : Prop) : (p5129) ∨ (((¬ p5127) ∨ (¬ p4425) ∨ (¬ p5126) ∨ (¬ p5128) ∨ (¬ p5129))) := by
  classical
  tauto

theorem initial13112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5129) ∨ (meaning t m 6019) := by
  exact rule13112 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule13114 (p3276 p4184 p5131 p5132 p5133 : Prop) : (p5131) ∨ (((¬ p5131) ∨ (¬ p4184) ∨ (¬ p3276) ∨ (¬ p5132) ∨ (¬ p5133))) := by
  classical
  tauto

theorem initial13114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5131) ∨ (meaning t m 6020) := by
  exact rule13114 (meaning t m 3276) (meaning t m 4184) (meaning t m 5131) (meaning t m 5132) (meaning t m 5133)

theorem rule13115 (p3276 p4184 p5131 p5132 p5133 : Prop) : (p4184) ∨ (((¬ p5131) ∨ (¬ p4184) ∨ (¬ p3276) ∨ (¬ p5132) ∨ (¬ p5133))) := by
  classical
  tauto

theorem initial13115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4184) ∨ (meaning t m 6020) := by
  exact rule13115 (meaning t m 3276) (meaning t m 4184) (meaning t m 5131) (meaning t m 5132) (meaning t m 5133)

theorem rule13116 (p3276 p4184 p5131 p5132 p5133 : Prop) : (p3276) ∨ (((¬ p5131) ∨ (¬ p4184) ∨ (¬ p3276) ∨ (¬ p5132) ∨ (¬ p5133))) := by
  classical
  tauto

theorem initial13116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3276) ∨ (meaning t m 6020) := by
  exact rule13116 (meaning t m 3276) (meaning t m 4184) (meaning t m 5131) (meaning t m 5132) (meaning t m 5133)

theorem rule13118 (p3276 p4184 p5131 p5132 p5133 : Prop) : (p5133) ∨ (((¬ p5131) ∨ (¬ p4184) ∨ (¬ p3276) ∨ (¬ p5132) ∨ (¬ p5133))) := by
  classical
  tauto

theorem initial13118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5133) ∨ (meaning t m 6020) := by
  exact rule13118 (meaning t m 3276) (meaning t m 4184) (meaning t m 5131) (meaning t m 5132) (meaning t m 5133)

theorem rule13122 (p6019 p6020 : Prop) : (¬ ((¬ p6019) ∨ (¬ p6020))) ∨ (¬ p6019) ∨ (¬ p6020) := by
  classical
  tauto

theorem initial13122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6018)) ∨ (¬ (meaning t m 6019)) ∨ (¬ (meaning t m 6020)) := by
  exact rule13122 (meaning t m 6019) (meaning t m 6020)

theorem rule13123 (p5124 p6018 : Prop) (h : (p5124 ↔ p6018)) : (¬ p5124) ∨ (p6018) := by
  classical
  tauto

theorem initial13123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5124)) ∨ (meaning t m 6018) := by
  have source := ElevenTheory.theory3356 t (m.theta 4 10) (m.theta 4 9) (m.theta 9 10)
  exact rule13123 (meaning t m 5124) (meaning t m 6018) source

theorem rule13126 (p1992 p2027 p2651 p2741 p2766 p3172 p4111 p4118 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p2741) ∨ p2766 ∨ (¬ p4111) ∨ (¬ p2651) ∨ (¬ p4118) ∨ (¬ p3172)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p4111) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial13126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory3358 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule13126 (meaning t m 1992) (meaning t m 2027) (meaning t m 2651) (meaning t m 2741) (meaning t m 2766) (meaning t m 3172) (meaning t m 4111) (meaning t m 4118) source

theorem rule13127 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p4427) ∨ (((¬ p4427) ∨ (¬ p3549) ∨ (¬ p4105) ∨ (¬ p5141) ∨ (¬ p5142))) := by
  classical
  tauto

theorem initial13127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4427) ∨ (meaning t m 6022) := by
  exact rule13127 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule13128 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p3549) ∨ (((¬ p4427) ∨ (¬ p3549) ∨ (¬ p4105) ∨ (¬ p5141) ∨ (¬ p5142))) := by
  classical
  tauto

theorem initial13128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3549) ∨ (meaning t m 6022) := by
  exact rule13128 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule13129 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p4105) ∨ (((¬ p4427) ∨ (¬ p3549) ∨ (¬ p4105) ∨ (¬ p5141) ∨ (¬ p5142))) := by
  classical
  tauto

theorem initial13129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4105) ∨ (meaning t m 6022) := by
  exact rule13129 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule13131 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p5142) ∨ (((¬ p4427) ∨ (¬ p3549) ∨ (¬ p4105) ∨ (¬ p5141) ∨ (¬ p5142))) := by
  classical
  tauto

theorem initial13131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5142) ∨ (meaning t m 6022) := by
  exact rule13131 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule13133 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p3547) ∨ (((¬ p3547) ∨ (¬ p4452) ∨ (¬ p3309) ∨ (¬ p5144) ∨ (¬ p5145))) := by
  classical
  tauto

theorem initial13133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3547) ∨ (meaning t m 6023) := by
  exact rule13133 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule13134 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p4452) ∨ (((¬ p3547) ∨ (¬ p4452) ∨ (¬ p3309) ∨ (¬ p5144) ∨ (¬ p5145))) := by
  classical
  tauto

theorem initial13134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4452) ∨ (meaning t m 6023) := by
  exact rule13134 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule13135 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p3309) ∨ (((¬ p3547) ∨ (¬ p4452) ∨ (¬ p3309) ∨ (¬ p5144) ∨ (¬ p5145))) := by
  classical
  tauto

theorem initial13135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3309) ∨ (meaning t m 6023) := by
  exact rule13135 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule13137 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p5145) ∨ (((¬ p3547) ∨ (¬ p4452) ∨ (¬ p3309) ∨ (¬ p5144) ∨ (¬ p5145))) := by
  classical
  tauto

theorem initial13137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5145) ∨ (meaning t m 6023) := by
  exact rule13137 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule13141 (p6022 p6023 : Prop) : (¬ ((¬ p6022) ∨ (¬ p6023))) ∨ (¬ p6022) ∨ (¬ p6023) := by
  classical
  tauto

theorem initial13141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6021)) ∨ (¬ (meaning t m 6022)) ∨ (¬ (meaning t m 6023)) := by
  exact rule13141 (meaning t m 6022) (meaning t m 6023)

theorem rule13142 (p5139 p6021 : Prop) (h : (p5139 ↔ p6021)) : (¬ p5139) ∨ (p6021) := by
  classical
  tauto

theorem initial13142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5139)) ∨ (meaning t m 6021) := by
  have source := ElevenTheory.theory3359 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 7)
  exact rule13142 (meaning t m 5139) (meaning t m 6021) source

theorem rule13144 (p4026 p4430 p5148 p5149 p5150 : Prop) : (p5148) ∨ (((¬ p5148) ∨ (¬ p4026) ∨ (¬ p4430) ∨ (¬ p5149) ∨ (¬ p5150))) := by
  classical
  tauto

theorem initial13144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5148) ∨ (meaning t m 6025) := by
  exact rule13144 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule13145 (p4026 p4430 p5148 p5149 p5150 : Prop) : (p4026) ∨ (((¬ p5148) ∨ (¬ p4026) ∨ (¬ p4430) ∨ (¬ p5149) ∨ (¬ p5150))) := by
  classical
  tauto

theorem initial13145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4026) ∨ (meaning t m 6025) := by
  exact rule13145 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule13146 (p4026 p4430 p5148 p5149 p5150 : Prop) : (p4430) ∨ (((¬ p5148) ∨ (¬ p4026) ∨ (¬ p4430) ∨ (¬ p5149) ∨ (¬ p5150))) := by
  classical
  tauto

theorem initial13146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4430) ∨ (meaning t m 6025) := by
  exact rule13146 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule13150 (p3319 p5152 p5153 p5154 p5155 : Prop) : (p5152) ∨ (((¬ p5152) ∨ (¬ p5153) ∨ (¬ p3319) ∨ (¬ p5154) ∨ (¬ p5155))) := by
  classical
  tauto

theorem initial13150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5152) ∨ (meaning t m 6026) := by
  exact rule13150 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule13151 (p3319 p5152 p5153 p5154 p5155 : Prop) : (p5153) ∨ (((¬ p5152) ∨ (¬ p5153) ∨ (¬ p3319) ∨ (¬ p5154) ∨ (¬ p5155))) := by
  classical
  tauto

theorem initial13151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5153) ∨ (meaning t m 6026) := by
  exact rule13151 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule13152 (p3319 p5152 p5153 p5154 p5155 : Prop) : (p3319) ∨ (((¬ p5152) ∨ (¬ p5153) ∨ (¬ p3319) ∨ (¬ p5154) ∨ (¬ p5155))) := by
  classical
  tauto

theorem initial13152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3319) ∨ (meaning t m 6026) := by
  exact rule13152 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule13158 (p6025 p6026 : Prop) : (¬ ((¬ p6025) ∨ (¬ p6026))) ∨ (¬ p6025) ∨ (¬ p6026) := by
  classical
  tauto

theorem initial13158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6024)) ∨ (¬ (meaning t m 6025)) ∨ (¬ (meaning t m 6026)) := by
  exact rule13158 (meaning t m 6025) (meaning t m 6026)

theorem rule13159 (p5146 p6024 : Prop) (h : (p5146 ↔ p6024)) : (¬ p5146) ∨ (p6024) := by
  classical
  tauto

theorem initial13159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5146)) ∨ (meaning t m 6024) := by
  have source := ElevenTheory.theory3360 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 9)
  exact rule13159 (meaning t m 5146) (meaning t m 6024) source

theorem rule13161 (p1988 p2027 p2295 p2388 p2761 p3319 p3549 p4336 p4623 : Prop) (h : (¬ p1988) ∨ p2388 ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2295) ∨ (¬ p4336) ∨ (¬ p4623) ∨ (¬ p3549) ∨ (¬ p3319)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2295) ∨ (p2388) ∨ (¬ p2761) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p4336) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial13161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory3361 t (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule13161 (meaning t m 1988) (meaning t m 2027) (meaning t m 2295) (meaning t m 2388) (meaning t m 2761) (meaning t m 3319) (meaning t m 3549) (meaning t m 4336) (meaning t m 4623) source

theorem rule13163 (p5158 p5159 p5160 p5161 p5162 : Prop) : (p5160) ∨ (((¬ p5159) ∨ (¬ p5160) ∨ (¬ p5158) ∨ (¬ p5161) ∨ (¬ p5162))) := by
  classical
  tauto

theorem initial13163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5160) ∨ (meaning t m 6028) := by
  exact rule13163 (meaning t m 5158) (meaning t m 5159) (meaning t m 5160) (meaning t m 5161) (meaning t m 5162)

theorem rule13170 (p3333 p5164 p5165 p5166 p5167 : Prop) : (p3333) ∨ (((¬ p5164) ∨ (¬ p5165) ∨ (¬ p3333) ∨ (¬ p5166) ∨ (¬ p5167))) := by
  classical
  tauto

theorem initial13170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3333) ∨ (meaning t m 6029) := by
  exact rule13170 (meaning t m 3333) (meaning t m 5164) (meaning t m 5165) (meaning t m 5166) (meaning t m 5167)

theorem rule13176 (p6028 p6029 : Prop) : (¬ ((¬ p6028) ∨ (¬ p6029))) ∨ (¬ p6028) ∨ (¬ p6029) := by
  classical
  tauto

theorem initial13176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6027)) ∨ (¬ (meaning t m 6028)) ∨ (¬ (meaning t m 6029)) := by
  exact rule13176 (meaning t m 6028) (meaning t m 6029)

theorem rule13177 (p5156 p6027 : Prop) (h : (p5156 ↔ p6027)) : (¬ p5156) ∨ (p6027) := by
  classical
  tauto

theorem initial13177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5156)) ∨ (meaning t m 6027) := by
  have source := ElevenTheory.theory3362 t (m.theta 2 4) (m.theta 2 9) (m.theta 4 9)
  exact rule13177 (meaning t m 5156) (meaning t m 6027) source

theorem rule13179 (p3359 p5170 p5171 p5172 p5173 : Prop) : (p5171) ∨ (((¬ p5171) ∨ (¬ p3359) ∨ (¬ p5170) ∨ (¬ p5172) ∨ (¬ p5173))) := by
  classical
  tauto

theorem initial13179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5171) ∨ (meaning t m 6031) := by
  exact rule13179 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule13180 (p3359 p5170 p5171 p5172 p5173 : Prop) : (p3359) ∨ (((¬ p5171) ∨ (¬ p3359) ∨ (¬ p5170) ∨ (¬ p5172) ∨ (¬ p5173))) := by
  classical
  tauto

theorem initial13180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3359) ∨ (meaning t m 6031) := by
  exact rule13180 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule13181 (p3359 p5170 p5171 p5172 p5173 : Prop) : (p5170) ∨ (((¬ p5171) ∨ (¬ p3359) ∨ (¬ p5170) ∨ (¬ p5172) ∨ (¬ p5173))) := by
  classical
  tauto

theorem initial13181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5170) ∨ (meaning t m 6031) := by
  exact rule13181 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule13182 (p3359 p5170 p5171 p5172 p5173 : Prop) : (p5172) ∨ (((¬ p5171) ∨ (¬ p3359) ∨ (¬ p5170) ∨ (¬ p5172) ∨ (¬ p5173))) := by
  classical
  tauto

theorem initial13182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5172) ∨ (meaning t m 6031) := by
  exact rule13182 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule13185 (p3343 p5175 p5176 p5177 p5178 : Prop) : (p5175) ∨ (((¬ p5175) ∨ (¬ p5176) ∨ (¬ p3343) ∨ (¬ p5177) ∨ (¬ p5178))) := by
  classical
  tauto

theorem initial13185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5175) ∨ (meaning t m 6032) := by
  exact rule13185 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule13186 (p3343 p5175 p5176 p5177 p5178 : Prop) : (p5176) ∨ (((¬ p5175) ∨ (¬ p5176) ∨ (¬ p3343) ∨ (¬ p5177) ∨ (¬ p5178))) := by
  classical
  tauto

theorem initial13186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5176) ∨ (meaning t m 6032) := by
  exact rule13186 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule13187 (p3343 p5175 p5176 p5177 p5178 : Prop) : (p3343) ∨ (((¬ p5175) ∨ (¬ p5176) ∨ (¬ p3343) ∨ (¬ p5177) ∨ (¬ p5178))) := by
  classical
  tauto

theorem initial13187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3343) ∨ (meaning t m 6032) := by
  exact rule13187 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule13188 (p3343 p5175 p5176 p5177 p5178 : Prop) : (p5177) ∨ (((¬ p5175) ∨ (¬ p5176) ∨ (¬ p3343) ∨ (¬ p5177) ∨ (¬ p5178))) := by
  classical
  tauto

theorem initial13188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5177) ∨ (meaning t m 6032) := by
  exact rule13188 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule13193 (p6031 p6032 : Prop) : (¬ ((¬ p6031) ∨ (¬ p6032))) ∨ (¬ p6031) ∨ (¬ p6032) := by
  classical
  tauto

theorem initial13193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6030)) ∨ (¬ (meaning t m 6031)) ∨ (¬ (meaning t m 6032)) := by
  exact rule13193 (meaning t m 6031) (meaning t m 6032)

theorem rule13194 (p5168 p6030 : Prop) (h : (p5168 ↔ p6030)) : (¬ p5168) ∨ (p6030) := by
  classical
  tauto

theorem initial13194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5168)) ∨ (meaning t m 6030) := by
  have source := ElevenTheory.theory3363 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 9)
  exact rule13194 (meaning t m 5168) (meaning t m 6030) source

theorem rule13198 (p3346 p5181 p5182 p5183 p5184 : Prop) : (p3346) ∨ (((¬ p5181) ∨ (¬ p5182) ∨ (¬ p3346) ∨ (¬ p5183) ∨ (¬ p5184))) := by
  classical
  tauto

theorem initial13198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3346) ∨ (meaning t m 6034) := by
  exact rule13198 (meaning t m 3346) (meaning t m 5181) (meaning t m 5182) (meaning t m 5183) (meaning t m 5184)

theorem rule13205 (p3355 p4263 p4264 p5186 p5187 : Prop) : (p3355) ∨ (((¬ p5186) ∨ (¬ p5187) ∨ (¬ p4264) ∨ (¬ p3355) ∨ (¬ p4263))) := by
  classical
  tauto

theorem initial13205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3355) ∨ (meaning t m 6035) := by
  exact rule13205 (meaning t m 3355) (meaning t m 4263) (meaning t m 4264) (meaning t m 5186) (meaning t m 5187)

theorem rule13210 (p6034 p6035 : Prop) : (¬ ((¬ p6034) ∨ (¬ p6035))) ∨ (¬ p6034) ∨ (¬ p6035) := by
  classical
  tauto

theorem initial13210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6033)) ∨ (¬ (meaning t m 6034)) ∨ (¬ (meaning t m 6035)) := by
  exact rule13210 (meaning t m 6034) (meaning t m 6035)

theorem rule13211 (p5179 p6033 : Prop) (h : (p5179 ↔ p6033)) : (¬ p5179) ∨ (p6033) := by
  classical
  tauto

theorem initial13211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5179)) ∨ (meaning t m 6033) := by
  have source := ElevenTheory.theory3364 t (m.theta 0 4) (m.theta 0 9) (m.theta 4 9)
  exact rule13211 (meaning t m 5179) (meaning t m 6033) source

theorem rule13213 (p1981 p2027 p2388 p2952 p3166 p3256 p4347 : Prop) (h : (¬ p1981) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3256)) : (¬ p1981) ∨ (p2027) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3365 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule13213 (meaning t m 1981) (meaning t m 2027) (meaning t m 2388) (meaning t m 2952) (meaning t m 3166) (meaning t m 3256) (meaning t m 4347) source

theorem rule13214 (p2252 p2952 p4282 p4365 : Prop) (h : (¬ p4365) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p4282)) : (¬ p2252) ∨ (¬ p2952) ∨ (¬ p4282) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial13214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory3366 (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5)
  exact rule13214 (meaning t m 2252) (meaning t m 2952) (meaning t m 4282) (meaning t m 4365) source

theorem rule13215 (p1984 p2688 p2744 p3954 : Prop) (h : p2688 ∨ (¬ p1984) ∨ (¬ p3954) ∨ p2744) : (¬ p1984) ∨ (p2688) ∨ (p2744) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial13215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2688) ∨ (meaning t m 2744) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory3367 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule13215 (meaning t m 1984) (meaning t m 2688) (meaning t m 2744) (meaning t m 3954) source

theorem rule13216 (p1994 p2027 p2388 p2641 p2651 p2963 p3662 : Prop) (h : (¬ p2963) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2651) ∨ p2388 ∨ (¬ p3662)) : (¬ p1994) ∨ (p2027) ∨ (p2388) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3368 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule13216 (meaning t m 1994) (meaning t m 2027) (meaning t m 2388) (meaning t m 2641) (meaning t m 2651) (meaning t m 2963) (meaning t m 3662) source

theorem rule13217 (p1983 p2027 p2274 p2284 p2396 p2688 p2992 : Prop) (h : (¬ p2274) ∨ (¬ p2284) ∨ p2688 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2396) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2396) ∨ (p2688) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial13217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory3369 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule13217 (meaning t m 1983) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2396) (meaning t m 2688) (meaning t m 2992) source

theorem rule13218 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p3519) ∨ (((¬ p3519) ∨ (¬ p3452) ∨ (¬ p5191) ∨ (¬ p5190) ∨ (¬ p4108))) := by
  classical
  tauto

theorem initial13218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3519) ∨ (meaning t m 6037) := by
  exact rule13218 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule13219 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p3452) ∨ (((¬ p3519) ∨ (¬ p3452) ∨ (¬ p5191) ∨ (¬ p5190) ∨ (¬ p4108))) := by
  classical
  tauto

theorem initial13219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3452) ∨ (meaning t m 6037) := by
  exact rule13219 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule13220 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p5191) ∨ (((¬ p3519) ∨ (¬ p3452) ∨ (¬ p5191) ∨ (¬ p5190) ∨ (¬ p4108))) := by
  classical
  tauto

theorem initial13220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5191) ∨ (meaning t m 6037) := by
  exact rule13220 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule13222 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p4108) ∨ (((¬ p3519) ∨ (¬ p3452) ∨ (¬ p5191) ∨ (¬ p5190) ∨ (¬ p4108))) := by
  classical
  tauto

theorem initial13222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4108) ∨ (meaning t m 6037) := by
  exact rule13222 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule13224 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p3347) ∨ (((¬ p3347) ∨ (¬ p4079) ∨ (¬ p5193) ∨ (¬ p3379) ∨ (¬ p5194))) := by
  classical
  tauto

theorem initial13224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3347) ∨ (meaning t m 6038) := by
  exact rule13224 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule13225 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p4079) ∨ (((¬ p3347) ∨ (¬ p4079) ∨ (¬ p5193) ∨ (¬ p3379) ∨ (¬ p5194))) := by
  classical
  tauto

theorem initial13225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4079) ∨ (meaning t m 6038) := by
  exact rule13225 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule13227 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p3379) ∨ (((¬ p3347) ∨ (¬ p4079) ∨ (¬ p5193) ∨ (¬ p3379) ∨ (¬ p5194))) := by
  classical
  tauto

theorem initial13227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3379) ∨ (meaning t m 6038) := by
  exact rule13227 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule13232 (p6037 p6038 : Prop) : (¬ ((¬ p6037) ∨ (¬ p6038))) ∨ (¬ p6037) ∨ (¬ p6038) := by
  classical
  tauto

theorem initial13232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6036)) ∨ (¬ (meaning t m 6037)) ∨ (¬ (meaning t m 6038)) := by
  exact rule13232 (meaning t m 6037) (meaning t m 6038)

theorem rule13233 (p5188 p6036 : Prop) (h : (p5188 ↔ p6036)) : (¬ p5188) ∨ (p6036) := by
  classical
  tauto

theorem initial13233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5188)) ∨ (meaning t m 6036) := by
  have source := ElevenTheory.theory3370 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule13233 (meaning t m 5188) (meaning t m 6036) source

theorem rule13236 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p3540) ∨ (((¬ p3540) ∨ (¬ p3575) ∨ (¬ p5197) ∨ (¬ p5199) ∨ (¬ p5198))) := by
  classical
  tauto

theorem initial13236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3540) ∨ (meaning t m 6040) := by
  exact rule13236 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule13237 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p3575) ∨ (((¬ p3540) ∨ (¬ p3575) ∨ (¬ p5197) ∨ (¬ p5199) ∨ (¬ p5198))) := by
  classical
  tauto

theorem initial13237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3575) ∨ (meaning t m 6040) := by
  exact rule13237 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule13238 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p5197) ∨ (((¬ p3540) ∨ (¬ p3575) ∨ (¬ p5197) ∨ (¬ p5199) ∨ (¬ p5198))) := by
  classical
  tauto

theorem initial13238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5197) ∨ (meaning t m 6040) := by
  exact rule13238 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule13239 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p5199) ∨ (((¬ p3540) ∨ (¬ p3575) ∨ (¬ p5197) ∨ (¬ p5199) ∨ (¬ p5198))) := by
  classical
  tauto

theorem initial13239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5199) ∨ (meaning t m 6040) := by
  exact rule13239 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule13243 (p3389 p4279 p5201 p5202 p5203 : Prop) : (p5201) ∨ (((¬ p5203) ∨ (¬ p5201) ∨ (¬ p3389) ∨ (¬ p5202) ∨ (¬ p4279))) := by
  classical
  tauto

theorem initial13243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5201) ∨ (meaning t m 6041) := by
  exact rule13243 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule13244 (p3389 p4279 p5201 p5202 p5203 : Prop) : (p3389) ∨ (((¬ p5203) ∨ (¬ p5201) ∨ (¬ p3389) ∨ (¬ p5202) ∨ (¬ p4279))) := by
  classical
  tauto

theorem initial13244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3389) ∨ (meaning t m 6041) := by
  exact rule13244 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule13246 (p3389 p4279 p5201 p5202 p5203 : Prop) : (p4279) ∨ (((¬ p5203) ∨ (¬ p5201) ∨ (¬ p3389) ∨ (¬ p5202) ∨ (¬ p4279))) := by
  classical
  tauto

theorem initial13246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4279) ∨ (meaning t m 6041) := by
  exact rule13246 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule13250 (p6040 p6041 : Prop) : (¬ ((¬ p6040) ∨ (¬ p6041))) ∨ (¬ p6040) ∨ (¬ p6041) := by
  classical
  tauto

theorem initial13250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6039)) ∨ (¬ (meaning t m 6040)) ∨ (¬ (meaning t m 6041)) := by
  exact rule13250 (meaning t m 6040) (meaning t m 6041)

theorem rule13251 (p5195 p6039 : Prop) (h : (p5195 ↔ p6039)) : (¬ p5195) ∨ (p6039) := by
  classical
  tauto

theorem initial13251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5195)) ∨ (meaning t m 6039) := by
  have source := ElevenTheory.theory3372 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7)
  exact rule13251 (meaning t m 5195) (meaning t m 6039) source

theorem rule13253 (p3543 p4366 p5206 p5207 p5208 : Prop) : (p5206) ∨ (((¬ p5206) ∨ (¬ p3543) ∨ (¬ p4366) ∨ (¬ p5207) ∨ (¬ p5208))) := by
  classical
  tauto

theorem initial13253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5206) ∨ (meaning t m 6043) := by
  exact rule13253 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule13254 (p3543 p4366 p5206 p5207 p5208 : Prop) : (p3543) ∨ (((¬ p5206) ∨ (¬ p3543) ∨ (¬ p4366) ∨ (¬ p5207) ∨ (¬ p5208))) := by
  classical
  tauto

theorem initial13254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3543) ∨ (meaning t m 6043) := by
  exact rule13254 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule13255 (p3543 p4366 p5206 p5207 p5208 : Prop) : (p4366) ∨ (((¬ p5206) ∨ (¬ p3543) ∨ (¬ p4366) ∨ (¬ p5207) ∨ (¬ p5208))) := by
  classical
  tauto

theorem initial13255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4366) ∨ (meaning t m 6043) := by
  exact rule13255 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule13259 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p5210) ∨ (((¬ p5210) ∨ (¬ p3399) ∨ (¬ p5211) ∨ (¬ p3546) ∨ (¬ p3545))) := by
  classical
  tauto

theorem initial13259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5210) ∨ (meaning t m 6044) := by
  exact rule13259 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule13260 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3399) ∨ (((¬ p5210) ∨ (¬ p3399) ∨ (¬ p5211) ∨ (¬ p3546) ∨ (¬ p3545))) := by
  classical
  tauto

theorem initial13260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3399) ∨ (meaning t m 6044) := by
  exact rule13260 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule13262 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3546) ∨ (((¬ p5210) ∨ (¬ p3399) ∨ (¬ p5211) ∨ (¬ p3546) ∨ (¬ p3545))) := by
  classical
  tauto

theorem initial13262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3546) ∨ (meaning t m 6044) := by
  exact rule13262 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule13263 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3545) ∨ (((¬ p5210) ∨ (¬ p3399) ∨ (¬ p5211) ∨ (¬ p3546) ∨ (¬ p3545))) := by
  classical
  tauto

theorem initial13263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3545) ∨ (meaning t m 6044) := by
  exact rule13263 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule13267 (p6043 p6044 : Prop) : (¬ ((¬ p6043) ∨ (¬ p6044))) ∨ (¬ p6043) ∨ (¬ p6044) := by
  classical
  tauto

theorem initial13267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6042)) ∨ (¬ (meaning t m 6043)) ∨ (¬ (meaning t m 6044)) := by
  exact rule13267 (meaning t m 6043) (meaning t m 6044)

theorem rule13268 (p5204 p6042 : Prop) (h : (p5204 ↔ p6042)) : (¬ p5204) ∨ (p6042) := by
  classical
  tauto

theorem initial13268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5204)) ∨ (meaning t m 6042) := by
  have source := ElevenTheory.theory3373 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 7)
  exact rule13268 (meaning t m 5204) (meaning t m 6042) source

theorem rule13270 (p1975 p2027 p2247 p2299 p2688 p3399 p3527 : Prop) (h : p2688 ∨ (¬ p3527) ∨ (¬ p3399) ∨ (¬ p2299) ∨ (¬ p1975) ∨ (¬ p2247) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (p2688) ∨ (¬ p3399) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial13270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory3374 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13270 (meaning t m 1975) (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2688) (meaning t m 3399) (meaning t m 3527) source

theorem rule13271 (p1975 p2027 p2114 p2299 p2717 p3399 p3576 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p2299) ∨ p2027 ∨ p2114 ∨ (¬ p3576) ∨ (¬ p3399) ∨ (¬ p1975) ∨ (¬ p2717)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial13271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory3375 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13271 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2299) (meaning t m 2717) (meaning t m 3399) (meaning t m 3576) (meaning t m 3954) source

theorem rule13273 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p3585) ∨ (((¬ p4376) ∨ (¬ p3585) ∨ (¬ p5214) ∨ (¬ p3590) ∨ (¬ p4257))) := by
  classical
  tauto

theorem initial13273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3585) ∨ (meaning t m 6046) := by
  exact rule13273 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule13275 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p3590) ∨ (((¬ p4376) ∨ (¬ p3585) ∨ (¬ p5214) ∨ (¬ p3590) ∨ (¬ p4257))) := by
  classical
  tauto

theorem initial13275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3590) ∨ (meaning t m 6046) := by
  exact rule13275 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule13276 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p4257) ∨ (((¬ p4376) ∨ (¬ p3585) ∨ (¬ p5214) ∨ (¬ p3590) ∨ (¬ p4257))) := by
  classical
  tauto

theorem initial13276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4257) ∨ (meaning t m 6046) := by
  exact rule13276 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule13278 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p5216) ∨ (((¬ p5216) ∨ (¬ p5217) ∨ (¬ p3367) ∨ (¬ p3541) ∨ (¬ p4030))) := by
  classical
  tauto

theorem initial13278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5216) ∨ (meaning t m 6047) := by
  exact rule13278 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule13280 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p3367) ∨ (((¬ p5216) ∨ (¬ p5217) ∨ (¬ p3367) ∨ (¬ p3541) ∨ (¬ p4030))) := by
  classical
  tauto

theorem initial13280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3367) ∨ (meaning t m 6047) := by
  exact rule13280 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule13281 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p3541) ∨ (((¬ p5216) ∨ (¬ p5217) ∨ (¬ p3367) ∨ (¬ p3541) ∨ (¬ p4030))) := by
  classical
  tauto

theorem initial13281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3541) ∨ (meaning t m 6047) := by
  exact rule13281 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule13282 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p4030) ∨ (((¬ p5216) ∨ (¬ p5217) ∨ (¬ p3367) ∨ (¬ p3541) ∨ (¬ p4030))) := by
  classical
  tauto

theorem initial13282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4030) ∨ (meaning t m 6047) := by
  exact rule13282 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule13286 (p6046 p6047 : Prop) : (¬ ((¬ p6046) ∨ (¬ p6047))) ∨ (¬ p6046) ∨ (¬ p6047) := by
  classical
  tauto

theorem initial13286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6045)) ∨ (¬ (meaning t m 6046)) ∨ (¬ (meaning t m 6047)) := by
  exact rule13286 (meaning t m 6046) (meaning t m 6047)

theorem rule13287 (p5212 p6045 : Prop) (h : (p5212 ↔ p6045)) : (¬ p5212) ∨ (p6045) := by
  classical
  tauto

theorem initial13287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5212)) ∨ (meaning t m 6045) := by
  have source := ElevenTheory.theory3376 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule13287 (meaning t m 5212) (meaning t m 6045) source

theorem rule13289 (p2027 p3379 p3585 p3954 p5214 : Prop) (h : (¬ p3954) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3379) ∨ (¬ p5214)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial13289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory3377 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule13289 (meaning t m 2027) (meaning t m 3379) (meaning t m 3585) (meaning t m 3954) (meaning t m 5214) source

theorem rule13290 (p3584 p4342 p5220 p5221 p5222 : Prop) : (p4342) ∨ (((¬ p4342) ∨ (¬ p3584) ∨ (¬ p5220) ∨ (¬ p5221) ∨ (¬ p5222))) := by
  classical
  tauto

theorem initial13290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4342) ∨ (meaning t m 6049) := by
  exact rule13290 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule13291 (p3584 p4342 p5220 p5221 p5222 : Prop) : (p3584) ∨ (((¬ p4342) ∨ (¬ p3584) ∨ (¬ p5220) ∨ (¬ p5221) ∨ (¬ p5222))) := by
  classical
  tauto

theorem initial13291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3584) ∨ (meaning t m 6049) := by
  exact rule13291 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule13292 (p3584 p4342 p5220 p5221 p5222 : Prop) : (p5220) ∨ (((¬ p4342) ∨ (¬ p3584) ∨ (¬ p5220) ∨ (¬ p5221) ∨ (¬ p5222))) := by
  classical
  tauto

theorem initial13292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5220) ∨ (meaning t m 6049) := by
  exact rule13292 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule13296 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p4390) ∨ (((¬ p4390) ∨ (¬ p4375) ∨ (¬ p3422) ∨ (¬ p5224) ∨ (¬ p5225))) := by
  classical
  tauto

theorem initial13296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4390) ∨ (meaning t m 6050) := by
  exact rule13296 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule13297 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p4375) ∨ (((¬ p4390) ∨ (¬ p4375) ∨ (¬ p3422) ∨ (¬ p5224) ∨ (¬ p5225))) := by
  classical
  tauto

theorem initial13297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4375) ∨ (meaning t m 6050) := by
  exact rule13297 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule13298 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p3422) ∨ (((¬ p4390) ∨ (¬ p4375) ∨ (¬ p3422) ∨ (¬ p5224) ∨ (¬ p5225))) := by
  classical
  tauto

theorem initial13298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3422) ∨ (meaning t m 6050) := by
  exact rule13298 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule13304 (p6049 p6050 : Prop) : (¬ ((¬ p6049) ∨ (¬ p6050))) ∨ (¬ p6049) ∨ (¬ p6050) := by
  classical
  tauto

theorem initial13304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6048)) ∨ (¬ (meaning t m 6049)) ∨ (¬ (meaning t m 6050)) := by
  exact rule13304 (meaning t m 6049) (meaning t m 6050)

theorem rule13305 (p5218 p6048 : Prop) (h : (p5218 ↔ p6048)) : (¬ p5218) ∨ (p6048) := by
  classical
  tauto

theorem initial13305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5218)) ∨ (meaning t m 6048) := by
  have source := ElevenTheory.theory3378 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule13305 (meaning t m 5218) (meaning t m 6048) source

theorem rule13307 (p1975 p2027 p2295 p2688 p2797 p3189 p3877 : Prop) (h : p2027 ∨ (¬ p2797) ∨ (¬ p1975) ∨ (¬ p3189) ∨ (¬ p3877) ∨ p2688 ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2688) ∨ (¬ p2797) ∨ (¬ p3189) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial13307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory3379 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule13307 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2688) (meaning t m 2797) (meaning t m 3189) (meaning t m 3877) source

theorem rule13308 (p1999 p2396 p2997 p4621 : Prop) (h : p2997 ∨ (¬ p1999) ∨ p4621 ∨ (¬ p2396)) : (¬ p1999) ∨ (¬ p2396) ∨ (p2997) ∨ (p4621) := by
  classical
  tauto

theorem initial13308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (meaning t m 4621) := by
  have source := ElevenTheory.theory3380 t (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule13308 (meaning t m 1999) (meaning t m 2396) (meaning t m 2997) (meaning t m 4621) source

theorem rule13309 (p1976 p2344 p2780 p2788 : Prop) (h : p2788 ∨ (¬ p1976) ∨ p2344 ∨ (¬ p2780)) : (¬ p1976) ∨ (p2344) ∨ (¬ p2780) ∨ (p2788) := by
  classical
  tauto

theorem initial13309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2788) := by
  have source := ElevenTheory.theory3381 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule13309 (meaning t m 1976) (meaning t m 2344) (meaning t m 2780) (meaning t m 2788) source

theorem rule13310 (p4324 p5228 p5229 p5230 p5231 : Prop) : (p5229) ∨ (((¬ p5229) ∨ (¬ p4324) ∨ (¬ p5228) ∨ (¬ p5230) ∨ (¬ p5231))) := by
  classical
  tauto

theorem initial13310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5229) ∨ (meaning t m 6052) := by
  exact rule13310 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule13311 (p4324 p5228 p5229 p5230 p5231 : Prop) : (p4324) ∨ (((¬ p5229) ∨ (¬ p4324) ∨ (¬ p5228) ∨ (¬ p5230) ∨ (¬ p5231))) := by
  classical
  tauto

theorem initial13311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4324) ∨ (meaning t m 6052) := by
  exact rule13311 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule13312 (p4324 p5228 p5229 p5230 p5231 : Prop) : (p5228) ∨ (((¬ p5229) ∨ (¬ p4324) ∨ (¬ p5228) ∨ (¬ p5230) ∨ (¬ p5231))) := by
  classical
  tauto

theorem initial13312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5228) ∨ (meaning t m 6052) := by
  exact rule13312 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule13316 (p3434 p5233 p5234 p5235 p5236 : Prop) : (p5233) ∨ (((¬ p5233) ∨ (¬ p5234) ∨ (¬ p3434) ∨ (¬ p5235) ∨ (¬ p5236))) := by
  classical
  tauto

theorem initial13316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5233) ∨ (meaning t m 6053) := by
  exact rule13316 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule13317 (p3434 p5233 p5234 p5235 p5236 : Prop) : (p5234) ∨ (((¬ p5233) ∨ (¬ p5234) ∨ (¬ p3434) ∨ (¬ p5235) ∨ (¬ p5236))) := by
  classical
  tauto

theorem initial13317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5234) ∨ (meaning t m 6053) := by
  exact rule13317 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule13318 (p3434 p5233 p5234 p5235 p5236 : Prop) : (p3434) ∨ (((¬ p5233) ∨ (¬ p5234) ∨ (¬ p3434) ∨ (¬ p5235) ∨ (¬ p5236))) := by
  classical
  tauto

theorem initial13318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3434) ∨ (meaning t m 6053) := by
  exact rule13318 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule13320 (p3434 p5233 p5234 p5235 p5236 : Prop) : (p5236) ∨ (((¬ p5233) ∨ (¬ p5234) ∨ (¬ p3434) ∨ (¬ p5235) ∨ (¬ p5236))) := by
  classical
  tauto

theorem initial13320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5236) ∨ (meaning t m 6053) := by
  exact rule13320 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule13324 (p6052 p6053 : Prop) : (¬ ((¬ p6052) ∨ (¬ p6053))) ∨ (¬ p6052) ∨ (¬ p6053) := by
  classical
  tauto

theorem initial13324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6051)) ∨ (¬ (meaning t m 6052)) ∨ (¬ (meaning t m 6053)) := by
  exact rule13324 (meaning t m 6052) (meaning t m 6053)

end SunPrize.SMT
