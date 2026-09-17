import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory042
import SunPrize.Certificate.Theory043
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule25039 (p2507 p3984 p4761 : Prop) (h : (¬ p2507) ∨ (¬ p3984) ∨ p4761) : (¬ p2507) ∨ (¬ p3984) ∨ (p4761) := by
  classical
  tauto

theorem initial25039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3984)) ∨ (meaning t m 4761) := by
  have source := ElevenTheory.theory14295 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 6)
  exact rule25039 (meaning t m 2507) (meaning t m 3984) (meaning t m 4761) source

theorem rule25040 (p2027 p2247 p2417 p2598 p3201 p3950 p4118 p4360 p4733 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p4118) ∨ (¬ p2598) ∨ (¬ p4360) ∨ (¬ p3201) ∨ (¬ p2247) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14296 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25040 (meaning t m 2027) (meaning t m 2247) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4733) source

theorem rule25041 (p2027 p3156 p3952 p3956 p3958 p4441 : Prop) (h : (¬ p3952) ∨ (¬ p3156) ∨ (¬ p4441) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p3956)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial25041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory14297 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule25041 (meaning t m 2027) (meaning t m 3156) (meaning t m 3952) (meaning t m 3956) (meaning t m 3958) (meaning t m 4441) source

theorem rule25043 (p1997 p2027 p2542 p2699 p3222 p3359 p3379 : Prop) (h : (¬ p3222) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p3359) ∨ (¬ p2542) ∨ (¬ p1997) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2699) ∨ (¬ p3222) ∨ (¬ p3359) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial25043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory14299 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule25043 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2699) (meaning t m 3222) (meaning t m 3359) (meaning t m 3379) source

theorem rule25045 (p2027 p2177 p2241 p2437 p2727 p3556 p3570 p4276 p4524 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p4276) ∨ (¬ p3570) ∨ (¬ p2437) ∨ (¬ p2241) ∨ (¬ p3556) ∨ (¬ p2727) ∨ (¬ p4524)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14301 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25045 (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2437) (meaning t m 2727) (meaning t m 3556) (meaning t m 3570) (meaning t m 4276) (meaning t m 4524) source

theorem rule25050 (p3773 p4191 p5379 : Prop) (h : (¬ p4191) ∨ (¬ p5379) ∨ p3773) : (p3773) ∨ (¬ p4191) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial25050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3773) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory14306 (m.theta 0 9) (m.theta 6 9) (m.theta 9 10)
  exact rule25050 (meaning t m 3773) (meaning t m 4191) (meaning t m 5379) source

theorem rule25053 (p2493 p2510 p2518 : Prop) (h : (¬ p2493) ∨ (¬ p2510) ∨ p2518) : (¬ p2493) ∨ (¬ p2510) ∨ (p2518) := by
  classical
  tauto

theorem initial25053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2510)) ∨ (meaning t m 2518) := by
  have source := ElevenTheory.theory14309 (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule25053 (meaning t m 2493) (meaning t m 2510) (meaning t m 2518) source

theorem rule25055 (p1994 p2230 p2323 p2440 p2663 p3879 p4705 : Prop) (h : p2323 ∨ (¬ p1994) ∨ (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2440) ∨ p4705 ∨ (¬ p3879)) : (¬ p1994) ∨ (¬ p2230) ∨ (p2323) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3879) ∨ (p4705) := by
  classical
  tauto

theorem initial25055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3879)) ∨ (meaning t m 4705) := by
  have source := ElevenTheory.theory14311 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule25055 (meaning t m 1994) (meaning t m 2230) (meaning t m 2323) (meaning t m 2440) (meaning t m 2663) (meaning t m 3879) (meaning t m 4705) source

theorem rule25059 (p1982 p2027 p2449 p2518 p2528 p2633 p3379 p3553 p3556 p3690 p4524 : Prop) (h : (¬ p2518) ∨ p2633 ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p1982) ∨ (¬ p2449) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p4524)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2633) ∨ (¬ p3379) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14315 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25059 (meaning t m 1982) (meaning t m 2027) (meaning t m 2449) (meaning t m 2518) (meaning t m 2528) (meaning t m 2633) (meaning t m 3379) (meaning t m 3553) (meaning t m 3556) (meaning t m 3690) (meaning t m 4524) source

theorem rule25060 (p2027 p2254 p2518 p2528 p2963 p3379 p3568 p4107 p4669 : Prop) (h : (¬ p2963) ∨ (¬ p2518) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4107) ∨ (¬ p2254) ∨ (¬ p3568) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14316 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25060 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 2963) (meaning t m 3379) (meaning t m 3568) (meaning t m 4107) (meaning t m 4669) source

theorem rule25061 (p2027 p2608 p2707 p3156 p3434 p3951 p4120 p4208 p4524 : Prop) (h : (¬ p3951) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4524) ∨ (¬ p2608) ∨ (¬ p4208) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3156) ∨ (¬ p3434) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14317 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule25061 (meaning t m 2027) (meaning t m 2608) (meaning t m 2707) (meaning t m 3156) (meaning t m 3434) (meaning t m 3951) (meaning t m 4120) (meaning t m 4208) (meaning t m 4524) source

theorem rule25062 (p2027 p2274 p2312 p2493 p2928 p3958 p4279 : Prop) (h : (¬ p2493) ∨ (¬ p4279) ∨ (¬ p3958) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2928) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3958) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial25062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory14318 t (m.theta 0 7) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule25062 (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 2493) (meaning t m 2928) (meaning t m 3958) (meaning t m 4279) source

theorem rule25065 (p2027 p2274 p2819 p3822 p3956 p3958 : Prop) (h : (¬ p3958) ∨ (¬ p2274) ∨ (¬ p3822) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2819)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3956) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial25065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory14321 t (m.theta 2 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25065 (meaning t m 2027) (meaning t m 2274) (meaning t m 2819) (meaning t m 3822) (meaning t m 3956) (meaning t m 3958) source

theorem rule25069 (p2027 p2122 p3367 p3549 p3953 p4426 p4752 : Prop) (h : (¬ p3953) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p3367) ∨ (¬ p4752) ∨ (¬ p3549) ∨ (¬ p4426)) : (p2027) ∨ (¬ p2122) ∨ (¬ p3367) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4426) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14325 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule25069 (meaning t m 2027) (meaning t m 2122) (meaning t m 3367) (meaning t m 3549) (meaning t m 3953) (meaning t m 4426) (meaning t m 4752) source

theorem rule25070 (p2027 p2870 p3367 p3486 p4313 p4752 p4874 : Prop) (h : (¬ p3367) ∨ (¬ p4752) ∨ (¬ p4874) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2870) ∨ (¬ p4313)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p4313) ∨ (¬ p4752) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory14326 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule25070 (meaning t m 2027) (meaning t m 2870) (meaning t m 3367) (meaning t m 3486) (meaning t m 4313) (meaning t m 4752) (meaning t m 4874) source

theorem rule25071 (p2027 p3051 p3568 p3646 p4140 p4564 : Prop) (h : (¬ p3646) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4140) ∨ (¬ p3568) ∨ (¬ p4564)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3568) ∨ (¬ p3646) ∨ (¬ p4140) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14327 t (m.theta 0 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule25071 (meaning t m 2027) (meaning t m 3051) (meaning t m 3568) (meaning t m 3646) (meaning t m 4140) (meaning t m 4564) source

theorem rule25072 (p2027 p3367 p3483 p3953 p4026 p4426 p4752 : Prop) (h : (¬ p3483) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p4426) ∨ (¬ p4026) ∨ (¬ p3953)) : (p2027) ∨ (¬ p3367) ∨ (¬ p3483) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p4426) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14328 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 9)
  exact rule25072 (meaning t m 2027) (meaning t m 3367) (meaning t m 3483) (meaning t m 3953) (meaning t m 4026) (meaning t m 4426) (meaning t m 4752) source

theorem rule25076 (p2027 p2241 p2427 p2641 p2668 p3556 p3880 p4134 p4524 : Prop) (h : p2027 ∨ (¬ p4134) ∨ (¬ p3880) ∨ (¬ p3556) ∨ (¬ p4524) ∨ (¬ p2241) ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2427) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14332 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule25076 (meaning t m 2027) (meaning t m 2241) (meaning t m 2427) (meaning t m 2641) (meaning t m 2668) (meaning t m 3556) (meaning t m 3880) (meaning t m 4134) (meaning t m 4524) source

theorem rule25078 (p2027 p2156 p2811 p2958 p3367 p4173 p4752 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p4752) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3367) ∨ (¬ p2958) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3367) ∨ (¬ p4173) ∨ (¬ p4752) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory14334 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 6)
  exact rule25078 (meaning t m 2027) (meaning t m 2156) (meaning t m 2811) (meaning t m 2958) (meaning t m 3367) (meaning t m 4173) (meaning t m 4752) (meaning t m 4874) source

theorem rule25079 (p2027 p2136 p2870 p3366 p3367 p3556 p4313 p4752 : Prop) (h : (¬ p3366) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p2136) ∨ (¬ p3556) ∨ (¬ p3367) ∨ (¬ p4313) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2870) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14335 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule25079 (meaning t m 2027) (meaning t m 2136) (meaning t m 2870) (meaning t m 3366) (meaning t m 3367) (meaning t m 3556) (meaning t m 4313) (meaning t m 4752) source

theorem rule25085 (p2027 p2138 p2363 p3063 p3093 p3690 p4244 p4669 p4736 : Prop) (h : (¬ p3063) ∨ (¬ p3690) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p4736) ∨ (¬ p2363) ∨ (¬ p4244) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14341 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25085 (meaning t m 2027) (meaning t m 2138) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4736) source

theorem rule25086 (p1976 p2027 p2766 p3266 p3365 p4035 p5284 : Prop) (h : (¬ p3365) ∨ p2766 ∨ (¬ p5284) ∨ (¬ p1976) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p4035)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial25086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory14342 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25086 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3365) (meaning t m 4035) (meaning t m 5284) source

theorem rule25091 (p2027 p2177 p2254 p2952 p3093 p3136 p3309 p3877 p4041 : Prop) (h : (¬ p2177) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p2254) ∨ (¬ p3136) ∨ (¬ p3093) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3309) ∨ (¬ p3877) ∨ (¬ p4041) := by
  classical
  tauto

theorem initial25091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) := by
  have source := ElevenTheory.theory14347 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule25091 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2952) (meaning t m 3093) (meaning t m 3136) (meaning t m 3309) (meaning t m 3877) (meaning t m 4041) source

theorem rule25093 (p1998 p2027 p2247 p2688 p3256 p3399 p4189 p4288 p4348 : Prop) (h : (¬ p4189) ∨ (¬ p4288) ∨ (¬ p3399) ∨ p2688 ∨ (¬ p4348) ∨ (¬ p3256) ∨ (¬ p2247) ∨ (¬ p1998) ∨ p2027) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3256) ∨ (¬ p3399) ∨ (¬ p4189) ∨ (¬ p4288) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial25093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory14349 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 1 8) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25093 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3256) (meaning t m 3399) (meaning t m 4189) (meaning t m 4288) (meaning t m 4348) source

theorem rule25096 (p2027 p2934 p3584 p3590 p3631 p3821 p4031 p4715 p4984 : Prop) (h : (¬ p4031) ∨ (¬ p3584) ∨ (¬ p4715) ∨ (¬ p2934) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p3821) ∨ (¬ p4984) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3584) ∨ (¬ p3590) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4031) ∨ (¬ p4715) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial25096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory14352 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 7 9)
  exact rule25096 (meaning t m 2027) (meaning t m 2934) (meaning t m 3584) (meaning t m 3590) (meaning t m 3631) (meaning t m 3821) (meaning t m 4031) (meaning t m 4715) (meaning t m 4984) source

theorem rule25097 (p2027 p2598 p2742 p3038 p3527 p3551 p3820 p4752 : Prop) (h : (¬ p2742) ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p3038) ∨ p2027 ∨ (¬ p3820) ∨ (¬ p3527) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14353 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 7 8)
  exact rule25097 (meaning t m 2027) (meaning t m 2598) (meaning t m 2742) (meaning t m 3038) (meaning t m 3527) (meaning t m 3551) (meaning t m 3820) (meaning t m 4752) source

theorem rule25100 (p3551 p4042 p4120 p4984 : Prop) (h : (¬ p4042) ∨ (¬ p3551) ∨ (¬ p4984) ∨ p4120) : (¬ p3551) ∨ (¬ p4042) ∨ (p4120) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial25100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4042)) ∨ (meaning t m 4120) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory14356 (m.theta 0 5) (m.theta 0 7) (m.theta 5 8) (m.theta 7 8)
  exact rule25100 (meaning t m 3551) (meaning t m 4042) (meaning t m 4120) (meaning t m 4984) source

theorem rule25101 (p1994 p2027 p2406 p2440 p2611 p2696 p2743 p3541 : Prop) (h : (¬ p2440) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p1994) ∨ p2611 ∨ (¬ p3541) ∨ (¬ p2696) ∨ (¬ p2743)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial25101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory14357 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule25101 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 3541) source

theorem rule25103 (p1998 p2027 p2323 p2449 p2807 p2911 p4278 : Prop) (h : (¬ p4278) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p1998) ∨ p2323 ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial25103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory14359 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25103 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2807) (meaning t m 2911) (meaning t m 4278) source

theorem rule25106 (p2027 p2881 p3516 p3551 p4277 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3516) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4277) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial25106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory14362 t (m.theta 0 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25106 (meaning t m 2027) (meaning t m 2881) (meaning t m 3516) (meaning t m 3551) (meaning t m 4277) (meaning t m 4278) source

theorem rule25108 (p3093 p3399 p4452 : Prop) (h : (¬ p4452) ∨ (¬ p3093) ∨ p3399) : (¬ p3093) ∨ (p3399) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial25108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (meaning t m 3399) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory14364 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule25108 (meaning t m 3093) (meaning t m 3399) (meaning t m 4452) source

theorem rule25111 (p3745 p3958 p4976 : Prop) (h : (¬ p3745) ∨ (¬ p3958) ∨ p4976) : (¬ p3745) ∨ (¬ p3958) ∨ (p4976) := by
  classical
  tauto

theorem initial25111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3958)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory14367 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6)
  exact rule25111 (meaning t m 3745) (meaning t m 3958) (meaning t m 4976) source

theorem rule25113 (p1975 p2027 p2287 p2553 p2630 p3016 p4195 : Prop) (h : p2287 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p4195)) : (¬ p1975) ∨ (p2027) ∨ (p2287) ∨ (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3016) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial25113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory14369 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule25113 (meaning t m 1975) (meaning t m 2027) (meaning t m 2287) (meaning t m 2553) (meaning t m 2630) (meaning t m 3016) (meaning t m 4195) source

theorem rule25115 (p2027 p3105 p3367 p4313 p4363 p4752 p4874 : Prop) (h : (¬ p4313) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p4363) ∨ (¬ p3367) ∨ (¬ p4874) ∨ (¬ p4752)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3367) ∨ (¬ p4313) ∨ (¬ p4363) ∨ (¬ p4752) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory14371 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 9)
  exact rule25115 (meaning t m 2027) (meaning t m 3105) (meaning t m 3367) (meaning t m 4313) (meaning t m 4363) (meaning t m 4752) (meaning t m 4874) source

theorem rule25118 (p2027 p2104 p2156 p2246 p2598 p2742 p2958 p3125 p3461 p4752 p5123 p5612 : Prop) (h : (¬ p2246) ∨ (¬ p3461) ∨ (¬ p5612) ∨ (¬ p2958) ∨ (¬ p2156) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2742) ∨ (¬ p4752) ∨ (¬ p2598) ∨ (¬ p2104) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2958) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4752) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial25118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory14374 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25118 (meaning t m 2027) (meaning t m 2104) (meaning t m 2156) (meaning t m 2246) (meaning t m 2598) (meaning t m 2742) (meaning t m 2958) (meaning t m 3125) (meaning t m 3461) (meaning t m 4752) (meaning t m 5123) (meaning t m 5612) source

theorem rule25119 (p2027 p2104 p2246 p2331 p2598 p2742 p3323 p3461 p4752 p5123 p5612 : Prop) (h : (¬ p2331) ∨ (¬ p2246) ∨ (¬ p2598) ∨ (¬ p2104) ∨ (¬ p3461) ∨ (¬ p2742) ∨ (¬ p4752) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p5612)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p4752) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial25119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory14375 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25119 (meaning t m 2027) (meaning t m 2104) (meaning t m 2246) (meaning t m 2331) (meaning t m 2598) (meaning t m 2742) (meaning t m 3323) (meaning t m 3461) (meaning t m 4752) (meaning t m 5123) (meaning t m 5612) source

theorem rule25121 (p2027 p2136 p2192 p2598 p2742 p3646 p4365 p4752 : Prop) (h : (¬ p4365) ∨ (¬ p2742) ∨ (¬ p2136) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p3646) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3646) ∨ (¬ p4365) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14377 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 6)
  exact rule25121 (meaning t m 2027) (meaning t m 2136) (meaning t m 2192) (meaning t m 2598) (meaning t m 2742) (meaning t m 3646) (meaning t m 4365) (meaning t m 4752) source

theorem rule25125 (p2027 p2104 p2246 p2449 p2598 p2742 p2761 p2807 p4752 p5123 p5612 : Prop) (h : (¬ p2246) ∨ (¬ p2742) ∨ (¬ p4752) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p5612) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p4752) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial25125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory14381 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25125 (meaning t m 2027) (meaning t m 2104) (meaning t m 2246) (meaning t m 2449) (meaning t m 2598) (meaning t m 2742) (meaning t m 2761) (meaning t m 2807) (meaning t m 4752) (meaning t m 5123) (meaning t m 5612) source

theorem rule25126 (p2027 p2493 p2743 p3541 p3584 p4752 : Prop) (h : (¬ p3541) ∨ (¬ p4752) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3584) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14382 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule25126 (meaning t m 2027) (meaning t m 2493) (meaning t m 2743) (meaning t m 3541) (meaning t m 3584) (meaning t m 4752) source

theorem rule25127 (p2027 p2743 p2780 p2829 p3362 p3363 p4752 : Prop) (h : (¬ p2743) ∨ (¬ p3362) ∨ (¬ p4752) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3362) ∨ (¬ p3363) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14383 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6)
  exact rule25127 (meaning t m 2027) (meaning t m 2743) (meaning t m 2780) (meaning t m 2829) (meaning t m 3362) (meaning t m 3363) (meaning t m 4752) source

theorem rule25131 (p2027 p2518 p2743 p3541 p3874 p4752 : Prop) (h : (¬ p2518) ∨ (¬ p2743) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3541)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3874) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14387 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 8)
  exact rule25131 (meaning t m 2027) (meaning t m 2518) (meaning t m 2743) (meaning t m 3541) (meaning t m 3874) (meaning t m 4752) source

theorem rule25132 (p2027 p2307 p2396 p2779 p2829 p3055 p3238 p3951 p4030 p4734 p4948 : Prop) (h : (¬ p2307) ∨ (¬ p3951) ∨ (¬ p2779) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p3238) ∨ (¬ p2396) ∨ (¬ p2829) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3951) ∨ (¬ p4030) ∨ (¬ p4734) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial25132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory14388 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule25132 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2779) (meaning t m 2829) (meaning t m 3055) (meaning t m 3238) (meaning t m 3951) (meaning t m 4030) (meaning t m 4734) (meaning t m 4948) source

theorem rule25133 (p2027 p2137 p2509 p2534 p2839 p3051 p3055 p3246 p3950 p4030 p4734 : Prop) (h : (¬ p3950) ∨ (¬ p2137) ∨ (¬ p3055) ∨ (¬ p3051) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p2509) ∨ (¬ p4734) ∨ (¬ p2534) ∨ (¬ p4030)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4030) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14389 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25133 (meaning t m 2027) (meaning t m 2137) (meaning t m 2509) (meaning t m 2534) (meaning t m 2839) (meaning t m 3051) (meaning t m 3055) (meaning t m 3246) (meaning t m 3950) (meaning t m 4030) (meaning t m 4734) source

theorem rule25134 (p1987 p2027 p2387 p2577 p2662 p2810 p3063 p3128 p4026 : Prop) (h : p3128 ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p2387) ∨ (¬ p4026) ∨ (¬ p2577) ∨ (¬ p1987) ∨ (¬ p2810) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3063) ∨ (p3128) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial25134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3063)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory14390 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 6 8) (m.theta 6 9)
  exact rule25134 (meaning t m 1987) (meaning t m 2027) (meaning t m 2387) (meaning t m 2577) (meaning t m 2662) (meaning t m 2810) (meaning t m 3063) (meaning t m 3128) (meaning t m 4026) source

theorem rule25135 (p2027 p2743 p2774 p3055 p3367 p4845 : Prop) (h : (¬ p2743) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p4845) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial25135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory14391 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6)
  exact rule25135 (meaning t m 2027) (meaning t m 2743) (meaning t m 2774) (meaning t m 3055) (meaning t m 3367) (meaning t m 4845) source

theorem rule25141 (p2027 p2166 p2210 p2254 p2657 p3146 p3742 p4278 p4669 : Prop) (h : (¬ p3742) ∨ (¬ p4278) ∨ (¬ p2254) ∨ (¬ p4669) ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14397 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25141 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 3146) (meaning t m 3742) (meaning t m 4278) (meaning t m 4669) source

theorem rule25142 (p2027 p2138 p2573 p3362 p3364 p3584 p5049 : Prop) (h : (¬ p3364) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p2138) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial25142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory14398 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule25142 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3362) (meaning t m 3364) (meaning t m 3584) (meaning t m 5049) source

theorem rule25144 (p2027 p2166 p2210 p2254 p2963 p3146 p3568 p4107 p4669 : Prop) (h : (¬ p4669) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2166) ∨ (¬ p4107) ∨ (¬ p3146) ∨ (¬ p2210) ∨ (¬ p2963) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3146) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14400 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25144 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2963) (meaning t m 3146) (meaning t m 3568) (meaning t m 4107) (meaning t m 4669) source

theorem rule25145 (p2027 p2191 p2619 p3367 p4313 p4752 p4874 : Prop) (h : (¬ p3367) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p4874) ∨ (¬ p4313) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p3367) ∨ (¬ p4313) ∨ (¬ p4752) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory14401 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule25145 (meaning t m 2027) (meaning t m 2191) (meaning t m 2619) (meaning t m 3367) (meaning t m 4313) (meaning t m 4752) (meaning t m 4874) source

theorem rule25148 (p3690 p4107 p4140 : Prop) (h : (¬ p3690) ∨ (¬ p4140) ∨ p4107) : (¬ p3690) ∨ (p4107) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial25148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3690)) ∨ (meaning t m 4107) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory14404 (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule25148 (meaning t m 3690) (meaning t m 4107) (meaning t m 4140) source

theorem rule25153 (p2027 p2254 p2363 p2657 p3063 p3093 p3742 p4278 p4669 : Prop) (h : (¬ p3093) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p3063) ∨ (¬ p4669) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14409 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25153 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2657) (meaning t m 3063) (meaning t m 3093) (meaning t m 3742) (meaning t m 4278) (meaning t m 4669) source

theorem rule25154 (p2027 p2274 p3016 p3325 p3958 p4256 p4432 : Prop) (h : (¬ p4256) ∨ (¬ p4432) ∨ (¬ p2274) ∨ (¬ p3958) ∨ (¬ p3325) ∨ (¬ p3016) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p3016) ∨ (¬ p3325) ∨ (¬ p3958) ∨ (¬ p4256) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial25154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory14410 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25154 (meaning t m 2027) (meaning t m 2274) (meaning t m 3016) (meaning t m 3325) (meaning t m 3958) (meaning t m 4256) (meaning t m 4432) source

theorem rule25155 (p2027 p2274 p2668 p3568 p3956 p3958 : Prop) (h : (¬ p3568) ∨ p2027 ∨ (¬ p3958) ∨ (¬ p2274) ∨ (¬ p3956) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3956) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial25155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory14411 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25155 (meaning t m 2027) (meaning t m 2274) (meaning t m 2668) (meaning t m 3568) (meaning t m 3956) (meaning t m 3958) source

theorem rule25158 (p2027 p3125 p3422 p3958 p4022 p5160 : Prop) (h : p2027 ∨ (¬ p5160) ∨ (¬ p3422) ∨ (¬ p3125) ∨ (¬ p4022) ∨ (¬ p3958)) : (p2027) ∨ (¬ p3125) ∨ (¬ p3422) ∨ (¬ p3958) ∨ (¬ p4022) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial25158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14414 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9)
  exact rule25158 (meaning t m 2027) (meaning t m 3125) (meaning t m 3422) (meaning t m 3958) (meaning t m 4022) (meaning t m 5160) source

theorem rule25163 (p2810 p4315 p4700 : Prop) (h : (¬ p4700) ∨ (¬ p2810) ∨ p4315) : (¬ p2810) ∨ (p4315) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial25163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (meaning t m 4315) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory14419 (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule25163 (meaning t m 2810) (meaning t m 4315) (meaning t m 4700) source

theorem rule25173 (p2027 p2144 p3051 p3365 p3486 p4030 p4202 p4752 : Prop) (h : (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3365) ∨ (¬ p4202) ∨ (¬ p4030) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p2144)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3486) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14429 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 7)
  exact rule25173 (meaning t m 2027) (meaning t m 2144) (meaning t m 3051) (meaning t m 3365) (meaning t m 3486) (meaning t m 4030) (meaning t m 4202) (meaning t m 4752) source

theorem rule25175 (p1980 p2027 p2622 p2774 p3309 p3365 p3568 p3918 : Prop) (h : p2622 ∨ (¬ p3568) ∨ (¬ p3309) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3918) ∨ (¬ p2774) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2027) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial25175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory14431 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule25175 (meaning t m 1980) (meaning t m 2027) (meaning t m 2622) (meaning t m 2774) (meaning t m 3309) (meaning t m 3365) (meaning t m 3568) (meaning t m 3918) source

theorem rule25180 (p2027 p2098 p2579 p2588 p3347 p3365 p3609 p4030 p4107 p4669 p4752 : Prop) (h : (¬ p3609) ∨ (¬ p2588) ∨ (¬ p4752) ∨ (¬ p2098) ∨ (¬ p4030) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4030) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14436 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25180 (meaning t m 2027) (meaning t m 2098) (meaning t m 2579) (meaning t m 2588) (meaning t m 3347) (meaning t m 3365) (meaning t m 3609) (meaning t m 4030) (meaning t m 4107) (meaning t m 4669) (meaning t m 4752) source

theorem rule25181 (p2027 p2156 p2542 p3096 p3574 p4539 : Prop) (h : (¬ p4539) ∨ (¬ p2156) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial25181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory14437 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule25181 (meaning t m 2027) (meaning t m 2156) (meaning t m 2542) (meaning t m 3096) (meaning t m 3574) (meaning t m 4539) source

theorem rule25182 (p2143 p4525 p4875 : Prop) (h : (¬ p2143) ∨ (¬ p4525) ∨ p4875) : (¬ p2143) ∨ (¬ p4525) ∨ (p4875) := by
  classical
  tauto

theorem initial25182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 4525)) ∨ (meaning t m 4875) := by
  have source := ElevenTheory.theory14438 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule25182 (meaning t m 2143) (meaning t m 4525) (meaning t m 4875) source

theorem rule25183 (p1998 p2027 p2542 p2545 p2589 p2881 p3389 p3569 : Prop) (h : (¬ p3569) ∨ (¬ p1998) ∨ p2545 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3389)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial25183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory14439 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule25183 (meaning t m 1998) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 2881) (meaning t m 3389) (meaning t m 3569) source

theorem rule25184 (p3543 p3817 p3821 : Prop) (h : (¬ p3817) ∨ (¬ p3543) ∨ p3821) : (¬ p3543) ∨ (¬ p3817) ∨ (p3821) := by
  classical
  tauto

theorem initial25184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3817)) ∨ (meaning t m 3821) := by
  have source := ElevenTheory.theory14440 (m.theta 0 7) (m.theta 1 7) (m.theta 7 9)
  exact rule25184 (meaning t m 3543) (meaning t m 3817) (meaning t m 3821) source

theorem rule25185 (p2027 p2470 p2528 p2780 p3367 p3759 p3822 p4107 p4669 p4734 : Prop) (h : (¬ p3759) ∨ (¬ p2470) ∨ (¬ p4734) ∨ (¬ p2780) ∨ (¬ p4107) ∨ (¬ p2528) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2780) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14441 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25185 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2780) (meaning t m 3367) (meaning t m 3759) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) (meaning t m 4734) source

theorem rule25188 (p2177 p2911 p3921 : Prop) (h : (¬ p2911) ∨ (¬ p3921) ∨ p2177) : (p2177) ∨ (¬ p2911) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial25188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory14444 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25188 (meaning t m 2177) (meaning t m 2911) (meaning t m 3921) source

theorem rule25190 (p2027 p2138 p2470 p2528 p3367 p3486 p3690 p3759 p4243 p4669 p4734 : Prop) (h : (¬ p4669) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4734) ∨ (¬ p3367) ∨ (¬ p3690) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p4243) ∨ (¬ p2138) ∨ (¬ p3759)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3690) ∨ (¬ p3759) ∨ (¬ p4243) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14446 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25190 (meaning t m 2027) (meaning t m 2138) (meaning t m 2470) (meaning t m 2528) (meaning t m 3367) (meaning t m 3486) (meaning t m 3690) (meaning t m 3759) (meaning t m 4243) (meaning t m 4669) (meaning t m 4734) source

theorem rule25191 (p2008 p2027 p2545 p3027 p3414 p3471 p4111 p4236 : Prop) (h : (¬ p3471) ∨ (¬ p2008) ∨ (¬ p4111) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4236) ∨ p2545) : (¬ p2008) ∨ (p2027) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3471) ∨ (¬ p4111) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial25191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory14447 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule25191 (meaning t m 2008) (meaning t m 2027) (meaning t m 2545) (meaning t m 3027) (meaning t m 3414) (meaning t m 3471) (meaning t m 4111) (meaning t m 4236) source

theorem rule25192 (p2027 p3256 p4341 p4347 p4358 p4843 : Prop) (h : (¬ p4341) ∨ (¬ p3256) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4843) ∨ (¬ p4358)) : (p2027) ∨ (¬ p3256) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial25192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory14448 t (m.theta 2 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule25192 (meaning t m 2027) (meaning t m 3256) (meaning t m 4341) (meaning t m 4347) (meaning t m 4358) (meaning t m 4843) source

theorem rule25195 (p2027 p2137 p2220 p2748 p2839 p2996 p3146 p3365 p3947 p4669 p4734 : Prop) (h : (¬ p3947) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p4734) ∨ (¬ p4669) ∨ (¬ p3365) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2748) ∨ (¬ p2996) ∨ p2027) : (p2027) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14451 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25195 (meaning t m 2027) (meaning t m 2137) (meaning t m 2220) (meaning t m 2748) (meaning t m 2839) (meaning t m 2996) (meaning t m 3146) (meaning t m 3365) (meaning t m 3947) (meaning t m 4669) (meaning t m 4734) source

theorem rule25198 (p2027 p2655 p2922 p2946 p3540 p4116 p4704 : Prop) (h : (¬ p2655) ∨ (¬ p2922) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4116) ∨ (¬ p4704)) : (p2027) ∨ (¬ p2655) ∨ (¬ p2922) ∨ (¬ p2946) ∨ (¬ p3540) ∨ (¬ p4116) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14454 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule25198 (meaning t m 2027) (meaning t m 2655) (meaning t m 2922) (meaning t m 2946) (meaning t m 3540) (meaning t m 4116) (meaning t m 4704) source

theorem rule25199 (p1998 p2027 p2088 p2110 p2114 p3055 p3367 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p2110) ∨ p2027 ∨ (¬ p3055) ∨ p2114 ∨ (¬ p3367) ∨ (¬ p1998) ∨ (¬ p2088)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2110) ∨ (p2114) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial25199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2110)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory14455 t (m.theta 0 2) (m.theta 0 8) (m.theta 1 2) (m.theta 2 4) (m.theta 7 8) (m.theta 8 9)
  exact rule25199 (meaning t m 1998) (meaning t m 2027) (meaning t m 2088) (meaning t m 2110) (meaning t m 2114) (meaning t m 3055) (meaning t m 3367) (meaning t m 4348) source

theorem rule25200 (p2191 p4335 p4363 : Prop) (h : (¬ p4335) ∨ (¬ p2191) ∨ p4363) : (¬ p2191) ∨ (¬ p4335) ∨ (p4363) := by
  classical
  tauto

theorem initial25200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 4335)) ∨ (meaning t m 4363) := by
  have source := ElevenTheory.theory14456 (m.theta 1 5) (m.theta 5 8) (m.theta 5 9)
  exact rule25200 (meaning t m 2191) (meaning t m 4335) (meaning t m 4363) source

theorem rule25202 (p2027 p2957 p2972 p4032 p4111 p4365 p4704 : Prop) (h : p2027 ∨ (¬ p4032) ∨ (¬ p2972) ∨ (¬ p2957) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704)) : (p2027) ∨ (¬ p2957) ∨ (¬ p2972) ∨ (¬ p4032) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14458 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9)
  exact rule25202 (meaning t m 2027) (meaning t m 2957) (meaning t m 2972) (meaning t m 4032) (meaning t m 4111) (meaning t m 4365) (meaning t m 4704) source

theorem rule25203 (p2027 p2737 p2811 p2946 p3585 p4343 p4704 : Prop) (h : (¬ p2946) ∨ (¬ p2811) ∨ (¬ p4343) ∨ (¬ p4704) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14459 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5)
  exact rule25203 (meaning t m 2027) (meaning t m 2737) (meaning t m 2811) (meaning t m 2946) (meaning t m 3585) (meaning t m 4343) (meaning t m 4704) source

theorem rule25207 (p2027 p2247 p2573 p3276 p4118 p4191 p4330 p4360 p4422 p5190 : Prop) (h : (¬ p4422) ∨ (¬ p2247) ∨ (¬ p5190) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p4118) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4330)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p3276) ∨ (¬ p4118) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4422) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial25207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory14463 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25207 (meaning t m 2027) (meaning t m 2247) (meaning t m 2573) (meaning t m 3276) (meaning t m 4118) (meaning t m 4191) (meaning t m 4330) (meaning t m 4360) (meaning t m 4422) (meaning t m 5190) source

theorem rule25208 (p3569 p3579 p4333 : Prop) (h : (¬ p3569) ∨ (¬ p3579) ∨ p4333) : (¬ p3569) ∨ (¬ p3579) ∨ (p4333) := by
  classical
  tauto

theorem initial25208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3579)) ∨ (meaning t m 4333) := by
  have source := ElevenTheory.theory14464 (m.theta 3 7) (m.theta 4 7) (m.theta 5 7)
  exact rule25208 (meaning t m 3569) (meaning t m 3579) (meaning t m 4333) source

theorem rule25210 (p3877 p4195 p4341 : Prop) (h : (¬ p3877) ∨ (¬ p4341) ∨ p4195) : (¬ p3877) ∨ (p4195) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial25210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3877)) ∨ (meaning t m 4195) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory14466 (m.theta 2 3) (m.theta 3 6) (m.theta 3 8)
  exact rule25210 (meaning t m 3877) (meaning t m 4195) (meaning t m 4341) source

theorem rule25211 (p2027 p3073 p3859 p4111 p4118 p4196 p4975 : Prop) (h : (¬ p4118) ∨ (¬ p3859) ∨ (¬ p4196) ∨ (¬ p4975) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3073)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3859) ∨ (¬ p4111) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial25211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory14467 t (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule25211 (meaning t m 2027) (meaning t m 3073) (meaning t m 3859) (meaning t m 4111) (meaning t m 4118) (meaning t m 4196) (meaning t m 4975) source

theorem rule25212 (p1990 p2027 p2132 p2563 p2611 p2870 p4235 : Prop) (h : (¬ p4235) ∨ p2611 ∨ (¬ p2870) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2563) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial25212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory14468 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule25212 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2563) (meaning t m 2611) (meaning t m 2870) (meaning t m 4235) source

theorem rule25213 (p1998 p2027 p2177 p2573 p2611 p3201 p3362 p3584 p4710 : Prop) (h : (¬ p1998) ∨ p2611 ∨ p2027 ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p3584) ∨ (¬ p2177) ∨ (¬ p4710) ∨ (¬ p3201)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2573) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial25213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory14469 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25213 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2573) (meaning t m 2611) (meaning t m 3201) (meaning t m 3362) (meaning t m 3584) (meaning t m 4710) source

theorem rule25214 (p2027 p2493 p3136 p3364 p3584 p4116 p4704 : Prop) (h : (¬ p3584) ∨ (¬ p3364) ∨ (¬ p2493) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p4116)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p4116) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14470 t (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule25214 (meaning t m 2027) (meaning t m 2493) (meaning t m 3136) (meaning t m 3364) (meaning t m 3584) (meaning t m 4116) (meaning t m 4704) source

theorem rule25215 (p2027 p2307 p2584 p2656 p3136 p3822 p4704 p4841 : Prop) (h : (¬ p2584) ∨ (¬ p4704) ∨ (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3822) ∨ (¬ p4841) ∨ p2027 ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3822) ∨ (¬ p4704) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial25215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory14471 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 7)
  exact rule25215 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2656) (meaning t m 3136) (meaning t m 3822) (meaning t m 4704) (meaning t m 4841) source

theorem rule25216 (p3568 p4037 p4187 : Prop) (h : (¬ p4187) ∨ (¬ p4037) ∨ p3568) : (p3568) ∨ (¬ p4037) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial25216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3568) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory14472 (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule25216 (meaning t m 3568) (meaning t m 4037) (meaning t m 4187) source

theorem rule25217 (p2027 p2505 p3136 p3319 p3917 p4116 p4704 p4841 : Prop) (h : (¬ p4116) ∨ (¬ p4704) ∨ (¬ p2505) ∨ p2027 ∨ (¬ p4841) ∨ (¬ p3917) ∨ (¬ p3136) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2505) ∨ (¬ p3136) ∨ (¬ p3319) ∨ (¬ p3917) ∨ (¬ p4116) ∨ (¬ p4704) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial25217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory14473 t (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 9)
  exact rule25217 (meaning t m 2027) (meaning t m 2505) (meaning t m 3136) (meaning t m 3319) (meaning t m 3917) (meaning t m 4116) (meaning t m 4704) (meaning t m 4841) source

theorem rule25219 (p2027 p2717 p3644 p3684 p4646 p5085 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p3684) ∨ (¬ p3644) ∨ (¬ p2717) ∨ (¬ p5085)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3644) ∨ (¬ p3684) ∨ (¬ p4646) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial25219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory14475 t (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule25219 (meaning t m 2027) (meaning t m 2717) (meaning t m 3644) (meaning t m 3684) (meaning t m 4646) (meaning t m 5085) source

theorem rule25221 (p2027 p2295 p2696 p2797 p3555 p3744 p4173 p4620 p4733 : Prop) (h : (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4620) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4620) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14477 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule25221 (meaning t m 2027) (meaning t m 2295) (meaning t m 2696) (meaning t m 2797) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4620) (meaning t m 4733) source

theorem rule25223 (p2027 p2363 p2589 p2774 p2819 p3690 p4235 p4669 p4729 : Prop) (h : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p4729) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3690) ∨ (¬ p2819) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial25223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory14479 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25223 (meaning t m 2027) (meaning t m 2363) (meaning t m 2589) (meaning t m 2774) (meaning t m 2819) (meaning t m 3690) (meaning t m 4235) (meaning t m 4669) (meaning t m 4729) source

theorem rule25224 (p2027 p2881 p3690 p3941 p4445 p5122 : Prop) (h : (¬ p5122) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4445) ∨ (¬ p3690) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4445) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory14480 t (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule25224 (meaning t m 2027) (meaning t m 2881) (meaning t m 3690) (meaning t m 3941) (meaning t m 4445) (meaning t m 5122) source

theorem rule25225 (p2220 p3646 p3988 : Prop) (h : (¬ p3646) ∨ (¬ p3988) ∨ (¬ p2220)) : (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial25225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory14481 (m.theta 0 5) (m.theta 5 6) (m.theta 5 8)
  exact rule25225 (meaning t m 2220) (meaning t m 3646) (meaning t m 3988) source

theorem rule25228 (p2027 p2797 p3125 p3297 p4035 p4564 p5379 : Prop) (h : (¬ p3297) ∨ (¬ p5379) ∨ (¬ p4035) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p4564) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3125) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4564) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial25228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory14484 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9)
  exact rule25228 (meaning t m 2027) (meaning t m 2797) (meaning t m 3125) (meaning t m 3297) (meaning t m 4035) (meaning t m 4564) (meaning t m 5379) source

theorem rule25229 (p2027 p2145 p2696 p3005 p3097 p3256 p3646 p4107 p4669 : Prop) (h : p2027 ∨ (¬ p4669) ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p4107) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3256) ∨ (¬ p2145)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3097) ∨ (¬ p3256) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14485 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25229 (meaning t m 2027) (meaning t m 2145) (meaning t m 2696) (meaning t m 3005) (meaning t m 3097) (meaning t m 3256) (meaning t m 3646) (meaning t m 4107) (meaning t m 4669) source

theorem rule25231 (p2010 p2027 p2437 p2459 p2476 p2534 p2633 p3363 p3683 : Prop) (h : (¬ p2437) ∨ (¬ p2010) ∨ p2027 ∨ (¬ p3683) ∨ (¬ p2476) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p2459) ∨ (¬ p3363)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3363) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial25231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory14487 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25231 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2633) (meaning t m 3363) (meaning t m 3683) source

theorem rule25232 (p2027 p2187 p2797 p3177 p3877 p4170 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p2797) ∨ (¬ p3177) ∨ p2027 ∨ (¬ p4170) ∨ (¬ p2187) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2797) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4170) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14488 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule25232 (meaning t m 2027) (meaning t m 2187) (meaning t m 2797) (meaning t m 3177) (meaning t m 3877) (meaning t m 4170) (meaning t m 4564) source

theorem rule25233 (p2027 p2252 p2750 p2952 p3707 p3830 p3952 p3954 p4393 p5254 : Prop) (h : (¬ p4393) ∨ (¬ p5254) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3707) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p3830)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4393) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial25233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory14489 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 9 10)
  exact rule25233 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3707) (meaning t m 3830) (meaning t m 3952) (meaning t m 3954) (meaning t m 4393) (meaning t m 5254) source

theorem rule25237 (p2027 p2098 p2509 p3055 p5214 p5373 : Prop) (h : (¬ p3055) ∨ (¬ p5214) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p5373) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2509) ∨ (¬ p3055) ∨ (¬ p5214) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial25237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 5214)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory14493 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule25237 (meaning t m 2027) (meaning t m 2098) (meaning t m 2509) (meaning t m 3055) (meaning t m 5214) (meaning t m 5373) source

theorem rule25241 (p2027 p2588 p3256 p3955 p4341 p4347 p4976 : Prop) (h : (¬ p4341) ∨ (¬ p2588) ∨ (¬ p4976) ∨ (¬ p3955) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3256) ∨ (¬ p3955) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial25241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory14497 t (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule25241 (meaning t m 2027) (meaning t m 2588) (meaning t m 3256) (meaning t m 3955) (meaning t m 4341) (meaning t m 4347) (meaning t m 4976) source

theorem rule25243 (p2027 p2810 p2870 p2957 p3556 p4313 p4704 : Prop) (h : (¬ p4704) ∨ (¬ p2957) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p4313) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14499 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule25243 (meaning t m 2027) (meaning t m 2810) (meaning t m 2870) (meaning t m 2957) (meaning t m 3556) (meaning t m 4313) (meaning t m 4704) source

theorem rule25244 (p2027 p2138 p2295 p2331 p2396 p3692 p3694 p3950 p4786 : Prop) (h : (¬ p2138) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14500 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25244 (meaning t m 2027) (meaning t m 2138) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4786) source

theorem rule25246 (p2027 p2657 p2958 p3051 p4320 p4704 : Prop) (h : (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4704) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4320)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14502 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule25246 (meaning t m 2027) (meaning t m 2657) (meaning t m 2958) (meaning t m 3051) (meaning t m 4320) (meaning t m 4704) source

theorem rule25247 (p2027 p2299 p2534 p2780 p3166 p3256 p3822 p4420 p4786 : Prop) (h : (¬ p4786) ∨ (¬ p2299) ∨ (¬ p3166) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3822) ∨ (¬ p4420) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14503 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25247 (meaning t m 2027) (meaning t m 2299) (meaning t m 2534) (meaning t m 2780) (meaning t m 3166) (meaning t m 3256) (meaning t m 3822) (meaning t m 4420) (meaning t m 4786) source

theorem rule25248 (p1990 p3128 p3989 p4601 : Prop) (h : (¬ p3989) ∨ p3128 ∨ (¬ p1990) ∨ p4601) : (¬ p1990) ∨ (p3128) ∨ (¬ p3989) ∨ (p4601) := by
  classical
  tauto

theorem initial25248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3989)) ∨ (meaning t m 4601) := by
  have source := ElevenTheory.theory14504 t (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule25248 (meaning t m 1990) (meaning t m 3128) (meaning t m 3989) (meaning t m 4601) source

theorem rule25249 (p2027 p2528 p2598 p2743 p3361 p3414 p3641 p3947 p4669 p4737 : Prop) (h : (¬ p3641) ∨ (¬ p2598) ∨ (¬ p2528) ∨ (¬ p2743) ∨ (¬ p4669) ∨ (¬ p3947) ∨ (¬ p3414) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3361)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3641) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory14505 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25249 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2743) (meaning t m 3361) (meaning t m 3414) (meaning t m 3641) (meaning t m 3947) (meaning t m 4669) (meaning t m 4737) source

theorem rule25250 (p2027 p2509 p2992 p3402 p3641 p4343 p4704 : Prop) (h : (¬ p3641) ∨ (¬ p4343) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4704) ∨ (¬ p3402)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p3641) ∨ (¬ p4343) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14506 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule25250 (meaning t m 2027) (meaning t m 2509) (meaning t m 2992) (meaning t m 3402) (meaning t m 3641) (meaning t m 4343) (meaning t m 4704) source

theorem rule25251 (p2027 p2608 p3333 p3367 p3556 p3570 p4332 p4348 p4524 : Prop) (h : p2027 ∨ (¬ p4332) ∨ (¬ p4524) ∨ (¬ p3367) ∨ (¬ p3333) ∨ (¬ p4348) ∨ (¬ p2608) ∨ (¬ p3570) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14507 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25251 (meaning t m 2027) (meaning t m 2608) (meaning t m 3333) (meaning t m 3367) (meaning t m 3556) (meaning t m 3570) (meaning t m 4332) (meaning t m 4348) (meaning t m 4524) source

theorem rule25252 (p1980 p2027 p2553 p2766 p3568 p3956 p4347 : Prop) (h : (¬ p3956) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2553) ∨ (¬ p1980) ∨ p2766 ∨ (¬ p3568)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2553) ∨ (p2766) ∨ (¬ p3568) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial25252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory14508 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule25252 (meaning t m 1980) (meaning t m 2027) (meaning t m 2553) (meaning t m 2766) (meaning t m 3568) (meaning t m 3956) (meaning t m 4347) source

theorem rule25255 (p2027 p2264 p2298 p2553 p3570 p4204 p4718 : Prop) (h : (¬ p2298) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p2264) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p4718)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2553) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial25255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory14511 t (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25255 (meaning t m 2027) (meaning t m 2264) (meaning t m 2298) (meaning t m 2553) (meaning t m 3570) (meaning t m 4204) (meaning t m 4718) source

theorem rule25256 (p2027 p2187 p3016 p3958 p4256 p4432 : Prop) (h : (¬ p4432) ∨ (¬ p4256) ∨ (¬ p2187) ∨ (¬ p3016) ∨ (¬ p3958) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4256) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial25256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory14512 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule25256 (meaning t m 2027) (meaning t m 2187) (meaning t m 3016) (meaning t m 3958) (meaning t m 4256) (meaning t m 4432) source

theorem rule25258 (p2027 p2608 p2922 p3540 p4108 p4376 : Prop) (h : (¬ p3540) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial25258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory14514 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7)
  exact rule25258 (meaning t m 2027) (meaning t m 2608) (meaning t m 2922) (meaning t m 3540) (meaning t m 4108) (meaning t m 4376) source

theorem rule25259 (p2027 p2810 p2811 p2958 p3051 p3486 p4282 p4704 : Prop) (h : (¬ p3486) ∨ (¬ p4704) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4282)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4282) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial25259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory14515 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule25259 (meaning t m 2027) (meaning t m 2810) (meaning t m 2811) (meaning t m 2958) (meaning t m 3051) (meaning t m 3486) (meaning t m 4282) (meaning t m 4704) source

theorem rule25262 (p1975 p2027 p2383 p2553 p2641 p2688 p3567 p3956 : Prop) (h : (¬ p2383) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p2641) ∨ p2688 ∨ (¬ p3956) ∨ (¬ p2553)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3567) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial25262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory14518 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25262 (meaning t m 1975) (meaning t m 2027) (meaning t m 2383) (meaning t m 2553) (meaning t m 2641) (meaning t m 2688) (meaning t m 3567) (meaning t m 3956) source

theorem rule25265 (p2027 p2247 p3742 p4111 p4279 p5207 : Prop) (h : (¬ p5207) ∨ (¬ p4279) ∨ (¬ p4111) ∨ (¬ p3742) ∨ (¬ p2247) ∨ p2027) : (p2027) ∨ (¬ p2247) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4279) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial25265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14521 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7)
  exact rule25265 (meaning t m 2027) (meaning t m 2247) (meaning t m 3742) (meaning t m 4111) (meaning t m 4279) (meaning t m 5207) source

theorem rule25269 (p2027 p2373 p3690 p4042 p4235 p4666 : Prop) (h : (¬ p4042) ∨ (¬ p2373) ∨ (¬ p4235) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3690)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3690) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial25269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory14525 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule25269 (meaning t m 2027) (meaning t m 2373) (meaning t m 3690) (meaning t m 4042) (meaning t m 4235) (meaning t m 4666) source

theorem rule25270 (p2027 p2241 p2528 p2598 p2750 p2753 p3641 p3817 p4366 p4669 : Prop) (h : (¬ p2528) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4669) ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3817) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14526 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25270 (meaning t m 2027) (meaning t m 2241) (meaning t m 2528) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3641) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule25271 (p1983 p2027 p2156 p2233 p2396 p2427 p4110 p4140 p4399 : Prop) (h : (¬ p2396) ∨ p2233 ∨ (¬ p2156) ∨ (¬ p4399) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p4140) ∨ (¬ p4110)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2156) ∨ (p2233) ∨ (¬ p2396) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial25271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory14527 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule25271 (meaning t m 1983) (meaning t m 2027) (meaning t m 2156) (meaning t m 2233) (meaning t m 2396) (meaning t m 2427) (meaning t m 4110) (meaning t m 4140) (meaning t m 4399) source

theorem rule25272 (p2027 p2373 p3073 p3949 p4498 p4948 : Prop) (h : p2027 ∨ (¬ p3073) ∨ (¬ p4498) ∨ (¬ p2373) ∨ (¬ p3949) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3073) ∨ (¬ p3949) ∨ (¬ p4498) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial25272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4498)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory14528 t (m.theta 1 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule25272 (meaning t m 2027) (meaning t m 2373) (meaning t m 3073) (meaning t m 3949) (meaning t m 4498) (meaning t m 4948) source

theorem rule25274 (p2027 p2249 p2470 p2528 p2656 p2727 p2963 p3549 p3922 p4107 p4669 : Prop) (h : (¬ p2656) ∨ (¬ p4669) ∨ (¬ p2470) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p2528) ∨ (¬ p3549) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14530 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25274 (meaning t m 2027) (meaning t m 2249) (meaning t m 2470) (meaning t m 2528) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 3549) (meaning t m 3922) (meaning t m 4107) (meaning t m 4669) source

theorem rule25275 (p2027 p2249 p2528 p2656 p2727 p3292 p3363 p3461 p3641 p4604 p5284 : Prop) (h : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p5284) ∨ (¬ p3461) ∨ (¬ p3292) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p4604) ∨ (¬ p3363) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3292) ∨ (¬ p3363) ∨ (¬ p3461) ∨ (¬ p3641) ∨ (¬ p4604) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial25275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory14531 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25275 (meaning t m 2027) (meaning t m 2249) (meaning t m 2528) (meaning t m 2656) (meaning t m 2727) (meaning t m 3292) (meaning t m 3363) (meaning t m 3461) (meaning t m 3641) (meaning t m 4604) (meaning t m 5284) source

theorem rule25276 (p2027 p2249 p2573 p2656 p2727 p2761 p3414 p3564 p4429 p4621 p5284 : Prop) (h : (¬ p3564) ∨ (¬ p3414) ∨ (¬ p5284) ∨ (¬ p2573) ∨ (¬ p4429) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p4621) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2761) ∨ (¬ p3414) ∨ (¬ p3564) ∨ (¬ p4429) ∨ (¬ p4621) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial25276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory14532 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule25276 (meaning t m 2027) (meaning t m 2249) (meaning t m 2573) (meaning t m 2656) (meaning t m 2727) (meaning t m 2761) (meaning t m 3414) (meaning t m 3564) (meaning t m 4429) (meaning t m 4621) (meaning t m 5284) source

theorem rule25277 (p2027 p2249 p2470 p2528 p2656 p2727 p2963 p3324 p5118 p5580 : Prop) (h : (¬ p2470) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p5580) ∨ (¬ p2528) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory14533 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25277 (meaning t m 2027) (meaning t m 2249) (meaning t m 2470) (meaning t m 2528) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 3324) (meaning t m 5118) (meaning t m 5580) source

theorem rule25278 (p2027 p2249 p2656 p2727 p2963 p3276 p3355 p3549 p3922 p4260 p4831 : Prop) (h : (¬ p2249) ∨ (¬ p3355) ∨ (¬ p4260) ∨ (¬ p2963) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p3276) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p3922) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial25278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory14534 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule25278 (meaning t m 2027) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 3276) (meaning t m 3355) (meaning t m 3549) (meaning t m 3922) (meaning t m 4260) (meaning t m 4831) source

theorem rule25280 (p1982 p2027 p2622 p2630 p2656 p3212 p3680 p4399 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p1982) ∨ (¬ p2630) ∨ p2622 ∨ (¬ p3680) ∨ p2027 ∨ (¬ p3212) ∨ (¬ p2656) ∨ (¬ p4399)) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p4399) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial25280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory14536 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25280 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3212) (meaning t m 3680) (meaning t m 4399) (meaning t m 4444) source

theorem rule25281 (p2027 p2254 p2518 p2528 p2952 p3379 p3690 p4320 p4669 : Prop) (h : (¬ p2254) ∨ (¬ p4320) ∨ (¬ p2528) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p3379) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14537 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25281 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 2952) (meaning t m 3379) (meaning t m 3690) (meaning t m 4320) (meaning t m 4669) source

theorem rule25283 (p2027 p2132 p2663 p2743 p2891 p3246 p3361 p3540 p3553 p3579 p4418 p4668 p4737 : Prop) (h : (¬ p3553) ∨ (¬ p4737) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4668) ∨ (¬ p4418) ∨ (¬ p3246) ∨ (¬ p2132) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3579) ∨ p2663 ∨ (¬ p3540)) : (p2027) ∨ (¬ p2132) ∨ (p2663) ∨ (¬ p2743) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3361) ∨ (¬ p3540) ∨ (¬ p3553) ∨ (¬ p3579) ∨ (¬ p4418) ∨ (¬ p4668) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2663) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory14539 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25283 (meaning t m 2027) (meaning t m 2132) (meaning t m 2663) (meaning t m 2743) (meaning t m 2891) (meaning t m 3246) (meaning t m 3361) (meaning t m 3540) (meaning t m 3553) (meaning t m 3579) (meaning t m 4418) (meaning t m 4668) (meaning t m 4737) source

theorem rule25289 (p2027 p2352 p2493 p2901 p3379 p3497 p3556 p4134 p4524 : Prop) (h : (¬ p2493) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3379) ∨ (¬ p4524) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p4134)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2901) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4134) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14545 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule25289 (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 2901) (meaning t m 3379) (meaning t m 3497) (meaning t m 3556) (meaning t m 4134) (meaning t m 4524) source

theorem rule25290 (p2010 p2027 p2545 p3019 p3323 p3527 p3644 p4026 p4452 : Prop) (h : (¬ p2010) ∨ (¬ p3019) ∨ p2027 ∨ (¬ p4026) ∨ p2545 ∨ (¬ p4452) ∨ (¬ p3644) ∨ (¬ p3323) ∨ (¬ p3527)) : (¬ p2010) ∨ (p2027) ∨ (p2545) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4026) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial25290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory14546 t (m.theta 1 6) (m.theta 1 7) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8)
  exact rule25290 (meaning t m 2010) (meaning t m 2027) (meaning t m 2545) (meaning t m 3019) (meaning t m 3323) (meaning t m 3527) (meaning t m 3644) (meaning t m 4026) (meaning t m 4452) source

theorem rule25291 (p2027 p2144 p2156 p2252 p2363 p2657 p2750 p2753 p2819 p3742 p4278 p4428 p4669 : Prop) (h : (¬ p2144) ∨ (¬ p4428) ∨ (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2753) ∨ (¬ p4278) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2819) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4428) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14547 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25291 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2252) (meaning t m 2363) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2819) (meaning t m 3742) (meaning t m 4278) (meaning t m 4428) (meaning t m 4669) source

theorem rule25292 (p2027 p2363 p2753 p2774 p2819 p3379 p3817 p4366 p4669 p5216 : Prop) (h : (¬ p2819) ∨ (¬ p3379) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p3817) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p2363) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14548 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25292 (meaning t m 2027) (meaning t m 2363) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) (meaning t m 5216) source

theorem rule25294 (p2027 p2254 p2608 p2952 p3537 p3609 p3690 p4320 p4669 : Prop) (h : (¬ p3537) ∨ (¬ p2952) ∨ (¬ p4669) ∨ (¬ p4320) ∨ (¬ p3609) ∨ (¬ p2254) ∨ (¬ p3690) ∨ (¬ p2608) ∨ p2027) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2952) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14550 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25294 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2952) (meaning t m 3537) (meaning t m 3609) (meaning t m 3690) (meaning t m 4320) (meaning t m 4669) source

theorem rule25295 (p2027 p2254 p2608 p2657 p3537 p3609 p3742 p4278 p4669 : Prop) (h : (¬ p4278) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2657) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14551 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25295 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2657) (meaning t m 3537) (meaning t m 3609) (meaning t m 3742) (meaning t m 4278) (meaning t m 4669) source

theorem rule25296 (p2027 p2254 p2608 p2963 p3537 p3568 p3609 p4107 p4669 : Prop) (h : (¬ p3568) ∨ (¬ p4669) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3537) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2963) ∨ (¬ p3537) ∨ (¬ p3568) ∨ (¬ p3609) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14552 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25296 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2963) (meaning t m 3537) (meaning t m 3568) (meaning t m 3609) (meaning t m 4107) (meaning t m 4669) source

theorem rule25297 (p3016 p3740 p3920 p4112 : Prop) (h : (¬ p3920) ∨ (¬ p4112) ∨ (¬ p3740) ∨ (¬ p3016)) : (¬ p3016) ∨ (¬ p3740) ∨ (¬ p3920) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial25297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory14553 (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule25297 (meaning t m 3016) (meaning t m 3740) (meaning t m 3920) (meaning t m 4112) source

theorem rule25298 (p2027 p2252 p2534 p2657 p2750 p3093 p3319 p3954 p4256 p4330 : Prop) (h : (¬ p3093) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p2657) ∨ (¬ p3319) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3954) ∨ (¬ p4256) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial25298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory14554 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule25298 (meaning t m 2027) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3954) (meaning t m 4256) (meaning t m 4330) source

theorem rule25299 (p1975 p2027 p2287 p3093 p3309 p3323 p3834 p5148 : Prop) (h : (¬ p5148) ∨ (¬ p3309) ∨ p2287 ∨ (¬ p3323) ∨ p2027 ∨ (¬ p3834) ∨ (¬ p1975) ∨ (¬ p3093)) : (¬ p1975) ∨ (p2027) ∨ (p2287) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3323) ∨ (¬ p3834) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial25299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory14555 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule25299 (meaning t m 1975) (meaning t m 2027) (meaning t m 2287) (meaning t m 3093) (meaning t m 3309) (meaning t m 3323) (meaning t m 3834) (meaning t m 5148) source

theorem rule25300 (p2027 p2098 p2528 p2748 p2761 p3055 p3368 p4039 p4363 p4669 p4749 p5284 p5373 : Prop) (h : p2027 ∨ (¬ p2098) ∨ (¬ p5373) ∨ (¬ p2761) ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p4039) ∨ (¬ p4363) ∨ (¬ p5284) ∨ (¬ p3368) ∨ (¬ p2748) ∨ (¬ p4749) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2528) ∨ (¬ p2748) ∨ (¬ p2761) ∨ (¬ p3055) ∨ (¬ p3368) ∨ (¬ p4039) ∨ (¬ p4363) ∨ (¬ p4669) ∨ (¬ p4749) ∨ (¬ p5284) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial25300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory14556 t (m.theta 0 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 9) (m.theta 4 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25300 (meaning t m 2027) (meaning t m 2098) (meaning t m 2528) (meaning t m 2748) (meaning t m 2761) (meaning t m 3055) (meaning t m 3368) (meaning t m 4039) (meaning t m 4363) (meaning t m 4669) (meaning t m 4749) (meaning t m 5284) (meaning t m 5373) source

theorem rule25301 (p2027 p2870 p3073 p3449 p3556 p3694 p4134 p4347 p4524 : Prop) (h : (¬ p4524) ∨ (¬ p4134) ∨ (¬ p3556) ∨ (¬ p4347) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3073) ∨ (¬ p3449)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3556) ∨ (¬ p3694) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14557 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule25301 (meaning t m 2027) (meaning t m 2870) (meaning t m 3073) (meaning t m 3449) (meaning t m 3556) (meaning t m 3694) (meaning t m 4134) (meaning t m 4347) (meaning t m 4524) source

theorem rule25302 (p2027 p2363 p3063 p3093 p3365 p3572 p3947 p4669 p4736 : Prop) (h : (¬ p3365) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3947) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p2363) ∨ (¬ p3572) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14558 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25302 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4669) (meaning t m 4736) source

theorem rule25303 (p1983 p2027 p2417 p2499 p2573 p2765 p2870 p2922 p3556 p3758 p4079 p4524 : Prop) (h : (¬ p2417) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2922) ∨ (¬ p3758) ∨ (¬ p4079) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2870) ∨ (¬ p3556) ∨ p2765 ∨ (¬ p4524)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p2922) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p4079) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14559 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule25303 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2499) (meaning t m 2573) (meaning t m 2765) (meaning t m 2870) (meaning t m 2922) (meaning t m 3556) (meaning t m 3758) (meaning t m 4079) (meaning t m 4524) source

theorem rule25305 (p2027 p2254 p2459 p2598 p3414 p3537 p3585 p3589 p3919 p4118 p4802 : Prop) (h : (¬ p4802) ∨ (¬ p3919) ∨ (¬ p2459) ∨ (¬ p3414) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3414) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4802) := by
  classical
  tauto

theorem initial25305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4802)) := by
  have source := ElevenTheory.theory14561 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25305 (meaning t m 2027) (meaning t m 2254) (meaning t m 2459) (meaning t m 2598) (meaning t m 3414) (meaning t m 3537) (meaning t m 3585) (meaning t m 3589) (meaning t m 3919) (meaning t m 4118) (meaning t m 4802) source

theorem rule25309 (p2027 p2138 p3073 p3366 p3449 p3452 p3690 p4244 p4376 p4669 : Prop) (h : (¬ p3690) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p3073) ∨ (¬ p3452) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3449) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4376) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14565 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25309 (meaning t m 2027) (meaning t m 2138) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3690) (meaning t m 4244) (meaning t m 4376) (meaning t m 4669) source

theorem rule25310 (p2027 p3073 p3365 p3366 p3449 p3452 p3572 p3947 p4376 p4669 : Prop) (h : p2027 ∨ (¬ p3572) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3452) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3449) ∨ (¬ p4669) ∨ (¬ p3947)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14566 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25310 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3572) (meaning t m 3947) (meaning t m 4376) (meaning t m 4669) source

theorem rule25311 (p2027 p2352 p2363 p2573 p3365 p3366 p3519 p3572 p3947 p4376 p4669 : Prop) (h : (¬ p3572) ∨ (¬ p3365) ∨ (¬ p2363) ∨ (¬ p2352) ∨ (¬ p4669) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3947) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p2573)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14567 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25311 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3572) (meaning t m 3947) (meaning t m 4376) (meaning t m 4669) source

theorem rule25312 (p2027 p3680 p3958 p4137 p4191 p4334 : Prop) (h : (¬ p4137) ∨ (¬ p4334) ∨ (¬ p3958) ∨ (¬ p4191) ∨ (¬ p3680) ∨ p2027) : (p2027) ∨ (¬ p3680) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial25312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory14568 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule25312 (meaning t m 2027) (meaning t m 3680) (meaning t m 3958) (meaning t m 4137) (meaning t m 4191) (meaning t m 4334) source

theorem rule25313 (p2027 p2352 p2363 p2573 p2761 p3292 p4236 p4419 p4669 p5284 : Prop) (h : (¬ p2761) ∨ (¬ p5284) ∨ (¬ p4236) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3292) ∨ (¬ p4419) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2761) ∨ (¬ p3292) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4669) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial25313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory14569 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25313 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2761) (meaning t m 3292) (meaning t m 4236) (meaning t m 4419) (meaning t m 4669) (meaning t m 5284) source

theorem rule25315 (p2027 p2166 p2210 p2780 p3146 p3822 p4107 p4669 p4736 : Prop) (h : (¬ p2780) ∨ (¬ p3146) ∨ (¬ p4669) ∨ (¬ p3822) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3146) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14571 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25315 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2780) (meaning t m 3146) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) (meaning t m 4736) source

theorem rule25316 (p2027 p2264 p2579 p2807 p3422 p3570 p3876 p3905 p4647 p4786 : Prop) (h : p2027 ∨ (¬ p3905) ∨ (¬ p2807) ∨ (¬ p3876) ∨ (¬ p2579) ∨ (¬ p4786) ∨ (¬ p3422) ∨ (¬ p4647) ∨ (¬ p3570) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p2807) ∨ (¬ p3422) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4647) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14572 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule25316 (meaning t m 2027) (meaning t m 2264) (meaning t m 2579) (meaning t m 2807) (meaning t m 3422) (meaning t m 3570) (meaning t m 3876) (meaning t m 3905) (meaning t m 4647) (meaning t m 4786) source

theorem rule25317 (p2027 p2696 p2742 p3189 p3256 p3363 p3540 p3585 p4278 p4669 p4737 : Prop) (h : p2027 ∨ (¬ p3585) ∨ (¬ p4737) ∨ (¬ p3256) ∨ (¬ p3363) ∨ (¬ p3189) ∨ (¬ p4669) ∨ (¬ p2742) ∨ (¬ p4278) ∨ (¬ p2696) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory14573 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25317 (meaning t m 2027) (meaning t m 2696) (meaning t m 2742) (meaning t m 3189) (meaning t m 3256) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 4278) (meaning t m 4669) (meaning t m 4737) source

theorem rule25319 (p2027 p2608 p2839 p3105 p3540 p3644 p4348 p4450 p5193 : Prop) (h : (¬ p4450) ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p3540) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p2839) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial25319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory14575 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule25319 (meaning t m 2027) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) (meaning t m 4450) (meaning t m 5193) source

theorem rule25320 (p2027 p2331 p3055 p3323 p3461 p3874 p4286 p4786 p5123 : Prop) (h : (¬ p4786) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p5123) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4786) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial25320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory14576 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25320 (meaning t m 2027) (meaning t m 2331) (meaning t m 3055) (meaning t m 3323) (meaning t m 3461) (meaning t m 3874) (meaning t m 4286) (meaning t m 4786) (meaning t m 5123) source

theorem rule25321 (p2027 p2331 p2363 p2668 p3055 p3876 p4278 p4669 p4786 : Prop) (h : (¬ p2331) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p2363) ∨ (¬ p3876) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14577 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25321 (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) (meaning t m 4786) source

theorem rule25323 (p2027 p2177 p2295 p2331 p2476 p2534 p3146 p3905 p4786 p4905 : Prop) (h : (¬ p2534) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4786) ∨ (¬ p3905) ∨ (¬ p2476) ∨ (¬ p2295) ∨ (¬ p4905) ∨ (¬ p2331) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial25323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory14579 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25323 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 2476) (meaning t m 2534) (meaning t m 3146) (meaning t m 3905) (meaning t m 4786) (meaning t m 4905) source

theorem rule25326 (p2027 p2138 p2264 p2459 p2807 p3744 p3758 p4604 p4786 : Prop) (h : (¬ p2807) ∨ (¬ p4604) ∨ (¬ p2138) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2264) ∨ (¬ p4786) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14582 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule25326 (meaning t m 2027) (meaning t m 2138) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3744) (meaning t m 3758) (meaning t m 4604) (meaning t m 4786) source

theorem rule25327 (p2027 p2138 p3166 p3256 p3266 p3758 p4393 p4786 p5254 : Prop) (h : (¬ p4393) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p4786) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4786) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial25327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory14583 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule25327 (meaning t m 2027) (meaning t m 2138) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3758) (meaning t m 4393) (meaning t m 4786) (meaning t m 5254) source

theorem rule25335 (p2027 p2780 p3073 p3366 p3449 p3452 p3822 p4107 p4376 p4669 : Prop) (h : (¬ p2780) ∨ (¬ p3073) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4107) ∨ (¬ p3822) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4376) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14591 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25335 (meaning t m 2027) (meaning t m 2780) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3822) (meaning t m 4107) (meaning t m 4376) (meaning t m 4669) source

theorem rule25336 (p2027 p2230 p2373 p2608 p3146 p3519 p3817 p4366 p4376 p4669 : Prop) (h : (¬ p4376) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2373) ∨ (¬ p3817) ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14592 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25336 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2608) (meaning t m 3146) (meaning t m 3519) (meaning t m 3817) (meaning t m 4366) (meaning t m 4376) (meaning t m 4669) source

theorem rule25337 (p2027 p2230 p2373 p3146 p3365 p3572 p3947 p4419 p4669 : Prop) (h : (¬ p3365) ∨ (¬ p3572) ∨ (¬ p2230) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4419) ∨ (¬ p3146) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4419) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14593 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25337 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4419) (meaning t m 4669) source

theorem rule25338 (p2027 p2139 p2156 p2187 p2363 p3365 p3572 p3947 p4669 : Prop) (h : (¬ p3572) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p2156) ∨ (¬ p2139) ∨ (¬ p3947) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14594 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25338 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4669) source

theorem rule25339 (p2027 p3146 p3365 p3366 p3449 p3555 p3572 p3947 p4377 p4446 p4669 : Prop) (h : (¬ p3555) ∨ (¬ p4446) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3947) ∨ (¬ p3146) ∨ (¬ p4377) ∨ (¬ p3572) ∨ (¬ p4669) ∨ (¬ p3366) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14595 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25339 (meaning t m 2027) (meaning t m 3146) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3572) (meaning t m 3947) (meaning t m 4377) (meaning t m 4446) (meaning t m 4669) source

theorem rule25340 (p2027 p2220 p2427 p3646 p3880 p4558 : Prop) (h : (¬ p3646) ∨ (¬ p2427) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial25340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory14596 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule25340 (meaning t m 2027) (meaning t m 2220) (meaning t m 2427) (meaning t m 3646) (meaning t m 3880) (meaning t m 4558) source

theorem rule25341 (p2220 p2951 p3156 : Prop) (h : (¬ p2220) ∨ (¬ p2951) ∨ p3156) : (¬ p2220) ∨ (¬ p2951) ∨ (p3156) := by
  classical
  tauto

theorem initial25341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2951)) ∨ (meaning t m 3156) := by
  have source := ElevenTheory.theory14597 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule25341 (meaning t m 2220) (meaning t m 2951) (meaning t m 3156) source

theorem rule25342 (p2027 p2657 p3146 p3366 p3449 p3555 p3683 p3876 p4236 p4278 p4377 p4446 p4669 : Prop) (h : (¬ p3366) ∨ (¬ p3876) ∨ (¬ p3449) ∨ (¬ p3683) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p3555) ∨ (¬ p4236) ∨ (¬ p3146) ∨ (¬ p2657) ∨ (¬ p4446) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4236) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14598 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25342 (meaning t m 2027) (meaning t m 2657) (meaning t m 3146) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3683) (meaning t m 3876) (meaning t m 4236) (meaning t m 4278) (meaning t m 4377) (meaning t m 4446) (meaning t m 4669) source

theorem rule25344 (p2027 p2139 p2220 p2533 p3365 p3572 p3680 p3947 p4444 p4669 : Prop) (h : (¬ p2220) ∨ (¬ p2139) ∨ (¬ p3365) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p3572) ∨ (¬ p4444) ∨ (¬ p3680) ∨ (¬ p2533)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2533) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14600 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25344 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 2533) (meaning t m 3365) (meaning t m 3572) (meaning t m 3680) (meaning t m 3947) (meaning t m 4444) (meaning t m 4669) source

theorem rule25347 (p2027 p2166 p2210 p3146 p3365 p3572 p3947 p4669 p4736 : Prop) (h : (¬ p3947) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14603 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25347 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3146) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4669) (meaning t m 4736) source

theorem rule25348 (p2027 p2166 p2230 p3146 p3365 p3572 p3947 p4034 p4079 p4669 p4736 : Prop) (h : (¬ p2166) ∨ (¬ p4034) ∨ (¬ p4669) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p3572) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2230) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2230) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4034) ∨ (¬ p4079) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14604 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25348 (meaning t m 2027) (meaning t m 2166) (meaning t m 2230) (meaning t m 3146) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4034) (meaning t m 4079) (meaning t m 4669) (meaning t m 4736) source

theorem rule25355 (p2027 p2166 p2210 p3055 p3146 p3876 p4278 p4669 p4736 : Prop) (h : (¬ p4278) ∨ (¬ p3055) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p3876) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14611 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25355 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3055) (meaning t m 3146) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) (meaning t m 4736) source

theorem rule25357 (p2027 p2241 p2780 p3189 p3256 p3822 p4107 p4669 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4669) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2241) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2780) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14613 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25357 (meaning t m 2027) (meaning t m 2241) (meaning t m 2780) (meaning t m 3189) (meaning t m 3256) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) (meaning t m 4736) source

theorem rule25358 (p1982 p2027 p2470 p2531 p2589 p2842 p2850 p3146 : Prop) (h : (¬ p2531) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2850) ∨ (¬ p2470) ∨ p2842 ∨ (¬ p1982) ∨ (¬ p2589)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial25358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory14614 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule25358 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2589) (meaning t m 2842) (meaning t m 2850) (meaning t m 3146) source

theorem rule25360 (p2027 p2946 p3055 p3146 p3156 p3584 p4137 p4604 p4786 : Prop) (h : (¬ p3146) ∨ (¬ p3055) ∨ (¬ p4786) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p4604) ∨ (¬ p3584) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14616 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule25360 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3146) (meaning t m 3156) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4786) source

theorem rule25361 (p2027 p2946 p3146 p3156 p3346 p3461 p3905 p4425 p4604 p4786 : Prop) (h : (¬ p3461) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p3905) ∨ (¬ p4604) ∨ (¬ p3146) ∨ (¬ p4786) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2946)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14617 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25361 (meaning t m 2027) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3346) (meaning t m 3461) (meaning t m 3905) (meaning t m 4425) (meaning t m 4604) (meaning t m 4786) source

theorem rule25362 (p2027 p2264 p2579 p2807 p3905 p3941 p4137 p4191 p4786 p5119 : Prop) (h : (¬ p3941) ∨ (¬ p5119) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2579) ∨ (¬ p3905) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p2807) ∨ (¬ p3905) ∨ (¬ p3941) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14618 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25362 (meaning t m 2027) (meaning t m 2264) (meaning t m 2579) (meaning t m 2807) (meaning t m 3905) (meaning t m 3941) (meaning t m 4137) (meaning t m 4191) (meaning t m 4786) (meaning t m 5119) source

theorem rule25363 (p2027 p2579 p2946 p3146 p3156 p3422 p3905 p4697 p4786 p5160 : Prop) (h : (¬ p4697) ∨ (¬ p3146) ∨ (¬ p2579) ∨ (¬ p3156) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial25363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14619 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule25363 (meaning t m 2027) (meaning t m 2579) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3422) (meaning t m 3905) (meaning t m 4697) (meaning t m 4786) (meaning t m 5160) source

theorem rule25366 (p2027 p2299 p2780 p3166 p3256 p3692 p3822 p4786 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p4786) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2299) ∨ (¬ p3692) ∨ (¬ p3166) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4786) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial25366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory14622 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25366 (meaning t m 2027) (meaning t m 2299) (meaning t m 2780) (meaning t m 3166) (meaning t m 3256) (meaning t m 3692) (meaning t m 3822) (meaning t m 4786) (meaning t m 4902) source

theorem rule25367 (p2027 p2696 p2743 p3452 p3589 p4376 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p3589) ∨ (¬ p2743) ∨ (¬ p2696) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3452) ∨ (¬ p3589) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial25367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory14623 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3)
  exact rule25367 (meaning t m 2027) (meaning t m 2696) (meaning t m 2743) (meaning t m 3452) (meaning t m 3589) (meaning t m 4376) source

theorem rule25368 (p2027 p2230 p2247 p2373 p2996 p3146 p3947 p4669 p5190 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial25368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory14624 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25368 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2373) (meaning t m 2996) (meaning t m 3146) (meaning t m 3947) (meaning t m 4669) (meaning t m 5190) source

theorem rule25372 (p2027 p2138 p2264 p2807 p3941 p4322 p4385 p4786 p5119 : Prop) (h : p2027 ∨ (¬ p2807) ∨ (¬ p2138) ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p2264) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14628 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25372 (meaning t m 2027) (meaning t m 2138) (meaning t m 2264) (meaning t m 2807) (meaning t m 3941) (meaning t m 4322) (meaning t m 4385) (meaning t m 4786) (meaning t m 5119) source

theorem rule25373 (p1994 p2027 p2253 p2406 p2440 p2699 p2807 p2996 p4281 : Prop) (h : (¬ p2253) ∨ p2699 ∨ (¬ p2440) ∨ (¬ p2807) ∨ (¬ p1994) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p4281) ∨ (¬ p2406)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2699) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial25373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory14629 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule25373 (meaning t m 1994) (meaning t m 2027) (meaning t m 2253) (meaning t m 2406) (meaning t m 2440) (meaning t m 2699) (meaning t m 2807) (meaning t m 2996) (meaning t m 4281) source

theorem rule25374 (p2027 p2241 p2459 p2727 p3083 p3692 p4120 p4420 p4524 : Prop) (h : (¬ p2727) ∨ (¬ p4120) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3083) ∨ (¬ p2459) ∨ (¬ p4420) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14630 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25374 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2727) (meaning t m 3083) (meaning t m 3692) (meaning t m 4120) (meaning t m 4420) (meaning t m 4524) source

theorem rule25375 (p2027 p2241 p2299 p2727 p3083 p3097 p3646 p4420 p4524 : Prop) (h : (¬ p2299) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p4524) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14631 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule25375 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2727) (meaning t m 3083) (meaning t m 3097) (meaning t m 3646) (meaning t m 4420) (meaning t m 4524) source

theorem rule25377 (p2027 p2138 p2528 p2651 p3083 p3690 p4244 p4669 p4786 : Prop) (h : (¬ p2138) ∨ (¬ p3690) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p3083) ∨ (¬ p4786) ∨ (¬ p2651) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14633 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25377 (meaning t m 2027) (meaning t m 2138) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4786) source

theorem rule25378 (p2027 p2241 p2641 p2870 p3323 p3556 p4368 p4385 p4524 : Prop) (h : (¬ p2641) ∨ (¬ p4524) ∨ (¬ p4368) ∨ (¬ p3556) ∨ (¬ p4385) ∨ (¬ p2870) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3323)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3556) ∨ (¬ p4368) ∨ (¬ p4385) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14634 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9)
  exact rule25378 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2870) (meaning t m 3323) (meaning t m 3556) (meaning t m 4368) (meaning t m 4385) (meaning t m 4524) source

theorem rule25379 (p2027 p2136 p2331 p2363 p2668 p2761 p4032 p4322 p4669 p4786 : Prop) (h : p2027 ∨ (¬ p2668) ∨ (¬ p4669) ∨ (¬ p4322) ∨ (¬ p2136) ∨ (¬ p2761) ∨ (¬ p2331) ∨ (¬ p4786) ∨ (¬ p2363) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2761) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4669) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14635 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25379 (meaning t m 2027) (meaning t m 2136) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2761) (meaning t m 4032) (meaning t m 4322) (meaning t m 4669) (meaning t m 4786) source

theorem rule25381 (p2027 p2136 p2860 p3166 p3506 p3646 p4033 p4385 p4444 p4604 p4786 p5111 : Prop) (h : p2027 ∨ (¬ p3166) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p3506) ∨ (¬ p5111) ∨ (¬ p3646) ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p4604) ∨ (¬ p4385) ∨ (¬ p4033)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3166) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4385) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4786) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial25381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory14637 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 8) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25381 (meaning t m 2027) (meaning t m 2136) (meaning t m 2860) (meaning t m 3166) (meaning t m 3506) (meaning t m 3646) (meaning t m 4033) (meaning t m 4385) (meaning t m 4444) (meaning t m 4604) (meaning t m 4786) (meaning t m 5111) source

theorem rule25382 (p2027 p2470 p2663 p2780 p3343 p3822 p4107 p4256 p4638 p4786 : Prop) (h : (¬ p2470) ∨ p2027 ∨ (¬ p4638) ∨ (¬ p3343) ∨ (¬ p4256) ∨ (¬ p2663) ∨ (¬ p3822) ∨ (¬ p4786) ∨ (¬ p2780) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14638 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule25382 (meaning t m 2027) (meaning t m 2470) (meaning t m 2663) (meaning t m 2780) (meaning t m 3343) (meaning t m 3822) (meaning t m 4107) (meaning t m 4256) (meaning t m 4638) (meaning t m 4786) source

theorem rule25383 (p2027 p2138 p2534 p3166 p3256 p3570 p4244 p4420 p4786 : Prop) (h : (¬ p3166) ∨ (¬ p4786) ∨ (¬ p4244) ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p4420) ∨ (¬ p3570) ∨ (¬ p2138) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2534) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14639 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25383 (meaning t m 2027) (meaning t m 2138) (meaning t m 2534) (meaning t m 3166) (meaning t m 3256) (meaning t m 3570) (meaning t m 4244) (meaning t m 4420) (meaning t m 4786) source

theorem rule25384 (p2027 p2138 p2651 p3276 p3343 p4244 p4786 p4831 p5660 : Prop) (h : (¬ p2138) ∨ (¬ p2651) ∨ (¬ p4244) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p3343) ∨ (¬ p4831) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4244) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial25384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory14640 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule25384 (meaning t m 2027) (meaning t m 2138) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 4244) (meaning t m 4786) (meaning t m 4831) (meaning t m 5660) source

theorem rule25385 (p2027 p2138 p2528 p2651 p3083 p3744 p3758 p4604 p4786 : Prop) (h : (¬ p4604) ∨ (¬ p3758) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p2138) ∨ (¬ p3083) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14641 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule25385 (meaning t m 2027) (meaning t m 2138) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3744) (meaning t m 3758) (meaning t m 4604) (meaning t m 4786) source

theorem rule25386 (p2027 p2136 p2528 p2651 p2860 p3083 p3646 p4385 p4786 p5059 : Prop) (h : (¬ p4385) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p5059) ∨ (¬ p3083) ∨ (¬ p3646) ∨ (¬ p2136) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2860) ∨ (¬ p3083) ∨ (¬ p3646) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial25386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory14642 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule25386 (meaning t m 2027) (meaning t m 2136) (meaning t m 2528) (meaning t m 2651) (meaning t m 2860) (meaning t m 3083) (meaning t m 3646) (meaning t m 4385) (meaning t m 4786) (meaning t m 5059) source

theorem rule25388 (p2027 p2138 p2651 p3083 p4149 p4322 p4385 p4786 p5119 : Prop) (h : (¬ p4385) ∨ (¬ p2138) ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p4322) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14644 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25388 (meaning t m 2027) (meaning t m 2138) (meaning t m 2651) (meaning t m 3083) (meaning t m 4149) (meaning t m 4322) (meaning t m 4385) (meaning t m 4786) (meaning t m 5119) source

theorem rule25390 (p3568 p3822 p4328 : Prop) (h : (¬ p3822) ∨ (¬ p4328) ∨ p3568) : (p3568) ∨ (¬ p3822) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial25390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3568) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory14646 (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule25390 (meaning t m 3568) (meaning t m 3822) (meaning t m 4328) source

theorem rule25392 (p2027 p2299 p2588 p3073 p3449 p3646 p4118 p4203 p4524 p4550 : Prop) (h : (¬ p2588) ∨ (¬ p3073) ∨ (¬ p4524) ∨ (¬ p4118) ∨ (¬ p4550) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4203) ∨ (¬ p2299) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3646) ∨ (¬ p4118) ∨ (¬ p4203) ∨ (¬ p4524) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial25392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory14648 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 8) (m.theta 3 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25392 (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 3073) (meaning t m 3449) (meaning t m 3646) (meaning t m 4118) (meaning t m 4203) (meaning t m 4524) (meaning t m 4550) source

theorem rule25393 (p2027 p2098 p3347 p3365 p3540 p4019 p4030 p4278 p4381 p4752 p5119 : Prop) (h : (¬ p2098) ∨ (¬ p4030) ∨ (¬ p3365) ∨ (¬ p4019) ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p3540) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3540) ∨ (¬ p4019) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4752) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14649 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25393 (meaning t m 2027) (meaning t m 2098) (meaning t m 3347) (meaning t m 3365) (meaning t m 3540) (meaning t m 4019) (meaning t m 4030) (meaning t m 4278) (meaning t m 4381) (meaning t m 4752) (meaning t m 5119) source

theorem rule25396 (p2027 p2230 p2373 p3146 p3588 p3954 p4324 p4669 p5190 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p4669) ∨ (¬ p3954) ∨ (¬ p3588) ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial25396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory14652 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25396 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) (meaning t m 5190) source

theorem rule25397 (p1984 p2027 p3008 p3584 p3609 p3860 p4261 p4354 : Prop) (h : (¬ p3609) ∨ (¬ p4261) ∨ (¬ p3860) ∨ p3008 ∨ (¬ p4354) ∨ (¬ p1984) ∨ (¬ p3584) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p3008) ∨ (¬ p3584) ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial25397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory14653 t (m.theta 0 1) (m.theta 1 8) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 8 9)
  exact rule25397 (meaning t m 1984) (meaning t m 2027) (meaning t m 3008) (meaning t m 3584) (meaning t m 3609) (meaning t m 3860) (meaning t m 4261) (meaning t m 4354) source

theorem rule25398 (p2027 p2352 p2363 p2573 p3588 p3954 p4324 p4669 p5190 : Prop) (h : p2027 ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p5190) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p2352) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial25398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory14654 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25398 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) (meaning t m 5190) source

theorem rule25401 (p4418 p4632 p4885 : Prop) (h : (¬ p4418) ∨ (¬ p4885) ∨ p4632) : (¬ p4418) ∨ (p4632) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial25401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4418)) ∨ (meaning t m 4632) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory14657 t (m.theta 1 5) (m.theta 2 5) (m.theta 4 5)
  exact rule25401 (meaning t m 4418) (meaning t m 4632) (meaning t m 4885) source

theorem rule25404 (p2027 p2248 p2331 p2363 p2668 p3486 p3555 p3690 p4669 : Prop) (h : (¬ p3486) ∨ (¬ p2248) ∨ (¬ p2668) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p3555) ∨ (¬ p2363) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14660 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25404 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4669) source

theorem rule25408 (p1998 p2027 p2387 p2753 p2764 p2911 p3204 p3471 p3692 p4253 p4441 p4444 p4512 p4877 p5503 : Prop) (h : (¬ p3471) ∨ (¬ p1998) ∨ (¬ p5503) ∨ (¬ p2911) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p3204) ∨ (¬ p4512) ∨ (¬ p4441) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p4444) ∨ p2764 ∨ (¬ p3692) ∨ (¬ p4253)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p2911) ∨ (¬ p3204) ∨ (¬ p3471) ∨ (¬ p3692) ∨ (¬ p4253) ∨ (¬ p4441) ∨ (¬ p4444) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial25408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory14664 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 7) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule25408 (meaning t m 1998) (meaning t m 2027) (meaning t m 2387) (meaning t m 2753) (meaning t m 2764) (meaning t m 2911) (meaning t m 3204) (meaning t m 3471) (meaning t m 3692) (meaning t m 4253) (meaning t m 4441) (meaning t m 4444) (meaning t m 4512) (meaning t m 4877) (meaning t m 5503) source

theorem rule25409 (p2027 p2396 p3309 p3690 p4204 p4518 : Prop) (h : p2027 ∨ (¬ p4518) ∨ (¬ p4204) ∨ (¬ p3690) ∨ (¬ p2396) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial25409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory14665 t (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule25409 (meaning t m 2027) (meaning t m 2396) (meaning t m 3309) (meaning t m 3690) (meaning t m 4204) (meaning t m 4518) source

theorem rule25410 (p1985 p2027 p2427 p2542 p2611 p2630 p2696 : Prop) (h : p2027 ∨ (¬ p2542) ∨ p2611 ∨ (¬ p1985) ∨ (¬ p2427) ∨ (¬ p2630) ∨ (¬ p2696)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2696) := by
  classical
  tauto

theorem initial25410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) := by
  have source := ElevenTheory.theory14666 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule25410 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 2611) (meaning t m 2630) (meaning t m 2696) source

theorem rule25413 (p2027 p2187 p2528 p4118 p4196 p4432 p4564 : Prop) (h : (¬ p2187) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4432) ∨ (¬ p4564)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2528) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4432) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14669 t (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25413 (meaning t m 2027) (meaning t m 2187) (meaning t m 2528) (meaning t m 4118) (meaning t m 4196) (meaning t m 4432) (meaning t m 4564) source

theorem rule25414 (p2027 p2743 p2922 p3541 p3876 p4752 : Prop) (h : (¬ p2743) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p4752) ∨ (¬ p3541) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3541) ∨ (¬ p3876) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14670 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7)
  exact rule25414 (meaning t m 2027) (meaning t m 2743) (meaning t m 2922) (meaning t m 3541) (meaning t m 3876) (meaning t m 4752) source

theorem rule25415 (p2005 p2027 p2406 p2573 p2589 p2622 p2743 p3541 : Prop) (h : p2622 ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p2005) ∨ (¬ p2573) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2406)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial25415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory14671 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 4 5) (m.theta 4 6)
  exact rule25415 (meaning t m 2005) (meaning t m 2027) (meaning t m 2406) (meaning t m 2573) (meaning t m 2589) (meaning t m 2622) (meaning t m 2743) (meaning t m 3541) source

end SunPrize.SMT
