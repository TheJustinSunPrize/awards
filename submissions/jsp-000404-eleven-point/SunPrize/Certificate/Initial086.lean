import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory070
import SunPrize.Certificate.Theory071
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule40270 (p3256 p4009 p4200 : Prop) (h : (¬ p3256) ∨ (¬ p4200) ∨ p4009) : (¬ p3256) ∨ (p4009) ∨ (¬ p4200) := by
  classical
  tauto

theorem initial40270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (meaning t m 4009) ∨ (¬ (meaning t m 4200)) := by
  have source := ElevenTheory.theory29526 (m.theta 3 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40270 (meaning t m 3256) (meaning t m 4009) (meaning t m 4200) source

theorem rule40272 (p2027 p2220 p2249 p2951 p2992 p3037 p3414 p3548 p3969 p4348 p5122 : Prop) (h : (¬ p3037) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4348) ∨ (¬ p2220) ∨ (¬ p3548) ∨ (¬ p5122) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3037) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29528 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40272 (meaning t m 2027) (meaning t m 2220) (meaning t m 2249) (meaning t m 2951) (meaning t m 2992) (meaning t m 3037) (meaning t m 3414) (meaning t m 3548) (meaning t m 3969) (meaning t m 4348) (meaning t m 5122) source

theorem rule40273 (p1991 p2027 p2766 p3172 p3941 p4348 p5600 : Prop) (h : (¬ p4348) ∨ (¬ p1991) ∨ (¬ p5600) ∨ (¬ p3172) ∨ p2766 ∨ p2027 ∨ (¬ p3941)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial40273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory29529 t (m.theta 0 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40273 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 3172) (meaning t m 3941) (meaning t m 4348) (meaning t m 5600) source

theorem rule40275 (p3569 p3570 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p3569) ∨ p3570) : (¬ p3569) ∨ (p3570) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial40275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3569)) ∨ (meaning t m 3570) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory29531 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule40275 (meaning t m 3569) (meaning t m 3570) (meaning t m 3644) source

theorem rule40277 (p1975 p2027 p2274 p2383 p2409 p2493 p2578 p3989 : Prop) (h : (¬ p2493) ∨ p2409 ∨ (¬ p2383) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3989) ∨ (¬ p2578)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial40277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory29533 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule40277 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2383) (meaning t m 2409) (meaning t m 2493) (meaning t m 2578) (meaning t m 3989) source

theorem rule40278 (p2027 p2470 p2656 p2727 p3662 p3879 p4610 : Prop) (h : (¬ p2656) ∨ (¬ p3662) ∨ (¬ p2727) ∨ (¬ p3879) ∨ p2027 ∨ (¬ p4610) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial40278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory29534 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule40278 (meaning t m 2027) (meaning t m 2470) (meaning t m 2656) (meaning t m 2727) (meaning t m 3662) (meaning t m 3879) (meaning t m 4610) source

theorem rule40282 (p2383 p3990 p5378 p5379 : Prop) (h : (¬ p5379) ∨ (¬ p2383) ∨ (¬ p3990) ∨ (¬ p5378)) : (¬ p2383) ∨ (¬ p3990) ∨ (¬ p5378) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial40282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 5378)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory29538 (m.theta 0 6) (m.theta 0 9) (m.theta 6 8) (m.theta 6 9)
  exact rule40282 (meaning t m 2383) (meaning t m 3990) (meaning t m 5378) (meaning t m 5379) source

theorem rule40283 (p1982 p2027 p2202 p2440 p3189 p3256 p4111 : Prop) (h : p2027 ∨ (¬ p3256) ∨ p2202 ∨ (¬ p2440) ∨ (¬ p4111) ∨ (¬ p1982) ∨ (¬ p3189)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial40283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory29539 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 8 9)
  exact rule40283 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3189) (meaning t m 3256) (meaning t m 4111) source

theorem rule40286 (p2573 p3646 p3904 p4203 : Prop) (h : (¬ p2573) ∨ (¬ p4203) ∨ (¬ p3904) ∨ (¬ p3646)) : (¬ p2573) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial40286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory29542 (m.theta 0 4) (m.theta 0 5) (m.theta 4 6) (m.theta 5 6)
  exact rule40286 (meaning t m 2573) (meaning t m 3646) (meaning t m 3904) (meaning t m 4203) source

theorem rule40287 (p2156 p2573 p3904 p4203 : Prop) (h : (¬ p2573) ∨ (¬ p4203) ∨ (¬ p3904) ∨ p2156) : (p2156) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial40287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory29543 (m.theta 0 4) (m.theta 0 5) (m.theta 4 6) (m.theta 5 6)
  exact rule40287 (meaning t m 2156) (meaning t m 2573) (meaning t m 3904) (meaning t m 4203) source

theorem rule40288 (p1977 p2027 p2241 p2274 p2765 p3549 p3591 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ p2765 ∨ (¬ p3591) ∨ (¬ p2274) ∨ (¬ p3549)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial40288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory29544 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule40288 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2274) (meaning t m 2765) (meaning t m 3549) (meaning t m 3591) source

theorem rule40289 (p1977 p2027 p2241 p2997 p3097 p3555 p4173 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3555) ∨ p2997 ∨ (¬ p3097)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial40289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory29545 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule40289 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2997) (meaning t m 3097) (meaning t m 3555) (meaning t m 4173) source

theorem rule40290 (p1997 p2027 p2252 p2750 p2766 p2850 p2922 p2952 p3266 p3497 p3541 p3876 p4322 p4335 : Prop) (h : p2766 ∨ (¬ p2750) ∨ (¬ p1997) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3541) ∨ (¬ p2922) ∨ (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4335)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (p2766) ∨ (¬ p2850) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3497) ∨ (¬ p3541) ∨ (¬ p3876) ∨ (¬ p4322) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial40290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory29546 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40290 (meaning t m 1997) (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2766) (meaning t m 2850) (meaning t m 2922) (meaning t m 2952) (meaning t m 3266) (meaning t m 3497) (meaning t m 3541) (meaning t m 3876) (meaning t m 4322) (meaning t m 4335) source

theorem rule40291 (p2027 p2098 p2252 p2750 p2753 p2952 p3609 p3952 p3989 p4348 p4503 : Prop) (h : (¬ p3609) ∨ (¬ p4348) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p4503) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2952) ∨ (¬ p3609) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29547 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40291 (meaning t m 2027) (meaning t m 2098) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2952) (meaning t m 3609) (meaning t m 3952) (meaning t m 3989) (meaning t m 4348) (meaning t m 4503) source

theorem rule40292 (p2027 p2252 p2598 p2750 p2753 p2950 p3156 p3422 p3564 p4120 p4208 p4368 : Prop) (h : (¬ p2950) ∨ (¬ p3156) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p3564) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4208) ∨ (¬ p4368)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2950) ∨ (¬ p3156) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4368) := by
  classical
  tauto

theorem initial40292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4368)) := by
  have source := ElevenTheory.theory29548 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9)
  exact rule40292 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2950) (meaning t m 3156) (meaning t m 3422) (meaning t m 3564) (meaning t m 4120) (meaning t m 4208) (meaning t m 4368) source

theorem rule40293 (p2027 p2241 p2750 p3055 p3367 p3873 : Prop) (h : (¬ p2241) ∨ (¬ p3873) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial40293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory29549 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4)
  exact rule40293 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3055) (meaning t m 3367) (meaning t m 3873) source

theorem rule40296 (p2027 p2210 p2252 p2750 p2963 p2972 p3324 p3954 p4347 p4450 : Prop) (h : (¬ p3954) ∨ (¬ p2210) ∨ (¬ p4450) ∨ (¬ p2252) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2750) ∨ (¬ p4347) ∨ (¬ p2972)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p2972) ∨ (¬ p3324) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial40296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory29552 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule40296 (meaning t m 2027) (meaning t m 2210) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 2972) (meaning t m 3324) (meaning t m 3954) (meaning t m 4347) (meaning t m 4450) source

theorem rule40310 (p2027 p2241 p2750 p2753 p2761 p3516 p3591 p3819 p4026 p4444 p4604 : Prop) (h : (¬ p2241) ∨ (¬ p4604) ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p4444) ∨ (¬ p4026) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p2753) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p3591) ∨ (¬ p3819) ∨ (¬ p4026) ∨ (¬ p4444) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29566 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40310 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 3516) (meaning t m 3591) (meaning t m 3819) (meaning t m 4026) (meaning t m 4444) (meaning t m 4604) source

theorem rule40311 (p2027 p2241 p2341 p2750 p2753 p2860 p3486 p3555 p3659 p3819 p4136 p4555 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3486) ∨ (¬ p2241) ∨ (¬ p3819) ∨ (¬ p2860) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2341) ∨ (¬ p4136) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2341) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4136) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial40311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory29567 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule40311 (meaning t m 2027) (meaning t m 2241) (meaning t m 2341) (meaning t m 2750) (meaning t m 2753) (meaning t m 2860) (meaning t m 3486) (meaning t m 3555) (meaning t m 3659) (meaning t m 3819) (meaning t m 4136) (meaning t m 4555) source

theorem rule40312 (p1977 p2027 p2241 p2633 p3486 p3555 p3570 : Prop) (h : p2027 ∨ (¬ p1977) ∨ (¬ p3570) ∨ (¬ p2241) ∨ p2633 ∨ (¬ p3486) ∨ (¬ p3555)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2633) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial40312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory29568 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule40312 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2633) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) source

theorem rule40313 (p1977 p2027 p2241 p2881 p2938 p3548 p4366 : Prop) (h : p2938 ∨ p2027 ∨ (¬ p2881) ∨ (¬ p1977) ∨ (¬ p2241) ∨ (¬ p3548) ∨ (¬ p4366)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial40313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory29569 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule40313 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2881) (meaning t m 2938) (meaning t m 3548) (meaning t m 4366) source

theorem rule40316 (p2027 p2482 p3874 p3998 p4286 p4730 : Prop) (h : p2027 ∨ (¬ p3874) ∨ (¬ p4730) ∨ (¬ p2482) ∨ (¬ p3998) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2482) ∨ (¬ p3874) ∨ (¬ p3998) ∨ (¬ p4286) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial40316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory29572 t (m.theta 0 4) (m.theta 0 8) (m.theta 2 4) (m.theta 4 8) (m.theta 8 10)
  exact rule40316 (meaning t m 2027) (meaning t m 2482) (meaning t m 3874) (meaning t m 3998) (meaning t m 4286) (meaning t m 4730) source

theorem rule40317 (p2253 p3166 p3860 p5074 : Prop) (h : (¬ p2253) ∨ (¬ p3860) ∨ (¬ p3166) ∨ (¬ p5074)) : (¬ p2253) ∨ (¬ p3166) ∨ (¬ p3860) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial40317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory29573 (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 8)
  exact rule40317 (meaning t m 2253) (meaning t m 3166) (meaning t m 3860) (meaning t m 5074) source

theorem rule40323 (p2027 p2138 p3366 p3449 p3452 p3692 p3694 p4181 p4376 p5122 : Prop) (h : (¬ p2138) ∨ (¬ p4181) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4376) ∨ (¬ p3692) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4181) ∨ (¬ p4376) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29579 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40323 (meaning t m 2027) (meaning t m 2138) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3692) (meaning t m 3694) (meaning t m 4181) (meaning t m 4376) (meaning t m 5122) source

theorem rule40324 (p2027 p3830 p4324 p4366 p4797 p5362 : Prop) (h : (¬ p4797) ∨ (¬ p4366) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p5362)) : (p2027) ∨ (¬ p3830) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4797) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial40324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4797)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory29580 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 2 7) (m.theta 7 9)
  exact rule40324 (meaning t m 2027) (meaning t m 3830) (meaning t m 4324) (meaning t m 4366) (meaning t m 4797) (meaning t m 5362) source

theorem rule40326 (p2027 p2252 p2750 p2952 p3399 p3527 p3690 p3954 p4320 p4666 : Prop) (h : (¬ p2952) ∨ (¬ p4320) ∨ (¬ p4666) ∨ (¬ p3954) ∨ (¬ p3690) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial40326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory29582 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40326 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3399) (meaning t m 3527) (meaning t m 3690) (meaning t m 3954) (meaning t m 4320) (meaning t m 4666) source

theorem rule40328 (p2027 p2241 p2750 p2753 p3276 p3355 p3362 p3591 p4037 p4319 p4381 p4625 : Prop) (h : (¬ p2753) ∨ (¬ p3362) ∨ (¬ p4381) ∨ (¬ p3355) ∨ (¬ p4625) ∨ (¬ p4037) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3591) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3591) ∨ (¬ p4037) ∨ (¬ p4319) ∨ (¬ p4381) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial40328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory29584 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40328 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3591) (meaning t m 4037) (meaning t m 4319) (meaning t m 4381) (meaning t m 4625) source

theorem rule40329 (p2027 p2138 p2417 p2933 p3366 p3399 p3452 p3692 p3694 p3950 p4376 : Prop) (h : p2027 ∨ (¬ p3452) ∨ (¬ p3399) ∨ (¬ p2933) ∨ (¬ p2417) ∨ (¬ p3950) ∨ (¬ p4376) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3694) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29585 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40329 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 2933) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4376) source

theorem rule40330 (p2027 p2138 p3366 p3452 p3694 p3707 p3830 p4376 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3707) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p3830) ∨ (¬ p4376) ∨ (¬ p3694) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3694) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29586 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40330 (meaning t m 2027) (meaning t m 2138) (meaning t m 3366) (meaning t m 3452) (meaning t m 3694) (meaning t m 3707) (meaning t m 3830) (meaning t m 4376) (meaning t m 5123) (meaning t m 5568) source

theorem rule40333 (p2750 p4262 p5317 : Prop) (h : (¬ p2750) ∨ (¬ p4262) ∨ p5317) : (¬ p2750) ∨ (¬ p4262) ∨ (p5317) := by
  classical
  tauto

theorem initial40333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 4262)) ∨ (meaning t m 5317) := by
  have source := ElevenTheory.theory29589 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 8)
  exact rule40333 (meaning t m 2750) (meaning t m 4262) (meaning t m 5317) source

theorem rule40334 (p2027 p2241 p2750 p2753 p3333 p3362 p3389 p3591 p3876 p4037 p4319 p5322 : Prop) (h : (¬ p5322) ∨ (¬ p3333) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3591) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4319) ∨ (¬ p4037) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3591) ∨ (¬ p3876) ∨ (¬ p4037) ∨ (¬ p4319) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial40334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory29590 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 6 9)
  exact rule40334 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3333) (meaning t m 3362) (meaning t m 3389) (meaning t m 3591) (meaning t m 3876) (meaning t m 4037) (meaning t m 4319) (meaning t m 5322) source

theorem rule40335 (p2027 p2241 p2750 p2922 p3540 p3541 p4108 : Prop) (h : (¬ p3541) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p2922) ∨ (¬ p4108) ∨ p2027 ∨ (¬ p3540)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3541) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial40335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory29591 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 7)
  exact rule40335 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2922) (meaning t m 3540) (meaning t m 3541) (meaning t m 4108) source

theorem rule40336 (p2437 p2922 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2922) ∨ p2437) : (p2437) ∨ (¬ p2922) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial40336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory29592 (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule40336 (meaning t m 2437) (meaning t m 2922) (meaning t m 4116) source

theorem rule40339 (p2027 p3452 p3516 p3545 p3817 p4376 p4400 : Prop) (h : (¬ p4400) ∨ (¬ p3817) ∨ (¬ p4376) ∨ (¬ p3545) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3452) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3817) ∨ (¬ p4376) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial40339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory29595 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 7 9)
  exact rule40339 (meaning t m 2027) (meaning t m 3452) (meaning t m 3516) (meaning t m 3545) (meaning t m 3817) (meaning t m 4376) (meaning t m 4400) source

theorem rule40341 (p2027 p2122 p2252 p2396 p2750 p2753 p2774 p2952 p3497 p3692 p3950 : Prop) (h : (¬ p2252) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p2753) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3497) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial40341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory29597 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40341 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2952) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule40343 (p2027 p2252 p2598 p2750 p2753 p2952 p3422 p3497 p3564 p3692 p4330 : Prop) (h : (¬ p4330) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p2750) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2952) ∨ (¬ p3422) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial40343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory29599 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40343 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2952) (meaning t m 3422) (meaning t m 3497) (meaning t m 3564) (meaning t m 3692) (meaning t m 4330) source

theorem rule40344 (p1976 p2027 p2952 p3136 p3877 p3982 p4236 p4312 p5568 : Prop) (h : (¬ p1976) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3136) ∨ p3982 ∨ (¬ p4236) ∨ (¬ p3877) ∨ (¬ p4312) ∨ (¬ p5568)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (p3982) ∨ (¬ p4236) ∨ (¬ p4312) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29600 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10)
  exact rule40344 (meaning t m 1976) (meaning t m 2027) (meaning t m 2952) (meaning t m 3136) (meaning t m 3877) (meaning t m 3982) (meaning t m 4236) (meaning t m 4312) (meaning t m 5568) source

theorem rule40347 (p1975 p2027 p2299 p2409 p2911 p2933 p3093 p3452 p4452 : Prop) (h : (¬ p2299) ∨ (¬ p1975) ∨ (¬ p3452) ∨ (¬ p2933) ∨ (¬ p3093) ∨ p2409 ∨ (¬ p4452) ∨ p2027 ∨ (¬ p2911)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2409) ∨ (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial40347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory29603 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 1 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule40347 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2409) (meaning t m 2911) (meaning t m 2933) (meaning t m 3093) (meaning t m 3452) (meaning t m 4452) source

theorem rule40348 (p2027 p2144 p2241 p2619 p2750 p2753 p3051 p3591 p3923 p4244 p4433 : Prop) (h : (¬ p2619) ∨ (¬ p3923) ∨ (¬ p2144) ∨ (¬ p4433) ∨ (¬ p2241) ∨ (¬ p3591) ∨ (¬ p4244) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4244) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial40348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory29604 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule40348 (meaning t m 2027) (meaning t m 2144) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3051) (meaning t m 3591) (meaning t m 3923) (meaning t m 4244) (meaning t m 4433) source

theorem rule40349 (p1975 p2027 p2252 p2299 p2545 p2741 p2810 p3005 p3172 p3399 p3452 p3527 p4376 : Prop) (h : (¬ p1975) ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2252) ∨ p2545 ∨ (¬ p3005) ∨ (¬ p2810) ∨ (¬ p3452) ∨ (¬ p2299) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p3527)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (p2545) ∨ (¬ p2741) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29605 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule40349 (meaning t m 1975) (meaning t m 2027) (meaning t m 2252) (meaning t m 2299) (meaning t m 2545) (meaning t m 2741) (meaning t m 2810) (meaning t m 3005) (meaning t m 3172) (meaning t m 3399) (meaning t m 3452) (meaning t m 3527) (meaning t m 4376) source

theorem rule40352 (p2027 p2373 p2441 p3426 p3434 p4278 p4428 p4509 : Prop) (h : (¬ p3426) ∨ (¬ p3434) ∨ (¬ p4428) ∨ (¬ p4509) ∨ (¬ p2373) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2441)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2441) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p4278) ∨ (¬ p4428) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial40352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29608 t (m.theta 2 6) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule40352 (meaning t m 2027) (meaning t m 2373) (meaning t m 2441) (meaning t m 3426) (meaning t m 3434) (meaning t m 4278) (meaning t m 4428) (meaning t m 4509) source

theorem rule40358 (p1988 p2027 p2545 p2685 p2810 p3461 p3564 p3579 p3581 : Prop) (h : (¬ p3461) ∨ (¬ p1988) ∨ (¬ p3564) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3581) ∨ p2545 ∨ (¬ p3579) ∨ (¬ p2685)) : (¬ p1988) ∨ (p2027) ∨ (p2545) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3579) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial40358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory29614 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9) (m.theta 9 10)
  exact rule40358 (meaning t m 1988) (meaning t m 2027) (meaning t m 2545) (meaning t m 2685) (meaning t m 2810) (meaning t m 3461) (meaning t m 3564) (meaning t m 3579) (meaning t m 3581) source

theorem rule40359 (p2027 p2138 p2307 p2588 p2781 p3564 p3692 p3694 p4330 : Prop) (h : (¬ p2781) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p4330) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2781) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial40359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory29615 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule40359 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2588) (meaning t m 2781) (meaning t m 3564) (meaning t m 3692) (meaning t m 3694) (meaning t m 4330) source

theorem rule40362 (p2027 p2145 p3156 p3276 p3355 p3362 p4120 p4191 p4208 p4368 : Prop) (h : (¬ p4208) ∨ (¬ p3355) ∨ (¬ p2145) ∨ (¬ p4368) ∨ (¬ p3276) ∨ (¬ p3362) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2145) ∨ (¬ p3156) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p4120) ∨ (¬ p4191) ∨ (¬ p4208) ∨ (¬ p4368) := by
  classical
  tauto

theorem initial40362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4368)) := by
  have source := ElevenTheory.theory29618 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule40362 (meaning t m 2027) (meaning t m 2145) (meaning t m 3156) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 4120) (meaning t m 4191) (meaning t m 4208) (meaning t m 4368) source

theorem rule40365 (p3584 p3746 p5160 : Prop) (h : (¬ p3746) ∨ (¬ p3584) ∨ p5160) : (¬ p3584) ∨ (¬ p3746) ∨ (p5160) := by
  classical
  tauto

theorem initial40365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3746)) ∨ (meaning t m 5160) := by
  have source := ElevenTheory.theory29621 (m.theta 2 4) (m.theta 4 6) (m.theta 4 9)
  exact rule40365 (meaning t m 3584) (meaning t m 3746) (meaning t m 5160) source

theorem rule40371 (p2027 p2145 p2573 p3156 p3333 p3362 p3584 p4120 p4208 p4950 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p2145) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4950) ∨ (¬ p3156) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2573) ∨ (¬ p3156) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4950) := by
  classical
  tauto

theorem initial40371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4950)) := by
  have source := ElevenTheory.theory29627 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9)
  exact rule40371 (meaning t m 2027) (meaning t m 2145) (meaning t m 2573) (meaning t m 3156) (meaning t m 3333) (meaning t m 3362) (meaning t m 3584) (meaning t m 4120) (meaning t m 4208) (meaning t m 4950) source

theorem rule40375 (p1998 p2027 p2210 p2409 p2427 p2881 p3452 p4210 : Prop) (h : (¬ p3452) ∨ p2409 ∨ (¬ p2427) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2210) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial40375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory29631 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule40375 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2409) (meaning t m 2427) (meaning t m 2881) (meaning t m 3452) (meaning t m 4210) source

theorem rule40377 (p1990 p2027 p2114 p2406 p2563 p3379 p3954 : Prop) (h : (¬ p1990) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3379) ∨ p2114 ∨ (¬ p2563) ∨ (¬ p2406)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial40377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory29633 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule40377 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2406) (meaning t m 2563) (meaning t m 3379) (meaning t m 3954) source

theorem rule40378 (p1998 p2027 p2598 p2611 p3641 p4149 p5558 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p5558) ∨ (¬ p3641) ∨ (¬ p2598) ∨ (¬ p4149)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29634 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10)
  exact rule40378 (meaning t m 1998) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 3641) (meaning t m 4149) (meaning t m 5558) source

theorem rule40382 (p2027 p2307 p2781 p2952 p3136 p3461 p4035 p4187 p4236 p4381 p4663 : Prop) (h : (¬ p2781) ∨ (¬ p4187) ∨ (¬ p2307) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p4663) ∨ (¬ p4236) ∨ (¬ p3136) ∨ (¬ p2952) ∨ (¬ p4381) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3461) ∨ (¬ p4035) ∨ (¬ p4187) ∨ (¬ p4236) ∨ (¬ p4381) ∨ (¬ p4663) := by
  classical
  tauto

theorem initial40382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4663)) := by
  have source := ElevenTheory.theory29638 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40382 (meaning t m 2027) (meaning t m 2307) (meaning t m 2781) (meaning t m 2952) (meaning t m 3136) (meaning t m 3461) (meaning t m 4035) (meaning t m 4187) (meaning t m 4236) (meaning t m 4381) (meaning t m 4663) source

theorem rule40383 (p2027 p2417 p2933 p3365 p3366 p3399 p3452 p3877 p3950 p4118 p4376 : Prop) (h : (¬ p2417) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p2933) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p3452) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2933) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29639 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40383 (meaning t m 2027) (meaning t m 2417) (meaning t m 2933) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4376) source

theorem rule40384 (p1990 p2027 p2114 p2563 p2850 p3379 p3954 p4030 : Prop) (h : (¬ p1990) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3379) ∨ (¬ p2563) ∨ (¬ p4030) ∨ p2114 ∨ (¬ p2850)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial40384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory29640 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule40384 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2563) (meaning t m 2850) (meaning t m 3379) (meaning t m 3954) (meaning t m 4030) source

theorem rule40389 (p2027 p3366 p3425 p3449 p3452 p3659 p3692 p4042 p4181 p4376 p5122 : Prop) (h : (¬ p4181) ∨ (¬ p3692) ∨ (¬ p3659) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4376) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4042)) : (p2027) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p4042) ∨ (¬ p4181) ∨ (¬ p4376) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29645 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40389 (meaning t m 2027) (meaning t m 3366) (meaning t m 3425) (meaning t m 3449) (meaning t m 3452) (meaning t m 3659) (meaning t m 3692) (meaning t m 4042) (meaning t m 4181) (meaning t m 4376) (meaning t m 5122) source

theorem rule40392 (p2027 p2417 p2761 p3365 p3389 p3877 p4419 p5123 p5600 : Prop) (h : (¬ p5600) ∨ (¬ p5123) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p2417) ∨ (¬ p4419) ∨ (¬ p3877) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3877) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial40392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory29648 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40392 (meaning t m 2027) (meaning t m 2417) (meaning t m 2761) (meaning t m 3365) (meaning t m 3389) (meaning t m 3877) (meaning t m 4419) (meaning t m 5123) (meaning t m 5600) source

theorem rule40397 (p2027 p2252 p3093 p3319 p3414 p3452 p3553 p4330 p4348 p4810 : Prop) (h : (¬ p3414) ∨ (¬ p4348) ∨ (¬ p3553) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p4810) ∨ (¬ p3093) ∨ (¬ p2252) ∨ (¬ p3452) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2252) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4810) := by
  classical
  tauto

theorem initial40397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4810)) := by
  have source := ElevenTheory.theory29653 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40397 (meaning t m 2027) (meaning t m 2252) (meaning t m 3093) (meaning t m 3319) (meaning t m 3414) (meaning t m 3452) (meaning t m 3553) (meaning t m 4330) (meaning t m 4348) (meaning t m 4810) source

theorem rule40398 (p2027 p2252 p2504 p3093 p3414 p3452 p3553 p3564 p4330 p4348 p4810 : Prop) (h : (¬ p3414) ∨ (¬ p4348) ∨ (¬ p3553) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p4810) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p2504) ∨ (¬ p2252) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4810) := by
  classical
  tauto

theorem initial40398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4810)) := by
  have source := ElevenTheory.theory29654 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40398 (meaning t m 2027) (meaning t m 2252) (meaning t m 2504) (meaning t m 3093) (meaning t m 3414) (meaning t m 3452) (meaning t m 3553) (meaning t m 3564) (meaning t m 4330) (meaning t m 4348) (meaning t m 4810) source

theorem rule40399 (p1990 p2027 p2191 p2192 p2388 p3256 p3857 p4115 p4237 : Prop) (h : (¬ p2192) ∨ (¬ p1990) ∨ (¬ p4115) ∨ (¬ p2191) ∨ p2027 ∨ p2388 ∨ (¬ p3256) ∨ (¬ p4237) ∨ (¬ p3857)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (p2388) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4115) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial40399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory29655 t (m.theta 0 8) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule40399 (meaning t m 1990) (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2388) (meaning t m 3256) (meaning t m 3857) (meaning t m 4115) (meaning t m 4237) source

theorem rule40400 (p2027 p2252 p2470 p2745 p2951 p3136 p3414 p3659 p3904 p4149 p4325 p4348 p5122 : Prop) (h : (¬ p2745) ∨ (¬ p2252) ∨ (¬ p4149) ∨ (¬ p2470) ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p4325) ∨ (¬ p3414) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p4348) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2470) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3414) ∨ (¬ p3659) ∨ (¬ p3904) ∨ (¬ p4149) ∨ (¬ p4325) ∨ (¬ p4348) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29656 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40400 (meaning t m 2027) (meaning t m 2252) (meaning t m 2470) (meaning t m 2745) (meaning t m 2951) (meaning t m 3136) (meaning t m 3414) (meaning t m 3659) (meaning t m 3904) (meaning t m 4149) (meaning t m 4325) (meaning t m 4348) (meaning t m 5122) source

theorem rule40401 (p2027 p2122 p2774 p3172 p3791 p4118 p4444 p4789 p4826 : Prop) (h : (¬ p4789) ∨ (¬ p4118) ∨ (¬ p4826) ∨ (¬ p3172) ∨ (¬ p4444) ∨ (¬ p3791) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3791) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial40401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory29657 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule40401 (meaning t m 2027) (meaning t m 2122) (meaning t m 2774) (meaning t m 3172) (meaning t m 3791) (meaning t m 4118) (meaning t m 4444) (meaning t m 4789) (meaning t m 4826) source

theorem rule40402 (p2027 p2252 p2750 p2952 p3399 p3497 p3631 p3692 p3950 p3954 : Prop) (h : (¬ p3399) ∨ (¬ p2252) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p2750) ∨ (¬ p3950) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3497) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial40402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory29658 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40402 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3399) (meaning t m 3497) (meaning t m 3631) (meaning t m 3692) (meaning t m 3950) (meaning t m 3954) source

theorem rule40403 (p2027 p2138 p2417 p2761 p3389 p3758 p4393 p4419 p5254 : Prop) (h : (¬ p2138) ∨ p2027 ∨ (¬ p5254) ∨ (¬ p3758) ∨ (¬ p2761) ∨ (¬ p4419) ∨ (¬ p2417) ∨ (¬ p4393) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4419) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial40403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29659 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40403 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 2761) (meaning t m 3389) (meaning t m 3758) (meaning t m 4393) (meaning t m 4419) (meaning t m 5254) source

theorem rule40404 (p2027 p2352 p3969 p4134 p5514 p5579 : Prop) (h : p2027 ∨ (¬ p4134) ∨ (¬ p3969) ∨ (¬ p2352) ∨ (¬ p5579) ∨ (¬ p5514)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3969) ∨ (¬ p4134) ∨ (¬ p5514) ∨ (¬ p5579) := by
  classical
  tauto

theorem initial40404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5514)) ∨ (¬ (meaning t m 5579)) := by
  have source := ElevenTheory.theory29660 t (m.theta 4 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule40404 (meaning t m 2027) (meaning t m 2352) (meaning t m 3969) (meaning t m 4134) (meaning t m 5514) (meaning t m 5579) source

theorem rule40405 (p2027 p2166 p2210 p3591 p3918 p4428 p4509 : Prop) (h : (¬ p3591) ∨ (¬ p3918) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p4428) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4428) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial40405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29661 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 2 6) (m.theta 5 6) (m.theta 5 8)
  exact rule40405 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3591) (meaning t m 3918) (meaning t m 4428) (meaning t m 4509) source

theorem rule40406 (p1975 p2027 p2192 p2210 p2274 p2409 p3452 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p2210) ∨ (¬ p3452) ∨ (¬ p2274) ∨ (¬ p2192) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (p2409) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial40406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory29662 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule40406 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2409) (meaning t m 3452) source

theorem rule40407 (p2027 p2252 p2750 p2753 p2761 p2952 p3434 p3471 p3497 p5123 p5568 : Prop) (h : p2027 ∨ (¬ p3434) ∨ (¬ p2952) ∨ (¬ p2753) ∨ (¬ p3497) ∨ (¬ p2252) ∨ (¬ p3471) ∨ (¬ p2750) ∨ (¬ p2761) ∨ (¬ p5568) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3497) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29663 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40407 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 2952) (meaning t m 3434) (meaning t m 3471) (meaning t m 3497) (meaning t m 5123) (meaning t m 5568) source

theorem rule40409 (p2027 p2138 p2307 p2588 p2781 p3888 p4322 p4385 p5250 : Prop) (h : (¬ p2588) ∨ (¬ p3888) ∨ (¬ p5250) ∨ (¬ p2138) ∨ (¬ p4385) ∨ p2027 ∨ (¬ p2781) ∨ (¬ p4322) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2781) ∨ (¬ p3888) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial40409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory29665 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 10) (m.theta 6 7) (m.theta 9 10)
  exact rule40409 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2588) (meaning t m 2781) (meaning t m 3888) (meaning t m 4322) (meaning t m 4385) (meaning t m 5250) source

theorem rule40411 (p2027 p2449 p2761 p3034 p3440 p3544 p4321 : Prop) (h : (¬ p2761) ∨ (¬ p3544) ∨ (¬ p3440) ∨ (¬ p3034) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p4321)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3034) ∨ (¬ p3440) ∨ (¬ p3544) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial40411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3034)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory29667 t (m.theta 1 7) (m.theta 1 8) (m.theta 1 9) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule40411 (meaning t m 2027) (meaning t m 2449) (meaning t m 2761) (meaning t m 3034) (meaning t m 3440) (meaning t m 3544) (meaning t m 4321) source

theorem rule40412 (p2027 p2252 p2573 p2750 p2753 p3266 p3292 p3333 p3362 p3584 p3950 p4331 p4623 p5284 : Prop) (h : (¬ p3950) ∨ (¬ p4623) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p4331) ∨ (¬ p2252) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p5284) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p3950) ∨ (¬ p4331) ∨ (¬ p4623) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29668 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40412 (meaning t m 2027) (meaning t m 2252) (meaning t m 2573) (meaning t m 2750) (meaning t m 2753) (meaning t m 3266) (meaning t m 3292) (meaning t m 3333) (meaning t m 3362) (meaning t m 3584) (meaning t m 3950) (meaning t m 4331) (meaning t m 4623) (meaning t m 5284) source

theorem rule40415 (p2027 p2307 p2781 p3365 p3461 p3877 p3950 p4118 p4187 p4381 : Prop) (h : (¬ p4187) ∨ (¬ p2781) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4381) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4187) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial40415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory29671 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40415 (meaning t m 2027) (meaning t m 2307) (meaning t m 2781) (meaning t m 3365) (meaning t m 3461) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4187) (meaning t m 4381) source

theorem rule40416 (p2027 p2210 p2891 p3055 p4129 p4425 p4736 p4826 p5160 : Prop) (h : (¬ p4425) ∨ p2027 ∨ (¬ p5160) ∨ (¬ p3055) ∨ (¬ p2891) ∨ (¬ p4736) ∨ (¬ p2210) ∨ (¬ p4826) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p4826) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial40416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory29672 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule40416 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3055) (meaning t m 4129) (meaning t m 4425) (meaning t m 4736) (meaning t m 4826) (meaning t m 5160) source

theorem rule40417 (p2027 p2954 p4009 p4120 p4237 p5568 : Prop) (h : (¬ p2954) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p4237) ∨ (¬ p4120) ∨ (¬ p4009)) : (p2027) ∨ (¬ p2954) ∨ (¬ p4009) ∨ (¬ p4120) ∨ (¬ p4237) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29673 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10)
  exact rule40417 (meaning t m 2027) (meaning t m 2954) (meaning t m 4009) (meaning t m 4120) (meaning t m 4237) (meaning t m 5568) source

theorem rule40418 (p2027 p2122 p2252 p2750 p2753 p2774 p2952 p3791 p4208 p4322 p4826 : Prop) (h : (¬ p4826) ∨ p2027 ∨ (¬ p4208) ∨ (¬ p2774) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p4322) ∨ (¬ p2750) ∨ (¬ p3791) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3791) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial40418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory29674 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule40418 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2952) (meaning t m 3791) (meaning t m 4208) (meaning t m 4322) (meaning t m 4826) source

theorem rule40422 (p2027 p2210 p2373 p3591 p3918 p4210 p4428 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p4428) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3918) ∨ (¬ p4210) ∨ (¬ p3591) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4210) ∨ (¬ p4428) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial40422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29678 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule40422 (meaning t m 2027) (meaning t m 2210) (meaning t m 2373) (meaning t m 3591) (meaning t m 3918) (meaning t m 4210) (meaning t m 4428) (meaning t m 4509) source

theorem rule40426 (p2027 p2138 p2573 p3366 p3461 p3519 p3564 p3694 p4376 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p5123) ∨ (¬ p3564) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3694) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p2573) ∨ (¬ p3461) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p3694) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29682 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40426 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3366) (meaning t m 3461) (meaning t m 3519) (meaning t m 3564) (meaning t m 3694) (meaning t m 4376) (meaning t m 5123) (meaning t m 5568) source

theorem rule40428 (p4318 p5580 p5693 : Prop) (h : (¬ p4318) ∨ (¬ p5693) ∨ p5580) : (¬ p4318) ∨ (p5580) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4318)) ∨ (meaning t m 5580) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory29684 (m.theta 1 8) (m.theta 6 8) (m.theta 8 10)
  exact rule40428 (meaning t m 4318) (meaning t m 5580) (meaning t m 5693) source

theorem rule40430 (p2027 p2307 p2588 p2781 p3365 p3564 p3877 p3950 p4118 p4623 : Prop) (h : (¬ p2781) ∨ (¬ p4623) ∨ (¬ p4118) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p3877) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p3564) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial40430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory29686 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule40430 (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 2781) (meaning t m 3365) (meaning t m 3564) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4623) source

theorem rule40431 (p2027 p2138 p2396 p2553 p2573 p3366 p3519 p3692 p3694 p3950 p4376 : Prop) (h : p2027 ∨ (¬ p3694) ∨ (¬ p2573) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p3519) ∨ (¬ p3692) ∨ (¬ p4376) ∨ (¬ p2396) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29687 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40431 (meaning t m 2027) (meaning t m 2138) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3366) (meaning t m 3519) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4376) source

theorem rule40435 (p2027 p2470 p2528 p2952 p3136 p3877 p4041 p4236 p4348 p4419 : Prop) (h : (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4348) ∨ (¬ p3877) ∨ (¬ p4041) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial40435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory29691 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40435 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2952) (meaning t m 3136) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) (meaning t m 4348) (meaning t m 4419) source

theorem rule40436 (p2810 p3019 p4195 : Prop) (h : (¬ p3019) ∨ (¬ p4195) ∨ p2810) : (p2810) ∨ (¬ p3019) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial40436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2810) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory29692 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule40436 (meaning t m 2810) (meaning t m 3019) (meaning t m 4195) source

theorem rule40438 (p2027 p3366 p3425 p3452 p3659 p3707 p3830 p4042 p4376 p5123 p5568 : Prop) (h : (¬ p5123) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3659) ∨ (¬ p3425) ∨ (¬ p4042) ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p5568)) : (p2027) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4042) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29694 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40438 (meaning t m 2027) (meaning t m 3366) (meaning t m 3425) (meaning t m 3452) (meaning t m 3659) (meaning t m 3707) (meaning t m 3830) (meaning t m 4042) (meaning t m 4376) (meaning t m 5123) (meaning t m 5568) source

theorem rule40439 (p2027 p2470 p2528 p3365 p3497 p4315 p4348 p4419 p4905 : Prop) (h : (¬ p4315) ∨ (¬ p4419) ∨ (¬ p3365) ∨ (¬ p2528) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4905) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4348) ∨ (¬ p4419) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial40439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory29695 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40439 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3365) (meaning t m 3497) (meaning t m 4315) (meaning t m 4348) (meaning t m 4419) (meaning t m 4905) source

theorem rule40442 (p2027 p2481 p2509 p3256 p3857 p4121 p4811 : Prop) (h : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p4811) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p4121)) : (p2027) ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial40442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory29698 t (m.theta 0 8) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule40442 (meaning t m 2027) (meaning t m 2481) (meaning t m 2509) (meaning t m 3256) (meaning t m 3857) (meaning t m 4121) (meaning t m 4811) source

theorem rule40443 (p2027 p2088 p2745 p2951 p3136 p4261 p4262 p4590 p4988 : Prop) (h : (¬ p4262) ∨ (¬ p4988) ∨ (¬ p4261) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p2088) ∨ (¬ p4590) ∨ p2027 ∨ (¬ p2745)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4590) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial40443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory29699 t (m.theta 0 5) (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 8 9)
  exact rule40443 (meaning t m 2027) (meaning t m 2088) (meaning t m 2745) (meaning t m 2951) (meaning t m 3136) (meaning t m 4261) (meaning t m 4262) (meaning t m 4590) (meaning t m 4988) source

theorem rule40444 (p1998 p2027 p2210 p2409 p2881 p2891 p3452 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3452) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial40444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory29700 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule40444 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2409) (meaning t m 2881) (meaning t m 2891) (meaning t m 3452) source

theorem rule40446 (p2027 p2573 p2952 p3333 p3362 p3497 p3584 p3692 p4330 p4331 p4789 : Prop) (h : p2027 ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p3584) ∨ (¬ p3692) ∨ (¬ p4331) ∨ (¬ p3497) ∨ (¬ p4330) ∨ (¬ p2952) ∨ (¬ p4789) ∨ (¬ p3333)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3584) ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p4331) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29702 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40446 (meaning t m 2027) (meaning t m 2573) (meaning t m 2952) (meaning t m 3333) (meaning t m 3362) (meaning t m 3497) (meaning t m 3584) (meaning t m 3692) (meaning t m 4330) (meaning t m 4331) (meaning t m 4789) source

theorem rule40453 (p2027 p2396 p2553 p2573 p3365 p3366 p3519 p3877 p3950 p4118 p4376 : Prop) (h : (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29709 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40453 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4376) source

theorem rule40454 (p2027 p2210 p2252 p2313 p2750 p2972 p3552 p3553 p3954 p3983 p4348 p4450 : Prop) (h : (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3983) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3552) ∨ (¬ p2313) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2313) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3552) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p3983) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial40454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory29710 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule40454 (meaning t m 2027) (meaning t m 2210) (meaning t m 2252) (meaning t m 2313) (meaning t m 2750) (meaning t m 2972) (meaning t m 3552) (meaning t m 3553) (meaning t m 3954) (meaning t m 3983) (meaning t m 4348) (meaning t m 4450) source

theorem rule40455 (p1988 p2027 p2210 p2409 p2982 p3452 p3680 p4210 : Prop) (h : (¬ p2982) ∨ (¬ p1988) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3452) ∨ p2409 ∨ (¬ p2210)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p2982) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial40455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory29711 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule40455 (meaning t m 1988) (meaning t m 2027) (meaning t m 2210) (meaning t m 2409) (meaning t m 2982) (meaning t m 3452) (meaning t m 3680) (meaning t m 4210) source

theorem rule40458 (p2027 p2241 p2518 p2528 p2750 p3541 p3591 p3923 p4348 p4503 : Prop) (h : (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3541) ∨ (¬ p2241) ∨ (¬ p3591) ∨ (¬ p2518) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29714 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40458 (meaning t m 2027) (meaning t m 2241) (meaning t m 2518) (meaning t m 2528) (meaning t m 2750) (meaning t m 3541) (meaning t m 3591) (meaning t m 3923) (meaning t m 4348) (meaning t m 4503) source

theorem rule40459 (p2027 p2952 p3276 p3355 p3362 p3497 p3692 p4191 p4330 p4789 : Prop) (h : p2027 ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p2952) ∨ (¬ p3692) ∨ (¬ p3497) ∨ (¬ p4789) ∨ (¬ p3355) ∨ (¬ p3276) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29715 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40459 (meaning t m 2027) (meaning t m 2952) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3497) (meaning t m 3692) (meaning t m 4191) (meaning t m 4330) (meaning t m 4789) source

theorem rule40464 (p2027 p2241 p2417 p2598 p2750 p2753 p3201 p3860 p3950 p4261 : Prop) (h : (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3950) ∨ (¬ p2750) ∨ (¬ p3201) ∨ (¬ p2417) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial40464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory29720 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40464 (meaning t m 2027) (meaning t m 2241) (meaning t m 2417) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3201) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule40465 (p4596 p4687 p4995 : Prop) (h : (¬ p4596) ∨ (¬ p4687) ∨ p4995) : (¬ p4596) ∨ (¬ p4687) ∨ (p4995) := by
  classical
  tauto

theorem initial40465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4687)) ∨ (meaning t m 4995) := by
  have source := ElevenTheory.theory29721 t (m.theta 1 8) (m.theta 4 8) (m.theta 6 8)
  exact rule40465 (meaning t m 4596) (meaning t m 4687) (meaning t m 4995) source

theorem rule40471 (p1983 p2027 p2233 p2573 p3461 p3564 p4381 : Prop) (h : (¬ p3461) ∨ (¬ p3564) ∨ (¬ p2573) ∨ p2233 ∨ p2027 ∨ (¬ p1983) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2233) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial40471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory29727 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40471 (meaning t m 1983) (meaning t m 2027) (meaning t m 2233) (meaning t m 2573) (meaning t m 3461) (meaning t m 3564) (meaning t m 4381) source

theorem rule40472 (p2027 p2138 p2417 p2761 p3389 p3694 p4419 p5123 p5568 : Prop) (h : (¬ p2417) ∨ (¬ p5568) ∨ (¬ p2761) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p5123) ∨ (¬ p4419) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3694) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29728 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40472 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 2761) (meaning t m 3389) (meaning t m 3694) (meaning t m 4419) (meaning t m 5123) (meaning t m 5568) source

theorem rule40475 (p1983 p2027 p2274 p2417 p2765 p3791 p5503 : Prop) (h : (¬ p1983) ∨ (¬ p5503) ∨ (¬ p2274) ∨ p2765 ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3791)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2417) ∨ (p2765) ∨ (¬ p3791) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial40475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory29731 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule40475 (meaning t m 1983) (meaning t m 2027) (meaning t m 2274) (meaning t m 2417) (meaning t m 2765) (meaning t m 3791) (meaning t m 5503) source

theorem rule40478 (p2027 p2252 p2264 p2750 p3093 p3319 p3551 p3947 p3954 p4621 p4849 : Prop) (h : p2027 ∨ (¬ p4621) ∨ (¬ p3319) ∨ (¬ p3954) ∨ (¬ p2264) ∨ (¬ p3093) ∨ (¬ p3551) ∨ (¬ p4849) ∨ (¬ p2252) ∨ (¬ p3947) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2264) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4621) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial40478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory29734 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40478 (meaning t m 2027) (meaning t m 2252) (meaning t m 2264) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3551) (meaning t m 3947) (meaning t m 3954) (meaning t m 4621) (meaning t m 4849) source

theorem rule40482 (p4261 p4340 p5315 : Prop) (h : (¬ p5315) ∨ (¬ p4261) ∨ p4340) : (¬ p4261) ∨ (p4340) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial40482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4261)) ∨ (meaning t m 4340) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory29738 (m.theta 1 8) (m.theta 2 8) (m.theta 8 9)
  exact rule40482 (meaning t m 4261) (meaning t m 4340) (meaning t m 5315) source

theorem rule40483 (p2027 p2573 p3346 p3564 p4330 p4440 : Prop) (h : (¬ p2573) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4440) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial40483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory29739 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9)
  exact rule40483 (meaning t m 2027) (meaning t m 2573) (meaning t m 3346) (meaning t m 3564) (meaning t m 4330) (meaning t m 4440) source

theorem rule40484 (p1983 p2027 p2274 p2765 p3564 p3581 p3791 p4623 p5503 : Prop) (h : (¬ p2274) ∨ (¬ p5503) ∨ p2765 ∨ (¬ p4623) ∨ (¬ p1983) ∨ (¬ p3581) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3791)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3791) ∨ (¬ p4623) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial40484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory29740 t (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 10) (m.theta 7 9)
  exact rule40484 (meaning t m 1983) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 3564) (meaning t m 3581) (meaning t m 3791) (meaning t m 4623) (meaning t m 5503) source

theorem rule40489 (p2027 p3093 p3319 p3366 p3414 p3452 p3553 p4236 p4330 p4348 p4376 : Prop) (h : (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p3553) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3452)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p4236) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29745 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40489 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3414) (meaning t m 3452) (meaning t m 3553) (meaning t m 4236) (meaning t m 4330) (meaning t m 4348) (meaning t m 4376) source

theorem rule40492 (p2027 p2573 p3362 p3414 p3461 p3553 p3564 p4789 p5123 p5558 : Prop) (h : p2027 ∨ (¬ p2573) ∨ (¬ p5123) ∨ (¬ p3564) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5558) ∨ (¬ p3461) ∨ (¬ p4789)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29748 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40492 (meaning t m 2027) (meaning t m 2573) (meaning t m 3362) (meaning t m 3414) (meaning t m 3461) (meaning t m 3553) (meaning t m 3564) (meaning t m 4789) (meaning t m 5123) (meaning t m 5558) source

theorem rule40493 (p2027 p2252 p2598 p2750 p2753 p2911 p2952 p3201 p3690 p4320 p4666 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4666) ∨ (¬ p2952) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3690) ∨ (¬ p2911) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p2952) ∨ (¬ p3201) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial40493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory29749 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40493 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2911) (meaning t m 2952) (meaning t m 3201) (meaning t m 3690) (meaning t m 4320) (meaning t m 4666) source

theorem rule40494 (p2027 p2252 p2417 p2598 p2750 p2753 p2952 p3201 p3497 p3692 p3950 : Prop) (h : (¬ p2750) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2952) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2952) ∨ (¬ p3201) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial40494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory29750 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40494 (meaning t m 2027) (meaning t m 2252) (meaning t m 2417) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2952) (meaning t m 3201) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule40495 (p2027 p2145 p3276 p3355 p3362 p3553 p3556 p4191 p4330 p4333 p4348 : Prop) (h : (¬ p2145) ∨ (¬ p4191) ∨ (¬ p3355) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p4348) ∨ (¬ p3553) ∨ (¬ p4333) ∨ (¬ p4330) ∨ (¬ p3362) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2145) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4333) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial40495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory29751 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 7) (m.theta 4 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule40495 (meaning t m 2027) (meaning t m 2145) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3553) (meaning t m 3556) (meaning t m 4191) (meaning t m 4330) (meaning t m 4333) (meaning t m 4348) source

theorem rule40496 (p2007 p2027 p2766 p3266 p3641 p4425 p5160 : Prop) (h : (¬ p2007) ∨ p2766 ∨ (¬ p4425) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p5160)) : (¬ p2007) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3641) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial40496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory29752 t (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40496 (meaning t m 2007) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3641) (meaning t m 4425) (meaning t m 5160) source

theorem rule40498 (p2027 p2573 p3333 p3362 p3414 p3553 p3584 p4332 p4348 p4789 : Prop) (h : (¬ p3553) ∨ (¬ p4332) ∨ (¬ p3362) ∨ (¬ p3333) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2573) ∨ (¬ p4789) ∨ (¬ p4348) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3584) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29754 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40498 (meaning t m 2027) (meaning t m 2573) (meaning t m 3333) (meaning t m 3362) (meaning t m 3414) (meaning t m 3553) (meaning t m 3584) (meaning t m 4332) (meaning t m 4348) (meaning t m 4789) source

theorem rule40500 (p1984 p2027 p2202 p2440 p3019 p3591 p4228 p4435 : Prop) (h : (¬ p1984) ∨ (¬ p2440) ∨ p2202 ∨ p2027 ∨ (¬ p3591) ∨ (¬ p3019) ∨ (¬ p4228) ∨ (¬ p4435)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3591) ∨ (¬ p4228) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial40500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory29756 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 10)
  exact rule40500 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3019) (meaning t m 3591) (meaning t m 4228) (meaning t m 4435) source

theorem rule40507 (p2027 p2241 p2598 p2750 p2753 p2911 p3032 p3201 p4366 p4391 p5559 : Prop) (h : (¬ p3032) ∨ (¬ p2911) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p5559) ∨ (¬ p2753) ∨ (¬ p4391)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3032) ∨ (¬ p3201) ∨ (¬ p4366) ∨ (¬ p4391) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial40507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory29763 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8)
  exact rule40507 (meaning t m 2027) (meaning t m 2241) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2911) (meaning t m 3032) (meaning t m 3201) (meaning t m 4366) (meaning t m 4391) (meaning t m 5559) source

theorem rule40508 (p1977 p2027 p2241 p2766 p3266 p3834 p4321 : Prop) (h : (¬ p1977) ∨ (¬ p3834) ∨ (¬ p2241) ∨ (¬ p4321) ∨ p2027 ∨ p2766 ∨ (¬ p3266)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3834) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial40508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory29764 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40508 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2766) (meaning t m 3266) (meaning t m 3834) (meaning t m 4321) source

theorem rule40509 (p2027 p2584 p3584 p3654 p4137 p4730 : Prop) (h : (¬ p4137) ∨ (¬ p2584) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4730) ∨ (¬ p3654)) : (p2027) ∨ (¬ p2584) ∨ (¬ p3584) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial40509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory29765 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9)
  exact rule40509 (meaning t m 2027) (meaning t m 2584) (meaning t m 3584) (meaning t m 3654) (meaning t m 4137) (meaning t m 4730) source

theorem rule40510 (p2027 p2241 p2750 p2753 p2774 p2819 p3692 p3860 p3906 p3979 p5122 : Prop) (h : (¬ p3906) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3692) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p2753) ∨ (¬ p5122) ∨ (¬ p2241) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p3979) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29766 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40510 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3692) (meaning t m 3860) (meaning t m 3906) (meaning t m 3979) (meaning t m 5122) source

theorem rule40515 (p1991 p2027 p2202 p2819 p2963 p3324 p3684 p4375 : Prop) (h : (¬ p2963) ∨ (¬ p1991) ∨ p2202 ∨ (¬ p4375) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2819)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2819) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3684) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial40515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory29771 t (m.theta 0 3) (m.theta 2 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 6 8)
  exact rule40515 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2819) (meaning t m 2963) (meaning t m 3324) (meaning t m 3684) (meaning t m 4375) source

theorem rule40519 (p2027 p2417 p2761 p3365 p3366 p3389 p3519 p4195 p4376 p5254 p5717 : Prop) (h : (¬ p4195) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2761) ∨ (¬ p5254) ∨ (¬ p3365) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p5717)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4195) ∨ (¬ p4376) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial40519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory29775 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40519 (meaning t m 2027) (meaning t m 2417) (meaning t m 2761) (meaning t m 3365) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 4195) (meaning t m 4376) (meaning t m 5254) (meaning t m 5717) source

theorem rule40522 (p2027 p2098 p2284 p2753 p3497 p3609 p3645 p3646 p4348 p4877 p4905 : Prop) (h : (¬ p2098) ∨ (¬ p3609) ∨ (¬ p4877) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p4348) ∨ (¬ p2284) ∨ (¬ p4905) ∨ (¬ p3646) ∨ (¬ p3645) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2284) ∨ (¬ p2753) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4348) ∨ (¬ p4877) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial40522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory29778 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40522 (meaning t m 2027) (meaning t m 2098) (meaning t m 2284) (meaning t m 2753) (meaning t m 3497) (meaning t m 3609) (meaning t m 3645) (meaning t m 3646) (meaning t m 4348) (meaning t m 4877) (meaning t m 4905) source

theorem rule40523 (p1988 p2027 p2409 p2417 p2761 p2933 p3399 p3452 : Prop) (h : (¬ p2761) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p2933) ∨ (¬ p1988) ∨ (¬ p3399) ∨ (¬ p3452) ∨ p2409) : (¬ p1988) ∨ (p2027) ∨ (p2409) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial40523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory29779 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule40523 (meaning t m 1988) (meaning t m 2027) (meaning t m 2409) (meaning t m 2417) (meaning t m 2761) (meaning t m 2933) (meaning t m 3399) (meaning t m 3452) source

theorem rule40525 (p2027 p2284 p2753 p3362 p3389 p3497 p3641 p3645 p3646 p3876 p4158 p4877 : Prop) (h : (¬ p2284) ∨ (¬ p3641) ∨ (¬ p4877) ∨ (¬ p3497) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p4158) ∨ (¬ p3389) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3497) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3876) ∨ (¬ p4158) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial40525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory29781 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule40525 (meaning t m 2027) (meaning t m 2284) (meaning t m 2753) (meaning t m 3362) (meaning t m 3389) (meaning t m 3497) (meaning t m 3641) (meaning t m 3645) (meaning t m 3646) (meaning t m 3876) (meaning t m 4158) (meaning t m 4877) source

theorem rule40527 (p2027 p2363 p2963 p3362 p3389 p3641 p3876 p4118 p4196 p4596 p4789 : Prop) (h : (¬ p4196) ∨ (¬ p4596) ∨ (¬ p3641) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p4789) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p3362) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29783 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule40527 (meaning t m 2027) (meaning t m 2363) (meaning t m 2963) (meaning t m 3362) (meaning t m 3389) (meaning t m 3641) (meaning t m 3876) (meaning t m 4118) (meaning t m 4196) (meaning t m 4596) (meaning t m 4789) source

theorem rule40529 (p2027 p2145 p2284 p2417 p2598 p3201 p3646 p3951 p4208 : Prop) (h : (¬ p3951) ∨ p2027 ∨ (¬ p2145) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p2284) ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial40529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory29785 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9)
  exact rule40529 (meaning t m 2027) (meaning t m 2145) (meaning t m 2284) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3646) (meaning t m 3951) (meaning t m 4208) source

theorem rule40530 (p2027 p3399 p3527 p3834 p4666 p5358 : Prop) (h : (¬ p4666) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p5358) ∨ (¬ p3834)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3834) ∨ (¬ p4666) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial40530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory29786 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40530 (meaning t m 2027) (meaning t m 3399) (meaning t m 3527) (meaning t m 3834) (meaning t m 4666) (meaning t m 5358) source

theorem rule40532 (p2027 p2098 p2963 p3324 p4236 p4503 p4804 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4503) ∨ (¬ p4804) ∨ (¬ p4236) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4236) ∨ (¬ p4503) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial40532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory29788 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8)
  exact rule40532 (meaning t m 2027) (meaning t m 2098) (meaning t m 2963) (meaning t m 3324) (meaning t m 4236) (meaning t m 4503) (meaning t m 4804) source

theorem rule40533 (p2027 p2363 p2911 p4278 p4445 p4503 : Prop) (h : (¬ p4503) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4445) ∨ (¬ p2911) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29789 t (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40533 (meaning t m 2027) (meaning t m 2363) (meaning t m 2911) (meaning t m 4278) (meaning t m 4445) (meaning t m 4503) source

theorem rule40542 (p2027 p2252 p2459 p2657 p2717 p2750 p2753 p3471 p3574 p4137 p4604 : Prop) (h : (¬ p3471) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p4604) ∨ (¬ p2753) ∨ (¬ p2657) ∨ (¬ p4137) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29798 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40542 (meaning t m 2027) (meaning t m 2252) (meaning t m 2459) (meaning t m 2657) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3574) (meaning t m 4137) (meaning t m 4604) source

theorem rule40544 (p1977 p2027 p2241 p2459 p2633 p3860 p4261 : Prop) (h : (¬ p1977) ∨ p2027 ∨ p2633 ∨ (¬ p3860) ∨ (¬ p2459) ∨ (¬ p2241) ∨ (¬ p4261)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial40544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory29800 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40544 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2633) (meaning t m 3860) (meaning t m 4261) source

theorem rule40545 (p1990 p2027 p2459 p2633 p3097 p3266 p4025 p4191 : Prop) (h : (¬ p3097) ∨ (¬ p4191) ∨ (¬ p4025) ∨ (¬ p1990) ∨ (¬ p2459) ∨ p2027 ∨ p2633 ∨ (¬ p3266)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3266) ∨ (¬ p4025) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial40545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory29801 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule40545 (meaning t m 1990) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3097) (meaning t m 3266) (meaning t m 4025) (meaning t m 4191) source

theorem rule40546 (p1982 p2027 p2409 p2459 p2518 p4149 p5558 : Prop) (h : (¬ p2459) ∨ p2409 ∨ (¬ p1982) ∨ (¬ p5558) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p2518)) : (¬ p1982) ∨ (p2027) ∨ (p2409) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (¬ p4149) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29802 t (m.theta 1 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40546 (meaning t m 1982) (meaning t m 2027) (meaning t m 2409) (meaning t m 2459) (meaning t m 2518) (meaning t m 4149) (meaning t m 5558) source

theorem rule40547 (p1977 p2027 p2241 p2459 p2633 p3032 p3919 p4118 p4366 : Prop) (h : (¬ p1977) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2459) ∨ p2633 ∨ (¬ p4118) ∨ (¬ p3919) ∨ (¬ p4366) ∨ (¬ p3032)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3032) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial40547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory29803 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40547 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2633) (meaning t m 3032) (meaning t m 3919) (meaning t m 4118) (meaning t m 4366) source

theorem rule40548 (p2027 p2177 p2315 p2459 p3857 p3961 : Prop) (h : (¬ p2177) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p2315) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p2459) ∨ (¬ p3857) ∨ (¬ p3961) := by
  classical
  tauto

theorem initial40548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) := by
  have source := ElevenTheory.theory29804 t (m.theta 0 7) (m.theta 0 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule40548 (meaning t m 2027) (meaning t m 2177) (meaning t m 2315) (meaning t m 2459) (meaning t m 3857) (meaning t m 3961) source

theorem rule40550 (p2027 p2252 p2750 p3073 p3414 p3449 p3553 p3954 p5118 p5558 : Prop) (h : p2027 ∨ (¬ p5118) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p2252) ∨ (¬ p5558) ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p3414) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3414) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29806 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40550 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 3073) (meaning t m 3414) (meaning t m 3449) (meaning t m 3553) (meaning t m 3954) (meaning t m 5118) (meaning t m 5558) source

theorem rule40551 (p1982 p2027 p2148 p2341 p3146 p3941 p4188 p4988 p5612 : Prop) (h : (¬ p2341) ∨ p2148 ∨ (¬ p1982) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3941) ∨ (¬ p5612) ∨ (¬ p4188)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2341) ∨ (¬ p3146) ∨ (¬ p3941) ∨ (¬ p4188) ∨ (¬ p4988) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial40551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory29807 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40551 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2341) (meaning t m 3146) (meaning t m 3941) (meaning t m 4188) (meaning t m 4988) (meaning t m 5612) source

theorem rule40555 (p1982 p2027 p2148 p2619 p3051 p3146 p4244 : Prop) (h : p2027 ∨ p2148 ∨ (¬ p3051) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p4244) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3146) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial40555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory29811 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule40555 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2619) (meaning t m 3051) (meaning t m 3146) (meaning t m 4244) source

theorem rule40558 (p4034 p4210 : Prop) (h : p4034 ∨ p4210) : (p4034) ∨ (p4210) := by
  classical
  tauto

theorem initial40558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4034) ∨ (meaning t m 4210) := by
  have source := ElevenTheory.theory29814 (m.theta 1 5) (m.theta 4 5)
  exact rule40558 (meaning t m 4034) (meaning t m 4210) source

theorem rule40560 (p2459 p3256 p4378 : Prop) (h : (¬ p2459) ∨ (¬ p4378) ∨ p3256) : (¬ p2459) ∨ (p3256) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial40560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (meaning t m 3256) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory29816 (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40560 (meaning t m 2459) (meaning t m 3256) (meaning t m 4378) source

theorem rule40561 (p1986 p2027 p2114 p2922 p3379 p3876 p3954 : Prop) (h : (¬ p3954) ∨ p2114 ∨ p2027 ∨ (¬ p2922) ∨ (¬ p1986) ∨ (¬ p3379) ∨ (¬ p3876)) : (¬ p1986) ∨ (p2027) ∨ (p2114) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3876) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial40561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory29817 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule40561 (meaning t m 1986) (meaning t m 2027) (meaning t m 2114) (meaning t m 2922) (meaning t m 3379) (meaning t m 3876) (meaning t m 3954) source

theorem rule40563 (p2027 p2132 p2579 p2619 p2655 p3016 p3146 p3359 p4022 p4604 p4789 : Prop) (h : (¬ p4022) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3359) ∨ (¬ p4789) ∨ (¬ p3146) ∨ (¬ p2619) ∨ (¬ p3016) ∨ (¬ p2655) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29819 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40563 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2619) (meaning t m 2655) (meaning t m 3016) (meaning t m 3146) (meaning t m 3359) (meaning t m 4022) (meaning t m 4604) (meaning t m 4789) source

theorem rule40564 (p2027 p2657 p2717 p3359 p3471 p3941 p4425 p4789 p5119 : Prop) (h : (¬ p2717) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p4789) ∨ (¬ p3941) ∨ (¬ p2657) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2717) ∨ (¬ p3359) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29820 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40564 (meaning t m 2027) (meaning t m 2657) (meaning t m 2717) (meaning t m 3359) (meaning t m 3471) (meaning t m 3941) (meaning t m 4425) (meaning t m 4789) (meaning t m 5119) source

theorem rule40566 (p2027 p2252 p2459 p2579 p2655 p2717 p2750 p2753 p3016 p3359 p3471 p4697 : Prop) (h : (¬ p3016) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2459) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p2579) ∨ (¬ p4697) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3471) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial40566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory29822 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40566 (meaning t m 2027) (meaning t m 2252) (meaning t m 2459) (meaning t m 2579) (meaning t m 2655) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3016) (meaning t m 3359) (meaning t m 3471) (meaning t m 4697) source

theorem rule40567 (p2027 p2252 p2579 p2655 p2717 p2750 p2753 p3471 p3941 p4137 p4191 p5119 : Prop) (h : (¬ p2717) ∨ (¬ p2753) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p2655) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29823 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40567 (meaning t m 2027) (meaning t m 2252) (meaning t m 2579) (meaning t m 2655) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3941) (meaning t m 4137) (meaning t m 4191) (meaning t m 5119) source

theorem rule40568 (p2027 p2144 p2252 p2750 p2753 p3051 p3105 p3292 p3461 p4244 p4397 p5284 : Prop) (h : (¬ p3292) ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p2750) ∨ (¬ p5284) ∨ (¬ p2144) ∨ (¬ p3461) ∨ (¬ p4397) ∨ (¬ p3051) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3105) ∨ (¬ p3292) ∨ (¬ p3461) ∨ (¬ p4244) ∨ (¬ p4397) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29824 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 9) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule40568 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 3051) (meaning t m 3105) (meaning t m 3292) (meaning t m 3461) (meaning t m 4244) (meaning t m 4397) (meaning t m 5284) source

theorem rule40570 (p2027 p2252 p2341 p2657 p2750 p2753 p3434 p3574 p3659 p3819 p4137 p4625 : Prop) (h : (¬ p2753) ∨ (¬ p2341) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3659) ∨ (¬ p3434) ∨ (¬ p3574) ∨ (¬ p4625) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3819)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2341) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3434) ∨ (¬ p3574) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial40570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory29826 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40570 (meaning t m 2027) (meaning t m 2252) (meaning t m 2341) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3434) (meaning t m 3574) (meaning t m 3659) (meaning t m 3819) (meaning t m 4137) (meaning t m 4625) source

theorem rule40571 (p1982 p2027 p2114 p2210 p2619 p3146 p3954 p4243 : Prop) (h : (¬ p2210) ∨ (¬ p4243) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p1982) ∨ p2114 ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3954) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial40571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory29827 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule40571 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2619) (meaning t m 3146) (meaning t m 3954) (meaning t m 4243) source

theorem rule40575 (p2027 p3449 p3659 p4366 p4797 p5307 : Prop) (h : (¬ p5307) ∨ (¬ p3659) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4797) ∨ (¬ p4366)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3659) ∨ (¬ p4366) ∨ (¬ p4797) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial40575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4797)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory29831 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8)
  exact rule40575 (meaning t m 2027) (meaning t m 3449) (meaning t m 3659) (meaning t m 4366) (meaning t m 4797) (meaning t m 5307) source

theorem rule40576 (p2027 p2252 p2657 p2750 p2753 p2761 p3516 p3574 p3819 p4137 p4444 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p3574) ∨ (¬ p2761) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p2753) ∨ (¬ p3819) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p3574) ∨ (¬ p3819) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29832 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40576 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 3516) (meaning t m 3574) (meaning t m 3819) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) source

theorem rule40578 (p2027 p2252 p2341 p2459 p2657 p2750 p2753 p3266 p3574 p3819 p5254 p5514 : Prop) (h : p2027 ∨ (¬ p3574) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p3819) ∨ (¬ p3266) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p5514) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3574) ∨ (¬ p3819) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial40578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory29834 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule40578 (meaning t m 2027) (meaning t m 2252) (meaning t m 2341) (meaning t m 2459) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3266) (meaning t m 3574) (meaning t m 3819) (meaning t m 5254) (meaning t m 5514) source

theorem rule40580 (p2027 p2241 p2341 p2459 p2750 p2753 p3266 p3591 p3819 p4435 p5254 : Prop) (h : (¬ p2241) ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p5254) ∨ (¬ p2753) ∨ (¬ p3819) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4435) ∨ (¬ p2341) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3591) ∨ (¬ p3819) ∨ (¬ p4435) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial40580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29836 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule40580 (meaning t m 2027) (meaning t m 2241) (meaning t m 2341) (meaning t m 2459) (meaning t m 2750) (meaning t m 2753) (meaning t m 3266) (meaning t m 3591) (meaning t m 3819) (meaning t m 4435) (meaning t m 5254) source

theorem rule40581 (p2027 p2241 p2341 p2750 p2753 p3434 p3591 p3659 p3819 p4026 p4625 : Prop) (h : (¬ p2753) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p4026) ∨ (¬ p3819) ∨ (¬ p3659) ∨ (¬ p3434) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2341) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3434) ∨ (¬ p3591) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4026) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial40581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory29837 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40581 (meaning t m 2027) (meaning t m 2241) (meaning t m 2341) (meaning t m 2750) (meaning t m 2753) (meaning t m 3434) (meaning t m 3591) (meaning t m 3659) (meaning t m 3819) (meaning t m 4026) (meaning t m 4625) source

theorem rule40583 (p2027 p2573 p3156 p3879 p3904 p4120 p4717 : Prop) (h : (¬ p2573) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p3904) ∨ (¬ p4717) ∨ (¬ p3879) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3156) ∨ (¬ p3879) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial40583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory29839 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule40583 (meaning t m 2027) (meaning t m 2573) (meaning t m 3156) (meaning t m 3879) (meaning t m 3904) (meaning t m 4120) (meaning t m 4717) source

theorem rule40585 (p2027 p2241 p2750 p4181 p4416 p5316 p5590 : Prop) (h : (¬ p2750) ∨ (¬ p5316) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4416) ∨ (¬ p4181) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p4181) ∨ (¬ p4416) ∨ (¬ p5316) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial40585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 5316)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory29841 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 8 10)
  exact rule40585 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 4181) (meaning t m 4416) (meaning t m 5316) (meaning t m 5590) source

theorem rule40586 (p2027 p2098 p2241 p2750 p2753 p3266 p3609 p4366 p4442 p4831 : Prop) (h : (¬ p4831) ∨ (¬ p2098) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3609) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p4442) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial40586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory29842 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule40586 (meaning t m 2027) (meaning t m 2098) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3266) (meaning t m 3609) (meaning t m 4366) (meaning t m 4442) (meaning t m 4831) source

theorem rule40588 (p2001 p2027 p2114 p3073 p3449 p3692 p3954 : Prop) (h : p2114 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3073) ∨ (¬ p2001)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial40588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory29844 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule40588 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 3073) (meaning t m 3449) (meaning t m 3692) (meaning t m 3954) source

theorem rule40590 (p2027 p2241 p2459 p2717 p2750 p2753 p3471 p3860 p5118 p5693 : Prop) (h : (¬ p3471) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory29846 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40590 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3860) (meaning t m 5118) (meaning t m 5693) source

theorem rule40591 (p2027 p2241 p2459 p2717 p2750 p2753 p3471 p3591 p4026 p4604 : Prop) (h : (¬ p3471) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2717) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29847 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40591 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) source

theorem rule40592 (p2027 p2098 p2753 p2901 p3497 p3556 p3609 p3645 p4134 p4347 p4877 : Prop) (h : (¬ p4347) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p2901) ∨ (¬ p4877) ∨ (¬ p3497) ∨ (¬ p2098) ∨ (¬ p4134) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2753) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial40592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory29848 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule40592 (meaning t m 2027) (meaning t m 2098) (meaning t m 2753) (meaning t m 2901) (meaning t m 3497) (meaning t m 3556) (meaning t m 3609) (meaning t m 3645) (meaning t m 4134) (meaning t m 4347) (meaning t m 4877) source

theorem rule40596 (p3412 p4632 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p3412) ∨ p4632) : (¬ p3412) ∨ (p4632) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial40596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3412)) ∨ (meaning t m 4632) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory29852 t (m.theta 1 5) (m.theta 3 5) (m.theta 4 5)
  exact rule40596 (meaning t m 3412) (meaning t m 4632) (meaning t m 4705) source

theorem rule40597 (p3051 p3370 p3412 p4320 : Prop) (h : (¬ p3412) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4320)) : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3412) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial40597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory29853 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule40597 (meaning t m 3051) (meaning t m 3370) (meaning t m 3412) (meaning t m 4320) source

theorem rule40598 (p2027 p2210 p3156 p3860 p3906 p4957 : Prop) (h : (¬ p3906) ∨ (¬ p4957) ∨ (¬ p2210) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3860)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3156) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial40598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory29854 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 8)
  exact rule40598 (meaning t m 2027) (meaning t m 2210) (meaning t m 3156) (meaning t m 3860) (meaning t m 3906) (meaning t m 4957) source

theorem rule40602 (p1982 p2027 p2132 p2611 p3105 p3680 p4444 : Prop) (h : p2611 ∨ (¬ p1982) ∨ (¬ p2132) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p3105) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial40602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory29858 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40602 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 3105) (meaning t m 3680) (meaning t m 4444) source

theorem rule40607 (p2027 p2252 p2750 p2761 p3073 p3292 p3449 p3954 p4669 p5284 : Prop) (h : (¬ p3073) ∨ (¬ p2252) ∨ (¬ p3449) ∨ (¬ p5284) ∨ (¬ p2761) ∨ (¬ p3954) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2761) ∨ (¬ p3073) ∨ (¬ p3292) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4669) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29863 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40607 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2761) (meaning t m 3073) (meaning t m 3292) (meaning t m 3449) (meaning t m 3954) (meaning t m 4669) (meaning t m 5284) source

theorem rule40609 (p2027 p2132 p2860 p3414 p3737 p3947 p4381 p4789 p5250 : Prop) (h : (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5250) ∨ (¬ p2132) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p3737)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3414) ∨ (¬ p3737) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial40609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory29865 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40609 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3414) (meaning t m 3737) (meaning t m 3947) (meaning t m 4381) (meaning t m 4789) (meaning t m 5250) source

theorem rule40610 (p2027 p2132 p2252 p2619 p2750 p2753 p2963 p3969 p4037 p4191 p5119 : Prop) (h : (¬ p2750) ∨ (¬ p5119) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p4191) ∨ (¬ p2132) ∨ (¬ p4037) ∨ (¬ p2252) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p3969)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29866 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40610 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3969) (meaning t m 4037) (meaning t m 4191) (meaning t m 5119) source

theorem rule40611 (p2027 p2717 p2952 p3471 p3941 p4208 p4322 p4789 p5119 : Prop) (h : (¬ p3471) ∨ (¬ p4322) ∨ (¬ p2717) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p4789) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29867 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40611 (meaning t m 2027) (meaning t m 2717) (meaning t m 2952) (meaning t m 3471) (meaning t m 3941) (meaning t m 4208) (meaning t m 4322) (meaning t m 4789) (meaning t m 5119) source

theorem rule40612 (p2027 p2098 p2952 p3570 p3609 p4133 p4320 p4347 p4789 : Prop) (h : (¬ p2098) ∨ (¬ p4133) ∨ (¬ p2952) ∨ (¬ p4320) ∨ (¬ p3570) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p3609) ∨ (¬ p4133) ∨ (¬ p4320) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29868 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40612 (meaning t m 2027) (meaning t m 2098) (meaning t m 2952) (meaning t m 3570) (meaning t m 3609) (meaning t m 4133) (meaning t m 4320) (meaning t m 4347) (meaning t m 4789) source

theorem rule40614 (p2027 p2528 p2598 p2963 p3568 p3641 p4107 p4669 p4789 : Prop) (h : (¬ p2963) ∨ (¬ p4789) ∨ (¬ p3641) ∨ (¬ p4669) ∨ (¬ p2598) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3641) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29870 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40614 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2963) (meaning t m 3568) (meaning t m 3641) (meaning t m 4107) (meaning t m 4669) (meaning t m 4789) source

theorem rule40615 (p2027 p2528 p2598 p2761 p2787 p3641 p3946 p4191 p4669 : Prop) (h : (¬ p2528) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2787) ∨ (¬ p4669) ∨ (¬ p3641) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2761) ∨ (¬ p2787) ∨ (¬ p3641) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory29871 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40615 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2761) (meaning t m 2787) (meaning t m 3641) (meaning t m 3946) (meaning t m 4191) (meaning t m 4669) source

theorem rule40617 (p2027 p2299 p2470 p2528 p2963 p3362 p3568 p3692 p4789 p4902 : Prop) (h : (¬ p3362) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p4902) ∨ (¬ p4789) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3692) ∨ (¬ p4789) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29873 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule40617 (meaning t m 2027) (meaning t m 2299) (meaning t m 2470) (meaning t m 2528) (meaning t m 2963) (meaning t m 3362) (meaning t m 3568) (meaning t m 3692) (meaning t m 4789) (meaning t m 4902) source

theorem rule40618 (p2027 p3032 p3553 p3631 p3692 p4443 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p3553) ∨ (¬ p3032) ∨ p2027 ∨ (¬ p4443) ∨ (¬ p3692) ∨ (¬ p3631)) : (p2027) ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29874 t (m.theta 1 7) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40618 (meaning t m 2027) (meaning t m 3032) (meaning t m 3553) (meaning t m 3631) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule40619 (p2027 p2230 p2241 p2373 p2750 p2753 p3146 p3362 p3860 p5118 p5693 : Prop) (h : (¬ p3146) ∨ (¬ p5118) ∨ (¬ p2230) ∨ (¬ p3860) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p2241) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p5693)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2373) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3362) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory29875 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40619 (meaning t m 2027) (meaning t m 2230) (meaning t m 2241) (meaning t m 2373) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3362) (meaning t m 3860) (meaning t m 5118) (meaning t m 5693) source

theorem rule40620 (p2027 p2230 p2252 p2373 p2750 p2753 p2963 p3146 p3362 p3568 p4107 p4669 : Prop) (h : (¬ p3146) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2753) ∨ (¬ p3568) ∨ (¬ p2963) ∨ (¬ p2252) ∨ (¬ p4669) ∨ (¬ p4107) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3146) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory29876 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40620 (meaning t m 2027) (meaning t m 2230) (meaning t m 2252) (meaning t m 2373) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3146) (meaning t m 3362) (meaning t m 3568) (meaning t m 4107) (meaning t m 4669) source

theorem rule40621 (p2010 p2027 p2481 p2633 p3201 p3874 p3941 p5590 : Prop) (h : (¬ p3201) ∨ (¬ p2481) ∨ (¬ p3874) ∨ p2027 ∨ p2633 ∨ (¬ p3941) ∨ (¬ p2010) ∨ (¬ p5590)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2481) ∨ (p2633) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3941) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial40621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory29877 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10)
  exact rule40621 (meaning t m 2010) (meaning t m 2027) (meaning t m 2481) (meaning t m 2633) (meaning t m 3201) (meaning t m 3874) (meaning t m 3941) (meaning t m 5590) source

theorem rule40624 (p2027 p2470 p2952 p3333 p3362 p3690 p3874 p4320 p4638 p4789 : Prop) (h : (¬ p3690) ∨ (¬ p2952) ∨ (¬ p3874) ∨ (¬ p4638) ∨ (¬ p4789) ∨ (¬ p3362) ∨ (¬ p4320) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p3333)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2952) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3690) ∨ (¬ p3874) ∨ (¬ p4320) ∨ (¬ p4638) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29880 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule40624 (meaning t m 2027) (meaning t m 2470) (meaning t m 2952) (meaning t m 3333) (meaning t m 3362) (meaning t m 3690) (meaning t m 3874) (meaning t m 4320) (meaning t m 4638) (meaning t m 4789) source

theorem rule40625 (p2010 p2027 p2611 p3201 p3276 p3355 p3362 p5158 p5387 : Prop) (h : (¬ p2010) ∨ (¬ p3355) ∨ p2027 ∨ p2611 ∨ (¬ p3276) ∨ (¬ p3362) ∨ (¬ p3201) ∨ (¬ p5387) ∨ (¬ p5158)) : (¬ p2010) ∨ (p2027) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p5158) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial40625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 5158)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory29881 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 9) (m.theta 4 7) (m.theta 4 9) (m.theta 9 10)
  exact rule40625 (meaning t m 2010) (meaning t m 2027) (meaning t m 2611) (meaning t m 3201) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 5158) (meaning t m 5387) source

theorem rule40628 (p2027 p2145 p2449 p2470 p3201 p3362 p3556 p3690 p3874 p4653 : Prop) (h : (¬ p3556) ∨ (¬ p3201) ∨ (¬ p2470) ∨ (¬ p4653) ∨ p2027 ∨ (¬ p2145) ∨ (¬ p2449) ∨ (¬ p3362) ∨ (¬ p3874) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2449) ∨ (¬ p2470) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3874) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial40628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory29884 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9)
  exact rule40628 (meaning t m 2027) (meaning t m 2145) (meaning t m 2449) (meaning t m 2470) (meaning t m 3201) (meaning t m 3362) (meaning t m 3556) (meaning t m 3690) (meaning t m 3874) (meaning t m 4653) source

theorem rule40631 (p2027 p2145 p2352 p2459 p2598 p3422 p4118 p4120 p4133 p4311 : Prop) (h : (¬ p3422) ∨ (¬ p2145) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4311) ∨ (¬ p2598) ∨ (¬ p2459) ∨ (¬ p4120) ∨ (¬ p4133) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4133) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial40631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory29887 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40631 (meaning t m 2027) (meaning t m 2145) (meaning t m 2352) (meaning t m 2459) (meaning t m 2598) (meaning t m 3422) (meaning t m 4118) (meaning t m 4120) (meaning t m 4133) (meaning t m 4311) source

theorem rule40632 (p2027 p2145 p2459 p2573 p3362 p3584 p3641 p4118 p4120 p4311 p4420 : Prop) (h : (¬ p4420) ∨ (¬ p2459) ∨ (¬ p2145) ∨ (¬ p4120) ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p3641) ∨ (¬ p4118) ∨ (¬ p3584) ∨ (¬ p4311) ∨ p2027) : (p2027) ∨ (¬ p2145) ∨ (¬ p2459) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial40632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory29888 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40632 (meaning t m 2027) (meaning t m 2145) (meaning t m 2459) (meaning t m 2573) (meaning t m 3362) (meaning t m 3584) (meaning t m 3641) (meaning t m 4118) (meaning t m 4120) (meaning t m 4311) (meaning t m 4420) source

theorem rule40633 (p2027 p2352 p2598 p2952 p3422 p3570 p4133 p4320 p4789 : Prop) (h : (¬ p3422) ∨ (¬ p4133) ∨ (¬ p3570) ∨ (¬ p2952) ∨ (¬ p2598) ∨ (¬ p4789) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3422) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29889 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule40633 (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 2952) (meaning t m 3422) (meaning t m 3570) (meaning t m 4133) (meaning t m 4320) (meaning t m 4789) source

theorem rule40634 (p2027 p2241 p2553 p2598 p2750 p2753 p3422 p3923 p4366 p4452 p4501 : Prop) (h : (¬ p2553) ∨ (¬ p4452) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3923) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3923) ∨ (¬ p4366) ∨ (¬ p4452) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial40634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory29890 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule40634 (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3422) (meaning t m 3923) (meaning t m 4366) (meaning t m 4452) (meaning t m 4501) source

theorem rule40635 (p2027 p2241 p2573 p2750 p2753 p3362 p3548 p3584 p3641 p4366 p4420 : Prop) (h : (¬ p3362) ∨ (¬ p3548) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4420) ∨ (¬ p3641) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2573) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4366) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial40635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory29891 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8)
  exact rule40635 (meaning t m 2027) (meaning t m 2241) (meaning t m 2573) (meaning t m 2750) (meaning t m 2753) (meaning t m 3362) (meaning t m 3548) (meaning t m 3584) (meaning t m 3641) (meaning t m 4366) (meaning t m 4420) source

theorem rule40637 (p2027 p2241 p2598 p2750 p2753 p3641 p3834 p3847 p4149 p5119 p5284 : Prop) (h : (¬ p5119) ∨ (¬ p2598) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p2750) ∨ (¬ p3847) ∨ (¬ p2753) ∨ (¬ p2241) ∨ (¬ p5284) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4149) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29893 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 4) (m.theta 3 9) (m.theta 4 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40637 (meaning t m 2027) (meaning t m 2241) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3641) (meaning t m 3834) (meaning t m 3847) (meaning t m 4149) (meaning t m 5119) (meaning t m 5284) source

theorem rule40641 (p2027 p2528 p2598 p2952 p3641 p3690 p4320 p4669 p4789 : Prop) (h : (¬ p4320) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4789)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29897 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40641 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2952) (meaning t m 3641) (meaning t m 3690) (meaning t m 4320) (meaning t m 4669) (meaning t m 4789) source

theorem rule40642 (p2027 p2598 p2761 p3292 p3422 p3564 p4621 p4789 p5284 : Prop) (h : (¬ p3292) ∨ (¬ p5284) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4621) ∨ (¬ p4789) ∨ (¬ p3564) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2761) ∨ (¬ p3292) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4621) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29898 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40642 (meaning t m 2027) (meaning t m 2598) (meaning t m 2761) (meaning t m 3292) (meaning t m 3422) (meaning t m 3564) (meaning t m 4621) (meaning t m 4789) (meaning t m 5284) source

theorem rule40643 (p1982 p2027 p2528 p2573 p2611 p3362 p3584 p3641 : Prop) (h : (¬ p3362) ∨ (¬ p1982) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p2573) ∨ p2611 ∨ (¬ p3641) ∨ (¬ p3584)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (p2611) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial40643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory29899 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule40643 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2573) (meaning t m 2611) (meaning t m 3362) (meaning t m 3584) (meaning t m 3641) source

theorem rule40644 (p2027 p2598 p3414 p3641 p3947 p4149 p4381 p4789 p5119 : Prop) (h : (¬ p3414) ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p4789) ∨ (¬ p3641) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3414) ∨ (¬ p3641) ∨ (¬ p3947) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29900 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40644 (meaning t m 2027) (meaning t m 2598) (meaning t m 3414) (meaning t m 3641) (meaning t m 3947) (meaning t m 4149) (meaning t m 4381) (meaning t m 4789) (meaning t m 5119) source

theorem rule40646 (p2027 p2132 p2241 p2619 p2750 p2753 p3146 p3193 p3452 p4697 : Prop) (h : (¬ p2750) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3452) ∨ (¬ p2241) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial40646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory29902 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule40646 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3193) (meaning t m 3452) (meaning t m 4697) source

theorem rule40647 (p2027 p2252 p2750 p2950 p3449 p3609 p3646 p3954 p3989 p5118 p5315 p5580 : Prop) (h : (¬ p5315) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p5118) ∨ (¬ p2750) ∨ (¬ p2950) ∨ (¬ p2252) ∨ (¬ p5580) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2950) ∨ (¬ p3449) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p5118) ∨ (¬ p5315) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5315)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29903 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40647 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2950) (meaning t m 3449) (meaning t m 3609) (meaning t m 3646) (meaning t m 3954) (meaning t m 3989) (meaning t m 5118) (meaning t m 5315) (meaning t m 5580) source

theorem rule40648 (p2027 p2295 p2313 p2528 p2598 p2787 p3641 p4037 p4396 p4669 : Prop) (h : (¬ p4669) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4396) ∨ (¬ p2787) ∨ (¬ p4037) ∨ (¬ p3641) ∨ (¬ p2528) ∨ (¬ p2313) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2787) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4396) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory29904 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule40648 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2528) (meaning t m 2598) (meaning t m 2787) (meaning t m 3641) (meaning t m 4037) (meaning t m 4396) (meaning t m 4669) source

theorem rule40649 (p2027 p2528 p2761 p4286 p4669 p5117 : Prop) (h : p2027 ∨ (¬ p2528) ∨ (¬ p4286) ∨ (¬ p5117) ∨ (¬ p4669) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p4286) ∨ (¬ p4669) ∨ (¬ p5117) := by
  classical
  tauto

theorem initial40649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5117)) := by
  have source := ElevenTheory.theory29905 t (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule40649 (meaning t m 2027) (meaning t m 2528) (meaning t m 2761) (meaning t m 4286) (meaning t m 4669) (meaning t m 5117) source

theorem rule40650 (p2027 p2132 p2187 p2449 p2860 p3553 p3821 p4133 p5260 : Prop) (h : p2027 ∨ (¬ p3553) ∨ (¬ p2187) ∨ (¬ p2449) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4133) ∨ (¬ p5260) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2449) ∨ (¬ p2860) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4133) ∨ (¬ p5260) := by
  classical
  tauto

theorem initial40650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5260)) := by
  have source := ElevenTheory.theory29906 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule40650 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2449) (meaning t m 2860) (meaning t m 3553) (meaning t m 3821) (meaning t m 4133) (meaning t m 5260) source

theorem rule40652 (p1983 p2027 p2997 p3097 p3125 p3461 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p1983) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3125)) : (¬ p1983) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial40652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory29908 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40652 (meaning t m 1983) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3461) (meaning t m 4381) source

theorem rule40653 (p2027 p2761 p2952 p3516 p3744 p3819 p3952 p4444 p4604 p4789 : Prop) (h : (¬ p2761) ∨ (¬ p3819) ∨ (¬ p3516) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3516) ∨ (¬ p3744) ∨ (¬ p3819) ∨ (¬ p3952) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29909 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40653 (meaning t m 2027) (meaning t m 2761) (meaning t m 2952) (meaning t m 3516) (meaning t m 3744) (meaning t m 3819) (meaning t m 3952) (meaning t m 4444) (meaning t m 4604) (meaning t m 4789) source

theorem rule40657 (p2027 p2573 p2753 p2901 p3362 p3497 p3556 p3584 p3641 p3645 p4158 p4877 : Prop) (h : (¬ p3362) ∨ (¬ p3645) ∨ (¬ p2573) ∨ (¬ p2901) ∨ (¬ p2753) ∨ (¬ p4158) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p3497) ∨ (¬ p3584) ∨ (¬ p4877)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2753) ∨ (¬ p2901) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p4158) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial40657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory29913 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule40657 (meaning t m 2027) (meaning t m 2573) (meaning t m 2753) (meaning t m 2901) (meaning t m 3362) (meaning t m 3497) (meaning t m 3556) (meaning t m 3584) (meaning t m 3641) (meaning t m 3645) (meaning t m 4158) (meaning t m 4877) source

theorem rule40658 (p2027 p2598 p2901 p2950 p3422 p3556 p3564 p4208 p4368 p4789 : Prop) (h : (¬ p2950) ∨ (¬ p4208) ∨ (¬ p2598) ∨ (¬ p3556) ∨ (¬ p4368) ∨ (¬ p4789) ∨ (¬ p2901) ∨ (¬ p3564) ∨ (¬ p3422) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3422) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p4208) ∨ (¬ p4368) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29914 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9)
  exact rule40658 (meaning t m 2027) (meaning t m 2598) (meaning t m 2901) (meaning t m 2950) (meaning t m 3422) (meaning t m 3556) (meaning t m 3564) (meaning t m 4208) (meaning t m 4368) (meaning t m 4789) source

theorem rule40659 (p2027 p2145 p2528 p2598 p2901 p3556 p3641 p4208 p5059 : Prop) (h : (¬ p2901) ∨ (¬ p3556) ∨ (¬ p2145) ∨ (¬ p2598) ∨ (¬ p2528) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3641) ∨ (¬ p4208) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory29915 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule40659 (meaning t m 2027) (meaning t m 2145) (meaning t m 2528) (meaning t m 2598) (meaning t m 2901) (meaning t m 3556) (meaning t m 3641) (meaning t m 4208) (meaning t m 5059) source

theorem rule40660 (p2027 p2098 p2241 p2750 p2753 p3548 p3609 p4133 p4347 p4366 : Prop) (h : (¬ p4366) ∨ (¬ p3548) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2098) ∨ (¬ p3609) ∨ (¬ p4133) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3548) ∨ (¬ p3609) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial40660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory29916 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40660 (meaning t m 2027) (meaning t m 2098) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3548) (meaning t m 3609) (meaning t m 4133) (meaning t m 4347) (meaning t m 4366) source

theorem rule40662 (p2441 p4186 p4607 : Prop) (h : (¬ p2441) ∨ (¬ p4186) ∨ p4607) : (¬ p2441) ∨ (¬ p4186) ∨ (p4607) := by
  classical
  tauto

theorem initial40662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 4186)) ∨ (meaning t m 4607) := by
  have source := ElevenTheory.theory29918 (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule40662 (meaning t m 2441) (meaning t m 4186) (meaning t m 4607) source

theorem rule40663 (p2027 p2307 p3549 p3954 p4870 p5020 : Prop) (h : (¬ p2307) ∨ (¬ p3954) ∨ (¬ p4870) ∨ (¬ p5020) ∨ (¬ p3549) ∨ p2027) : (p2027) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4870) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial40663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory29919 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7)
  exact rule40663 (meaning t m 2027) (meaning t m 2307) (meaning t m 3549) (meaning t m 3954) (meaning t m 4870) (meaning t m 5020) source

theorem rule40664 (p2027 p2230 p2299 p2963 p3362 p3568 p3641 p3684 p4420 p4789 : Prop) (h : (¬ p3362) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4420) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2230) ∨ (¬ p4789)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4420) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29920 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule40664 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2963) (meaning t m 3362) (meaning t m 3568) (meaning t m 3641) (meaning t m 3684) (meaning t m 4420) (meaning t m 4789) source

theorem rule40665 (p2027 p2295 p2313 p2470 p2528 p2753 p3204 p3324 p3362 p3692 p4433 p4870 : Prop) (h : (¬ p3204) ∨ (¬ p2753) ∨ (¬ p4870) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p3362) ∨ (¬ p4433) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3692) ∨ (¬ p4433) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial40665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory29921 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule40665 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2470) (meaning t m 2528) (meaning t m 2753) (meaning t m 3204) (meaning t m 3324) (meaning t m 3362) (meaning t m 3692) (meaning t m 4433) (meaning t m 4870) source

theorem rule40667 (p2027 p2459 p2717 p2952 p3471 p3744 p3952 p4604 p4789 : Prop) (h : (¬ p4604) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p4789) ∨ (¬ p2952) ∨ (¬ p2717) ∨ (¬ p2459) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3471) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29923 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40667 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 2952) (meaning t m 3471) (meaning t m 3744) (meaning t m 3952) (meaning t m 4604) (meaning t m 4789) source

theorem rule40670 (p2027 p3449 p3556 p3645 p3690 p3954 p4181 p4381 p4877 p5119 : Prop) (h : (¬ p3556) ∨ (¬ p3449) ∨ (¬ p4181) ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p3645) ∨ (¬ p4877) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29926 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40670 (meaning t m 2027) (meaning t m 3449) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 3954) (meaning t m 4181) (meaning t m 4381) (meaning t m 4877) (meaning t m 5119) source

theorem rule40671 (p2027 p3333 p3874 p4286 p4695 p5118 : Prop) (h : (¬ p4695) ∨ (¬ p3333) ∨ (¬ p3874) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p4286)) : (p2027) ∨ (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4695) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial40671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4695)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory29927 t (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 10) (m.theta 8 9)
  exact rule40671 (meaning t m 2027) (meaning t m 3333) (meaning t m 3874) (meaning t m 4286) (meaning t m 4695) (meaning t m 5118) source

theorem rule40672 (p2027 p2230 p2295 p2313 p2787 p3324 p3362 p3641 p3684 p4596 : Prop) (h : (¬ p2787) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4596) ∨ (¬ p3362) ∨ (¬ p2313) ∨ (¬ p2295) ∨ (¬ p3641) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial40672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory29928 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule40672 (meaning t m 2027) (meaning t m 2230) (meaning t m 2295) (meaning t m 2313) (meaning t m 2787) (meaning t m 3324) (meaning t m 3362) (meaning t m 3641) (meaning t m 3684) (meaning t m 4596) source

end SunPrize.SMT
