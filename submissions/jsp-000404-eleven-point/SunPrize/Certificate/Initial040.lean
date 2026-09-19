import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory024
import SunPrize.Certificate.Theory025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule18316 (p1982 p2027 p2177 p2287 p2459 p2685 p3552 p4195 : Prop) (h : p2027 ∨ (¬ p1982) ∨ p2287 ∨ (¬ p2177) ∨ (¬ p4195) ∨ (¬ p2459) ∨ (¬ p2685) ∨ (¬ p3552)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2287) ∨ (¬ p2459) ∨ (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial18316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory7588 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18316 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2287) (meaning t m 2459) (meaning t m 2685) (meaning t m 3552) (meaning t m 4195) source

theorem rule18318 (p1990 p2027 p2563 p2997 p3325 p3880 p3979 p4115 p5590 : Prop) (h : (¬ p5590) ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p4115) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3325) ∨ p2997 ∨ (¬ p3979)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2997) ∨ (¬ p3325) ∨ (¬ p3880) ∨ (¬ p3979) ∨ (¬ p4115) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial18318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory7590 t (m.theta 0 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule18318 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2997) (meaning t m 3325) (meaning t m 3880) (meaning t m 3979) (meaning t m 4115) (meaning t m 5590) source

theorem rule18320 (p1988 p2027 p2148 p2459 p2911 p3051 p3266 p4001 : Prop) (h : p2148 ∨ (¬ p4001) ∨ (¬ p3051) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2911) ∨ (¬ p2459)) : (¬ p1988) ∨ (p2027) ∨ (p2148) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p3266) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial18320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory7592 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18320 (meaning t m 1988) (meaning t m 2027) (meaning t m 2148) (meaning t m 2459) (meaning t m 2911) (meaning t m 3051) (meaning t m 3266) (meaning t m 4001) source

theorem rule18321 (p1982 p2027 p2287 p2295 p2352 p2363 p2588 : Prop) (h : (¬ p2295) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2588) ∨ p2027 ∨ p2287 ∨ (¬ p2352)) : (¬ p1982) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial18321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory7593 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule18321 (meaning t m 1982) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2352) (meaning t m 2363) (meaning t m 2588) source

theorem rule18327 (p1982 p2027 p2352 p2363 p2386 p2545 p2641 p3567 p4111 : Prop) (h : (¬ p3567) ∨ (¬ p2386) ∨ (¬ p2352) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2641) ∨ (¬ p4111) ∨ p2545) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2386) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial18327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2386)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7599 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18327 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2386) (meaning t m 2545) (meaning t m 2641) (meaning t m 3567) (meaning t m 4111) source

theorem rule18338 (p1992 p2027 p2169 p2313 p2608 p3309 p3923 p5015 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p1992) ∨ (¬ p3923) ∨ (¬ p3309) ∨ (¬ p5015) ∨ (¬ p2313)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial18338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory7610 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18338 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2608) (meaning t m 3309) (meaning t m 3923) (meaning t m 5015) source

theorem rule18339 (p1982 p2027 p2233 p2363 p2470 p4149 p5580 : Prop) (h : p2233 ∨ (¬ p2363) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p5580) ∨ (¬ p4149)) : (¬ p1982) ∨ (p2027) ∨ (p2233) ∨ (¬ p2363) ∨ (¬ p2470) ∨ (¬ p4149) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7611 t (m.theta 0 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18339 (meaning t m 1982) (meaning t m 2027) (meaning t m 2233) (meaning t m 2363) (meaning t m 2470) (meaning t m 4149) (meaning t m 5580) source

theorem rule18340 (p1976 p2027 p2104 p2766 p4009 p4118 p5612 : Prop) (h : (¬ p4118) ∨ (¬ p1976) ∨ p2766 ∨ p2027 ∨ (¬ p4009) ∨ (¬ p2104) ∨ (¬ p5612)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2104) ∨ (p2766) ∨ (¬ p4009) ∨ (¬ p4118) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial18340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory7612 t (m.theta 0 2) (m.theta 2 8) (m.theta 3 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18340 (meaning t m 1976) (meaning t m 2027) (meaning t m 2104) (meaning t m 2766) (meaning t m 4009) (meaning t m 4118) (meaning t m 5612) source

theorem rule18342 (p2023 p2027 p3128 p3449 p3461 p3834 p3847 p5284 : Prop) (h : (¬ p2023) ∨ (¬ p3847) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p5284) ∨ (¬ p3834) ∨ (¬ p3461) ∨ p3128) : (¬ p2023) ∨ (p2027) ∨ (p3128) ∨ (¬ p3449) ∨ (¬ p3461) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7614 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule18342 (meaning t m 2023) (meaning t m 2027) (meaning t m 3128) (meaning t m 3449) (meaning t m 3461) (meaning t m 3834) (meaning t m 3847) (meaning t m 5284) source

theorem rule18344 (p1975 p2027 p2148 p2299 p2911 p2962 p3654 p3920 p4137 : Prop) (h : (¬ p1975) ∨ p2148 ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2299) ∨ (¬ p3654) ∨ (¬ p2962) ∨ (¬ p3920)) : (¬ p1975) ∨ (p2027) ∨ (p2148) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3920) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial18344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7616 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule18344 (meaning t m 1975) (meaning t m 2027) (meaning t m 2148) (meaning t m 2299) (meaning t m 2911) (meaning t m 2962) (meaning t m 3654) (meaning t m 3920) (meaning t m 4137) source

theorem rule18345 (p1988 p2027 p2156 p2233 p2982 p3680 p4110 p4399 : Prop) (h : (¬ p3680) ∨ p2233 ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p2982) ∨ (¬ p4399) ∨ (¬ p1988) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2156) ∨ (p2233) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial18345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory7617 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule18345 (meaning t m 1988) (meaning t m 2027) (meaning t m 2156) (meaning t m 2233) (meaning t m 2982) (meaning t m 3680) (meaning t m 4110) (meaning t m 4399) source

theorem rule18346 (p2001 p2027 p2765 p3051 p3156 p3646 p4320 : Prop) (h : (¬ p3646) ∨ (¬ p3051) ∨ (¬ p4320) ∨ p2765 ∨ p2027 ∨ (¬ p2001) ∨ (¬ p3156)) : (¬ p2001) ∨ (p2027) ∨ (p2765) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3646) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial18346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory7618 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule18346 (meaning t m 2001) (meaning t m 2027) (meaning t m 2765) (meaning t m 3051) (meaning t m 3156) (meaning t m 3646) (meaning t m 4320) source

theorem rule18350 (p1984 p2027 p2169 p3591 p3914 p4358 p4435 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3591) ∨ p2169 ∨ (¬ p4358) ∨ (¬ p3914) ∨ (¬ p4435)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3591) ∨ (¬ p3914) ∨ (¬ p4358) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial18350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory7622 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 10) (m.theta 6 8)
  exact rule18350 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3591) (meaning t m 3914) (meaning t m 4358) (meaning t m 4435) source

theorem rule18351 (p1997 p2027 p2132 p2753 p2842 p2870 p3585 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2753) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p1997) ∨ (¬ p2132) ∨ p2842) : (¬ p1997) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (p2842) ∨ (¬ p2870) ∨ (¬ p3585) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7623 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule18351 (meaning t m 1997) (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2842) (meaning t m 2870) (meaning t m 3585) (meaning t m 4235) source

theorem rule18352 (p1982 p2027 p2148 p2761 p3051 p3246 p4444 : Prop) (h : p2148 ∨ (¬ p3051) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p1982) ∨ (¬ p3246)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7624 t (m.theta 0 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18352 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 4444) source

theorem rule18353 (p1998 p2027 p2230 p2233 p2427 p3146 p3747 p4348 : Prop) (h : p2233 ∨ (¬ p3747) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3146)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7625 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18353 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2427) (meaning t m 3146) (meaning t m 3747) (meaning t m 4348) source

theorem rule18357 (p1988 p2027 p2230 p2233 p2427 p2761 p3246 : Prop) (h : p2233 ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p2230) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2427)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2427) ∨ (¬ p2761) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial18357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory7629 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18357 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2427) (meaning t m 2761) (meaning t m 3246) source

theorem rule18358 (p2027 p3688 p3954 p4113 p4114 p4358 p5017 : Prop) (h : (¬ p4114) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p5017) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p4113)) : (p2027) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4113) ∨ (¬ p4114) ∨ (¬ p4358) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial18358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory7630 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 8) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8)
  exact rule18358 (meaning t m 2027) (meaning t m 3688) (meaning t m 3954) (meaning t m 4113) (meaning t m 4114) (meaning t m 4358) (meaning t m 5017) source

theorem rule18359 (p1997 p2027 p3128 p3914 p4037 p4110 p4337 p4393 : Prop) (h : (¬ p4337) ∨ (¬ p4110) ∨ (¬ p1997) ∨ p3128 ∨ (¬ p4037) ∨ (¬ p3914) ∨ p2027 ∨ (¬ p4393)) : (¬ p1997) ∨ (p2027) ∨ (p3128) ∨ (¬ p3914) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4337) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial18359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory7631 t (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 10) (m.theta 6 9)
  exact rule18359 (meaning t m 1997) (meaning t m 2027) (meaning t m 3128) (meaning t m 3914) (meaning t m 4037) (meaning t m 4110) (meaning t m 4337) (meaning t m 4393) source

theorem rule18363 (p2005 p2997 p3568 p4976 : Prop) (h : p2997 ∨ (¬ p2005) ∨ (¬ p3568) ∨ p4976) : (¬ p2005) ∨ (p2997) ∨ (¬ p3568) ∨ (p4976) := by
  classical
  tauto

theorem initial18363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory7635 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule18363 (meaning t m 2005) (meaning t m 2997) (meaning t m 3568) (meaning t m 4976) source

theorem rule18364 (p1998 p2148 p2220 p4905 : Prop) (h : p4905 ∨ (¬ p1998) ∨ p2148 ∨ (¬ p2220)) : (¬ p1998) ∨ (p2148) ∨ (¬ p2220) ∨ (p4905) := by
  classical
  tauto

theorem initial18364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 4905) := by
  have source := ElevenTheory.theory7636 t (m.theta 0 5) (m.theta 5 8) (m.theta 7 8)
  exact rule18364 (meaning t m 1998) (meaning t m 2148) (meaning t m 2220) (meaning t m 4905) source

theorem rule18365 (p1991 p2873 p2952 p4960 : Prop) (h : (¬ p1991) ∨ (¬ p2952) ∨ p2873 ∨ p4960) : (¬ p1991) ∨ (p2873) ∨ (¬ p2952) ∨ (p4960) := by
  classical
  tauto

theorem initial18365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 4960) := by
  have source := ElevenTheory.theory7637 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5)
  exact rule18365 (meaning t m 1991) (meaning t m 2873) (meaning t m 2952) (meaning t m 4960) source

theorem rule18370 (p2001 p2027 p2388 p3005 p3256 p3692 p4315 : Prop) (h : p2027 ∨ (¬ p2001) ∨ p2388 ∨ (¬ p4315) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p3256)) : (¬ p2001) ∨ (p2027) ∨ (p2388) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7642 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18370 (meaning t m 2001) (meaning t m 2027) (meaning t m 2388) (meaning t m 3005) (meaning t m 3256) (meaning t m 3692) (meaning t m 4315) source

theorem rule18371 (p1991 p2027 p2545 p2810 p3005 p3170 p4009 p5590 : Prop) (h : (¬ p1991) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p5590) ∨ p2545 ∨ (¬ p4009) ∨ (¬ p3005) ∨ (¬ p3170)) : (¬ p1991) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3170) ∨ (¬ p4009) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial18371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory7643 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 10)
  exact rule18371 (meaning t m 1991) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 3170) (meaning t m 4009) (meaning t m 5590) source

theorem rule18374 (p1977 p2545 p2745 p2810 : Prop) (h : (¬ p1977) ∨ p2545 ∨ (¬ p2810) ∨ p2745) : (¬ p1977) ∨ (p2545) ∨ (p2745) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial18374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2545) ∨ (meaning t m 2745) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory7646 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule18374 (meaning t m 1977) (meaning t m 2545) (meaning t m 2745) (meaning t m 2810) source

theorem rule18379 (p1990 p2027 p2470 p2563 p2611 p2850 p3362 p3874 : Prop) (h : (¬ p3362) ∨ (¬ p3874) ∨ (¬ p2563) ∨ p2611 ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2470)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2563) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p3362) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial18379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory7651 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule18379 (meaning t m 1990) (meaning t m 2027) (meaning t m 2470) (meaning t m 2563) (meaning t m 2611) (meaning t m 2850) (meaning t m 3362) (meaning t m 3874) source

theorem rule18384 (p1981 p2027 p2148 p2187 p2563 p3051 p4235 : Prop) (h : p2148 ∨ (¬ p3051) ∨ (¬ p1981) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (p2148) ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7656 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule18384 (meaning t m 1981) (meaning t m 2027) (meaning t m 2148) (meaning t m 2187) (meaning t m 2563) (meaning t m 3051) (meaning t m 4235) source

theorem rule18385 (p1990 p2027 p2144 p2563 p2842 p3051 p3055 p4235 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3051) ∨ p2842 ∨ (¬ p3055) ∨ (¬ p4235) ∨ (¬ p2144)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2563) ∨ (p2842) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7657 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18385 (meaning t m 1990) (meaning t m 2027) (meaning t m 2144) (meaning t m 2563) (meaning t m 2842) (meaning t m 3051) (meaning t m 3055) (meaning t m 4235) source

theorem rule18389 (p1983 p2027 p2622 p2630 p2656 p3276 p3355 p4381 : Prop) (h : (¬ p3355) ∨ p2622 ∨ (¬ p4381) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2656) ∨ (¬ p2630)) : (¬ p1983) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7661 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule18389 (meaning t m 1983) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3276) (meaning t m 3355) (meaning t m 4381) source

theorem rule18393 (p1983 p2027 p2156 p2233 p2299 p2396 p2881 p3872 p4399 : Prop) (h : (¬ p2396) ∨ p2233 ∨ (¬ p1983) ∨ (¬ p2156) ∨ (¬ p4399) ∨ p2027 ∨ (¬ p3872) ∨ (¬ p2299) ∨ (¬ p2881)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2156) ∨ (p2233) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial18393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory7665 t (m.theta 0 4) (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18393 (meaning t m 1983) (meaning t m 2027) (meaning t m 2156) (meaning t m 2233) (meaning t m 2299) (meaning t m 2396) (meaning t m 2881) (meaning t m 3872) (meaning t m 4399) source

theorem rule18395 (p2003 p2148 p2156 p4486 : Prop) (h : (¬ p2003) ∨ p2148 ∨ (¬ p2156) ∨ p4486) : (¬ p2003) ∨ (p2148) ∨ (¬ p2156) ∨ (p4486) := by
  classical
  tauto

theorem initial18395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 4486) := by
  have source := ElevenTheory.theory7667 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6)
  exact rule18395 (meaning t m 2003) (meaning t m 2148) (meaning t m 2156) (meaning t m 4486) source

theorem rule18396 (p1983 p2027 p2997 p3319 p3461 p3549 p4381 : Prop) (h : (¬ p3549) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p4381) ∨ p2997 ∨ (¬ p3319) ∨ (¬ p3461)) : (¬ p1983) ∨ (p2027) ∨ (p2997) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3549) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7668 t (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule18396 (meaning t m 1983) (meaning t m 2027) (meaning t m 2997) (meaning t m 3319) (meaning t m 3461) (meaning t m 3549) (meaning t m 4381) source

theorem rule18405 (p1997 p2027 p2169 p2192 p2363 p3949 p4110 p4363 : Prop) (h : (¬ p2192) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4110) ∨ p2169 ∨ (¬ p1997) ∨ (¬ p3949) ∨ (¬ p4363)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3949) ∨ (¬ p4110) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial18405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory7677 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule18405 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2192) (meaning t m 2363) (meaning t m 3949) (meaning t m 4110) (meaning t m 4363) source

theorem rule18407 (p1985 p2027 p2192 p2210 p2427 p2699 p4110 : Prop) (h : p2027 ∨ (¬ p1985) ∨ p2699 ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p2210) ∨ (¬ p2192)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2427) ∨ (p2699) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7679 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18407 (meaning t m 1985) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2427) (meaning t m 2699) (meaning t m 4110) source

theorem rule18412 (p2005 p2027 p2470 p2656 p2688 p2727 p3422 p3874 : Prop) (h : (¬ p2656) ∨ p2688 ∨ p2027 ∨ (¬ p2727) ∨ (¬ p3422) ∨ (¬ p2005) ∨ (¬ p2470) ∨ (¬ p3874)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial18412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory7684 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule18412 (meaning t m 2005) (meaning t m 2027) (meaning t m 2470) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3422) (meaning t m 3874) source

theorem rule18414 (p2022 p2027 p2169 p2363 p3544 p4075 p4261 p4372 : Prop) (h : p2169 ∨ (¬ p2022) ∨ (¬ p2363) ∨ (¬ p3544) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p4075) ∨ (¬ p4372)) : (¬ p2022) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3544) ∨ (¬ p4075) ∨ (¬ p4261) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial18414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory7686 t (m.theta 0 7) (m.theta 1 7) (m.theta 1 8) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9)
  exact rule18414 (meaning t m 2022) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 3544) (meaning t m 4075) (meaning t m 4261) (meaning t m 4372) source

theorem rule18417 (p1999 p2027 p2765 p3115 p3680 p3952 p4191 : Prop) (h : (¬ p3952) ∨ (¬ p1999) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p4191) ∨ p2765 ∨ (¬ p3115)) : (¬ p1999) ∨ (p2027) ∨ (p2765) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3952) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial18417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory7689 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule18417 (meaning t m 1999) (meaning t m 2027) (meaning t m 2765) (meaning t m 3115) (meaning t m 3680) (meaning t m 3952) (meaning t m 4191) source

theorem rule18419 (p1983 p2027 p2233 p2396 p2573 p3201 p3584 p4710 : Prop) (h : p2233 ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2396) ∨ (¬ p1983) ∨ (¬ p4710) ∨ (¬ p3584) ∨ (¬ p3201)) : (¬ p1983) ∨ (p2027) ∨ (p2233) ∨ (¬ p2396) ∨ (¬ p2573) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial18419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory7691 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18419 (meaning t m 1983) (meaning t m 2027) (meaning t m 2233) (meaning t m 2396) (meaning t m 2573) (meaning t m 3201) (meaning t m 3584) (meaning t m 4710) source

theorem rule18422 (p1988 p2027 p2470 p2528 p2622 p2630 p2656 p3266 : Prop) (h : (¬ p1988) ∨ (¬ p2656) ∨ (¬ p2528) ∨ p2622 ∨ p2027 ∨ (¬ p3266) ∨ (¬ p2630) ∨ (¬ p2470)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial18422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory7694 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18422 (meaning t m 1988) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3266) source

theorem rule18424 (p1977 p2027 p2241 p2766 p3032 p3553 p4348 p4366 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ p2766 ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p3032) ∨ (¬ p4366)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2766) ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7696 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18424 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2766) (meaning t m 3032) (meaning t m 3553) (meaning t m 4348) (meaning t m 4366) source

theorem rule18425 (p1984 p2027 p2449 p2633 p3553 p3817 p4366 : Prop) (h : (¬ p3553) ∨ (¬ p1984) ∨ p2633 ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2449) ∨ (¬ p3817)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2449) ∨ (p2633) ∨ (¬ p3553) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7697 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18425 (meaning t m 1984) (meaning t m 2027) (meaning t m 2449) (meaning t m 2633) (meaning t m 3553) (meaning t m 3817) (meaning t m 4366) source

theorem rule18426 (p1975 p2027 p2132 p2611 p2870 p3246 p4107 : Prop) (h : (¬ p3246) ∨ p2027 ∨ (¬ p2132) ∨ p2611 ∨ (¬ p4107) ∨ (¬ p1975) ∨ (¬ p2870)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7698 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18426 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2870) (meaning t m 3246) (meaning t m 4107) source

theorem rule18428 (p1975 p2027 p2417 p2598 p2611 p3201 p4107 : Prop) (h : p2611 ∨ (¬ p4107) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2598) ∨ (¬ p2417)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7700 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18428 (meaning t m 1975) (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2611) (meaning t m 3201) (meaning t m 4107) source

theorem rule18429 (p1990 p2027 p2493 p2553 p2699 p3097 p3379 : Prop) (h : (¬ p1990) ∨ (¬ p2553) ∨ p2699 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p2493)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3097) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial18429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory7701 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule18429 (meaning t m 1990) (meaning t m 2027) (meaning t m 2493) (meaning t m 2553) (meaning t m 2699) (meaning t m 3097) (meaning t m 3379) source

theorem rule18430 (p1987 p2027 p2187 p2737 p2765 p3688 p4358 : Prop) (h : (¬ p2737) ∨ p2765 ∨ (¬ p1987) ∨ (¬ p2187) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3688)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2737) ∨ (p2765) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7702 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule18430 (meaning t m 1987) (meaning t m 2027) (meaning t m 2187) (meaning t m 2737) (meaning t m 2765) (meaning t m 3688) (meaning t m 4358) source

theorem rule18431 (p1975 p2027 p2553 p2699 p3063 p3093 p3956 : Prop) (h : p2027 ∨ (¬ p3956) ∨ (¬ p2553) ∨ (¬ p1975) ∨ (¬ p3093) ∨ p2699 ∨ (¬ p3063)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7703 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18431 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 3956) source

theorem rule18432 (p1987 p2027 p2737 p2766 p3583 p3692 p3694 : Prop) (h : (¬ p3694) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p1987) ∨ (¬ p3692) ∨ p2027 ∨ p2766) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial18432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory7704 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18432 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2766) (meaning t m 3583) (meaning t m 3692) (meaning t m 3694) source

theorem rule18434 (p1992 p2027 p2743 p2766 p3266 p3292 p3361 p5284 : Prop) (h : (¬ p3361) ∨ (¬ p2743) ∨ (¬ p1992) ∨ (¬ p5284) ∨ (¬ p3266) ∨ p2766 ∨ (¬ p3292) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3361) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7706 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18434 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 3266) (meaning t m 3292) (meaning t m 3361) (meaning t m 5284) source

theorem rule18437 (p1992 p2027 p2169 p2295 p2313 p2743 p3324 p3361 p3983 : Prop) (h : p2169 ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p1992) ∨ (¬ p3983) ∨ (¬ p2295)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial18437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory7709 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18437 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 2313) (meaning t m 2743) (meaning t m 3324) (meaning t m 3361) (meaning t m 3983) source

theorem rule18438 (p1992 p2027 p2299 p2633 p2743 p2963 p3361 p3568 : Prop) (h : p2027 ∨ (¬ p3568) ∨ (¬ p2743) ∨ (¬ p1992) ∨ (¬ p3361) ∨ p2633 ∨ (¬ p2963) ∨ (¬ p2299)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial18438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory7710 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18438 (meaning t m 1992) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 3568) source

theorem rule18439 (p1992 p2027 p2588 p2657 p2743 p2997 p3361 p3574 : Prop) (h : p2997 ∨ (¬ p3361) ∨ (¬ p2588) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2743) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (p2997) ∨ (¬ p3361) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial18439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory7711 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule18439 (meaning t m 1992) (meaning t m 2027) (meaning t m 2588) (meaning t m 2657) (meaning t m 2743) (meaning t m 2997) (meaning t m 3361) (meaning t m 3574) source

theorem rule18442 (p1982 p2027 p2611 p2774 p2819 p3461 p3990 p4444 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2819) ∨ (¬ p2774) ∨ (¬ p3461) ∨ (¬ p4444) ∨ (¬ p3990)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7714 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18442 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2774) (meaning t m 2819) (meaning t m 3461) (meaning t m 3990) (meaning t m 4444) source

theorem rule18443 (p1992 p2027 p2437 p3008 p3363 p3540 p3574 p3585 : Prop) (h : p2027 ∨ (¬ p3363) ∨ (¬ p1992) ∨ (¬ p3585) ∨ (¬ p3540) ∨ p3008 ∨ (¬ p2437) ∨ (¬ p3574)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2437) ∨ (p3008) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial18443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7715 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule18443 (meaning t m 1992) (meaning t m 2027) (meaning t m 2437) (meaning t m 3008) (meaning t m 3363) (meaning t m 3540) (meaning t m 3574) (meaning t m 3585) source

theorem rule18444 (p1992 p2027 p2264 p2462 p2743 p3361 p3551 p3947 p4849 : Prop) (h : p2462 ∨ (¬ p3551) ∨ (¬ p3361) ∨ (¬ p4849) ∨ (¬ p2264) ∨ (¬ p2743) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3947)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2264) ∨ (p2462) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial18444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory7716 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18444 (meaning t m 1992) (meaning t m 2027) (meaning t m 2264) (meaning t m 2462) (meaning t m 2743) (meaning t m 3361) (meaning t m 3551) (meaning t m 3947) (meaning t m 4849) source

theorem rule18445 (p1992 p2027 p2743 p2766 p2952 p3361 p3497 p3692 : Prop) (h : (¬ p1992) ∨ p2766 ∨ (¬ p3497) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p3692)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial18445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7717 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18445 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 2952) (meaning t m 3361) (meaning t m 3497) (meaning t m 3692) source

theorem rule18446 (p2027 p2476 p3355 p4347 p4384 p4695 : Prop) (h : (¬ p4695) ∨ p2027 ∨ (¬ p4384) ∨ (¬ p3355) ∨ (¬ p4347) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial18446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory7718 t (m.theta 0 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule18446 (meaning t m 2027) (meaning t m 2476) (meaning t m 3355) (meaning t m 4347) (meaning t m 4384) (meaning t m 4695) source

theorem rule18447 (p1998 p2177 p2938 p4559 : Prop) (h : (¬ p1998) ∨ p2938 ∨ (¬ p2177) ∨ p4559) : (¬ p1998) ∨ (¬ p2177) ∨ (p2938) ∨ (p4559) := by
  classical
  tauto

theorem initial18447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2938) ∨ (meaning t m 4559) := by
  have source := ElevenTheory.theory7719 t (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule18447 (meaning t m 1998) (meaning t m 2177) (meaning t m 2938) (meaning t m 4559) source

theorem rule18448 (p1992 p2027 p2579 p2655 p2743 p2914 p3016 p3361 p3742 : Prop) (h : (¬ p3016) ∨ (¬ p2655) ∨ (¬ p2579) ∨ (¬ p3361) ∨ (¬ p1992) ∨ (¬ p2743) ∨ p2027 ∨ p2914 ∨ (¬ p3742)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (p2914) ∨ (¬ p3016) ∨ (¬ p3361) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial18448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory7720 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule18448 (meaning t m 1992) (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2743) (meaning t m 2914) (meaning t m 3016) (meaning t m 3361) (meaning t m 3742) source

theorem rule18452 (p1985 p2027 p2611 p2774 p2839 p2870 p3688 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p2839) ∨ (¬ p1985) ∨ (¬ p2870) ∨ (¬ p3688) ∨ (¬ p2774)) : (¬ p1985) ∨ (p2027) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial18452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory7724 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7)
  exact rule18452 (meaning t m 1985) (meaning t m 2027) (meaning t m 2611) (meaning t m 2774) (meaning t m 2839) (meaning t m 2870) (meaning t m 3688) source

theorem rule18456 (p1981 p2027 p2114 p3073 p3449 p3954 p4347 : Prop) (h : (¬ p3954) ∨ p2027 ∨ p2114 ∨ (¬ p4347) ∨ (¬ p3449) ∨ (¬ p1981) ∨ (¬ p3073)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7728 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18456 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 3073) (meaning t m 3449) (meaning t m 3954) (meaning t m 4347) source

theorem rule18457 (p2015 p2148 p2156 p4514 : Prop) (h : (¬ p2015) ∨ (¬ p2156) ∨ p4514 ∨ p2148) : (¬ p2015) ∨ (p2148) ∨ (¬ p2156) ∨ (p4514) := by
  classical
  tauto

theorem initial18457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 4514) := by
  have source := ElevenTheory.theory7729 t (m.theta 0 5) (m.theta 1 6) (m.theta 5 6)
  exact rule18457 (meaning t m 2015) (meaning t m 2148) (meaning t m 2156) (meaning t m 4514) source

theorem rule18460 (p3096 p3745 p4389 : Prop) (h : (¬ p4389) ∨ p3745 ∨ (¬ p3096)) : (¬ p3096) ∨ (p3745) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial18460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3096)) ∨ (meaning t m 3745) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory7732 (m.theta 3 6) (m.theta 4 6) (m.theta 5 6)
  exact rule18460 (meaning t m 3096) (meaning t m 3745) (meaning t m 4389) source

theorem rule18461 (p1991 p2027 p2534 p2542 p2589 p2655 p2766 p4256 : Prop) (h : (¬ p1991) ∨ p2766 ∨ (¬ p2534) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p2655)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (p2766) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7733 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule18461 (meaning t m 1991) (meaning t m 2027) (meaning t m 2534) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2766) (meaning t m 4256) source

theorem rule18462 (p1991 p2027 p2952 p2982 p3578 p3880 p4208 : Prop) (h : (¬ p3880) ∨ p2027 ∨ p3578 ∨ (¬ p1991) ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p2952)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2952) ∨ (¬ p2982) ∨ (p3578) ∨ (¬ p3880) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial18462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2982)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory7734 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule18462 (meaning t m 1991) (meaning t m 2027) (meaning t m 2952) (meaning t m 2982) (meaning t m 3578) (meaning t m 3880) (meaning t m 4208) source

theorem rule18463 (p1991 p2027 p2440 p2657 p2766 p3692 p3880 : Prop) (h : (¬ p1991) ∨ p2766 ∨ (¬ p2657) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3692)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial18463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory7735 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18463 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2766) (meaning t m 3692) (meaning t m 3880) source

theorem rule18464 (p1995 p2027 p2440 p3193 p3343 p3578 p3880 : Prop) (h : p3578 ∨ (¬ p3880) ∨ (¬ p1995) ∨ (¬ p3343) ∨ (¬ p3193) ∨ p2027 ∨ (¬ p2440)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (p3578) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial18464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory7736 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 8)
  exact rule18464 (meaning t m 1995) (meaning t m 2027) (meaning t m 2440) (meaning t m 3193) (meaning t m 3343) (meaning t m 3578) (meaning t m 3880) source

theorem rule18465 (p1991 p2027 p2373 p2765 p2952 p3497 p4110 : Prop) (h : (¬ p1991) ∨ p2765 ∨ p2027 ∨ (¬ p3497) ∨ (¬ p2373) ∨ (¬ p2952) ∨ (¬ p4110)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7737 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule18465 (meaning t m 1991) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 2952) (meaning t m 3497) (meaning t m 4110) source

theorem rule18466 (p2020 p2027 p2252 p2307 p2534 p2657 p2750 p2753 p2766 p2786 p2819 p3550 p3822 p3941 p4256 : Prop) (h : (¬ p2307) ∨ (¬ p3941) ∨ (¬ p2786) ∨ (¬ p2819) ∨ p2766 ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2657) ∨ (¬ p4256) ∨ (¬ p2534) ∨ (¬ p3550) ∨ (¬ p2020)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (p2766) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3822) ∨ (¬ p3941) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7738 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18466 (meaning t m 2020) (meaning t m 2027) (meaning t m 2252) (meaning t m 2307) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2766) (meaning t m 2786) (meaning t m 2819) (meaning t m 3550) (meaning t m 3822) (meaning t m 3941) (meaning t m 4256) source

theorem rule18469 (p2009 p2027 p3008 p3083 p3574 p4149 p5590 : Prop) (h : p3008 ∨ (¬ p2009) ∨ (¬ p3574) ∨ (¬ p5590) ∨ (¬ p4149) ∨ p2027 ∨ (¬ p3083)) : (¬ p2009) ∨ (p2027) ∨ (p3008) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4149) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial18469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory7741 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 10)
  exact rule18469 (meaning t m 2009) (meaning t m 2027) (meaning t m 3008) (meaning t m 3083) (meaning t m 3574) (meaning t m 4149) (meaning t m 5590) source

theorem rule18470 (p2006 p2027 p2114 p2210 p2972 p3954 p4385 : Prop) (h : (¬ p2210) ∨ p2114 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p2006) ∨ (¬ p4385)) : (¬ p2006) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial18470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory7742 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 9)
  exact rule18470 (meaning t m 2006) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2972) (meaning t m 3954) (meaning t m 4385) source

theorem rule18473 (p2020 p2027 p2114 p2122 p2177 p2829 p3941 : Prop) (h : p2114 ∨ (¬ p2177) ∨ (¬ p2829) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p2020) ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2829) ∨ (¬ p3941) := by
  classical
  tauto

theorem initial18473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3941)) := by
  have source := ElevenTheory.theory7745 t (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule18473 (meaning t m 2020) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2177) (meaning t m 2829) (meaning t m 3941) source

theorem rule18475 (p1982 p2027 p2114 p2122 p2177 p2459 p2829 : Prop) (h : p2114 ∨ (¬ p2459) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial18475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory7747 t (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18475 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2177) (meaning t m 2459) (meaning t m 2829) source

theorem rule18477 (p2252 p3292 p3842 : Prop) (h : (¬ p2252) ∨ (¬ p3292) ∨ (¬ p3842)) : (¬ p2252) ∨ (¬ p3292) ∨ (¬ p3842) := by
  classical
  tauto

theorem initial18477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3842)) := by
  have source := ElevenTheory.theory7749 (m.theta 0 3) (m.theta 1 3) (m.theta 3 9)
  exact rule18477 (meaning t m 2252) (meaning t m 3292) (meaning t m 3842) source

theorem rule18478 (p2025 p2027 p3008 p3276 p3343 p3574 p4321 : Prop) (h : p3008 ∨ (¬ p4321) ∨ (¬ p3276) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2025) ∨ (¬ p3343)) : (¬ p2025) ∨ (p2027) ∨ (p3008) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial18478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2025)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory7750 t (m.theta 1 9) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule18478 (meaning t m 2025) (meaning t m 2027) (meaning t m 3008) (meaning t m 3276) (meaning t m 3343) (meaning t m 3574) (meaning t m 4321) source

theorem rule18480 (p1975 p2027 p2122 p3043 p3680 p3917 p4191 : Prop) (h : (¬ p4191) ∨ p2027 ∨ (¬ p3680) ∨ p3043 ∨ (¬ p1975) ∨ (¬ p2122) ∨ (¬ p3917)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p3043) ∨ (¬ p3680) ∨ (¬ p3917) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial18480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory7752 t (m.theta 2 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule18480 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 3043) (meaning t m 3680) (meaning t m 3917) (meaning t m 4191) source

theorem rule18482 (p1981 p2027 p2220 p2765 p3146 p3646 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p3646) ∨ p2765 ∨ (¬ p3146) ∨ (¬ p2220)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3646) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7754 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18482 (meaning t m 1981) (meaning t m 2027) (meaning t m 2220) (meaning t m 2765) (meaning t m 3146) (meaning t m 3646) (meaning t m 4347) source

theorem rule18485 (p1985 p2027 p2699 p2870 p3073 p3093 p4317 p4340 p4359 : Prop) (h : (¬ p1985) ∨ p2699 ∨ (¬ p2870) ∨ (¬ p4317) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p3093)) : (¬ p1985) ∨ (p2027) ∨ (p2699) ∨ (¬ p2870) ∨ (¬ p3073) ∨ (¬ p3093) ∨ (¬ p4317) ∨ (¬ p4340) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial18485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory7757 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 2 5) (m.theta 2 8) (m.theta 5 7) (m.theta 8 9)
  exact rule18485 (meaning t m 1985) (meaning t m 2027) (meaning t m 2699) (meaning t m 2870) (meaning t m 3073) (meaning t m 3093) (meaning t m 4317) (meaning t m 4340) (meaning t m 4359) source

theorem rule18486 (p1977 p2027 p2191 p2202 p2241 p2373 p3555 : Prop) (h : p2202 ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2373) ∨ (¬ p3555) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2191) ∨ (p2202) ∨ (¬ p2241) ∨ (¬ p2373) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial18486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory7758 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule18486 (meaning t m 1977) (meaning t m 2027) (meaning t m 2191) (meaning t m 2202) (meaning t m 2241) (meaning t m 2373) (meaning t m 3555) source

theorem rule18489 (p2005 p2027 p2459 p2534 p2573 p2633 p3540 p4186 : Prop) (h : (¬ p2005) ∨ p2027 ∨ (¬ p3540) ∨ p2633 ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2573)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial18489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory7761 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18489 (meaning t m 2005) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2573) (meaning t m 2633) (meaning t m 3540) (meaning t m 4186) source

theorem rule18492 (p4109 p4207 p4209 p4948 : Prop) (h : (¬ p4109) ∨ (¬ p4948) ∨ (¬ p4209) ∨ (¬ p4207)) : (¬ p4109) ∨ (¬ p4207) ∨ (¬ p4209) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial18492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4209)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7764 (m.theta 0 5) (m.theta 0 9) (m.theta 4 5) (m.theta 5 9)
  exact rule18492 (meaning t m 4109) (meaning t m 4207) (meaning t m 4209) (meaning t m 4948) source

theorem rule18494 (p1992 p2027 p2588 p2598 p2780 p2997 p3585 p4342 : Prop) (h : (¬ p2588) ∨ p2997 ∨ p2027 ∨ (¬ p2598) ∨ (¬ p1992) ∨ (¬ p3585) ∨ (¬ p4342) ∨ (¬ p2780)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3585) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial18494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory7766 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule18494 (meaning t m 1992) (meaning t m 2027) (meaning t m 2588) (meaning t m 2598) (meaning t m 2780) (meaning t m 2997) (meaning t m 3585) (meaning t m 4342) source

theorem rule18495 (p1992 p2027 p2387 p2668 p2743 p2997 p3361 p3568 p3983 : Prop) (h : (¬ p2387) ∨ p2997 ∨ p2027 ∨ (¬ p3568) ∨ (¬ p1992) ∨ (¬ p2743) ∨ (¬ p2668) ∨ (¬ p3361) ∨ (¬ p3983)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2743) ∨ (p2997) ∨ (¬ p3361) ∨ (¬ p3568) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial18495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory7767 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18495 (meaning t m 1992) (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2743) (meaning t m 2997) (meaning t m 3361) (meaning t m 3568) (meaning t m 3983) source

theorem rule18496 (p1992 p2743 p3586 p4842 : Prop) (h : p3586 ∨ (¬ p1992) ∨ (¬ p2743) ∨ p4842) : (¬ p1992) ∨ (¬ p2743) ∨ (p3586) ∨ (p4842) := by
  classical
  tauto

theorem initial18496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 3586) ∨ (meaning t m 4842) := by
  have source := ElevenTheory.theory7768 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6)
  exact rule18496 (meaning t m 1992) (meaning t m 2743) (meaning t m 3586) (meaning t m 4842) source

theorem rule18497 (p2132 p2780 p3985 : Prop) (h : (¬ p3985) ∨ (¬ p2132) ∨ (¬ p2780)) : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial18497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory7769 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule18497 (meaning t m 2132) (meaning t m 2780) (meaning t m 3985) source

theorem rule18499 (p1987 p2027 p2143 p2737 p2766 p3583 p3692 p4120 : Prop) (h : (¬ p3583) ∨ p2766 ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p2143) ∨ (¬ p2737) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial18499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory7771 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18499 (meaning t m 1987) (meaning t m 2027) (meaning t m 2143) (meaning t m 2737) (meaning t m 2766) (meaning t m 3583) (meaning t m 3692) (meaning t m 4120) source

theorem rule18500 (p1986 p2027 p2230 p2633 p3540 p3644 p3684 : Prop) (h : (¬ p1986) ∨ (¬ p2230) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3684) ∨ p2633 ∨ (¬ p3540)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2230) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial18500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7772 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule18500 (meaning t m 1986) (meaning t m 2027) (meaning t m 2230) (meaning t m 2633) (meaning t m 3540) (meaning t m 3644) (meaning t m 3684) source

theorem rule18501 (p1975 p2027 p2122 p2287 p2774 p3323 p4232 p5265 : Prop) (h : p2027 ∨ (¬ p5265) ∨ (¬ p4232) ∨ (¬ p2774) ∨ (¬ p3323) ∨ (¬ p2122) ∨ (¬ p1975) ∨ p2287) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p2287) ∨ (¬ p2774) ∨ (¬ p3323) ∨ (¬ p4232) ∨ (¬ p5265) := by
  classical
  tauto

theorem initial18501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5265)) := by
  have source := ElevenTheory.theory7773 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 9) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule18501 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2287) (meaning t m 2774) (meaning t m 3323) (meaning t m 4232) (meaning t m 5265) source

theorem rule18504 (p2006 p2027 p2765 p2839 p2901 p3588 p3952 p4169 : Prop) (h : (¬ p3588) ∨ (¬ p2839) ∨ (¬ p2006) ∨ (¬ p2901) ∨ p2765 ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4169)) : (¬ p2006) ∨ (p2027) ∨ (p2765) ∨ (¬ p2839) ∨ (¬ p2901) ∨ (¬ p3588) ∨ (¬ p3952) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial18504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory7776 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18504 (meaning t m 2006) (meaning t m 2027) (meaning t m 2765) (meaning t m 2839) (meaning t m 2901) (meaning t m 3588) (meaning t m 3952) (meaning t m 4169) source

theorem rule18505 (p1987 p2027 p2765 p2901 p3246 p3952 p4324 p4357 : Prop) (h : (¬ p3952) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p4357) ∨ (¬ p4324) ∨ (¬ p3246) ∨ (¬ p2901) ∨ p2765) : (¬ p1987) ∨ (p2027) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4324) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial18505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory7777 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule18505 (meaning t m 1987) (meaning t m 2027) (meaning t m 2765) (meaning t m 2901) (meaning t m 3246) (meaning t m 3952) (meaning t m 4324) (meaning t m 4357) source

theorem rule18506 (p1990 p2027 p2114 p3093 p3097 p3309 p3954 : Prop) (h : (¬ p3309) ∨ (¬ p3097) ∨ (¬ p3093) ∨ p2114 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7778 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule18506 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 3093) (meaning t m 3097) (meaning t m 3309) (meaning t m 3954) source

theorem rule18508 (p1985 p2027 p2870 p3694 p3998 p4080 p5568 : Prop) (h : p2027 ∨ p4080 ∨ (¬ p3694) ∨ (¬ p1985) ∨ (¬ p2870) ∨ (¬ p5568) ∨ (¬ p3998)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p3998) ∨ (p4080) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3998)) ∨ (meaning t m 4080) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7780 t (m.theta 0 8) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 10)
  exact rule18508 (meaning t m 1985) (meaning t m 2027) (meaning t m 2870) (meaning t m 3694) (meaning t m 3998) (meaning t m 4080) (meaning t m 5568) source

theorem rule18510 (p1975 p2027 p2122 p2144 p2156 p2187 p2611 p4358 : Prop) (h : p2027 ∨ (¬ p4358) ∨ p2611 ∨ (¬ p2144) ∨ (¬ p1975) ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2122)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (p2611) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7782 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18510 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2144) (meaning t m 2156) (meaning t m 2187) (meaning t m 2611) (meaning t m 4358) source

theorem rule18511 (p1975 p2027 p2344 p2383 p3246 p3872 p3989 p4107 : Prop) (h : p2344 ∨ (¬ p2383) ∨ (¬ p3872) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p4107) ∨ (¬ p3989) ∨ (¬ p3246)) : (¬ p1975) ∨ (p2027) ∨ (p2344) ∨ (¬ p2383) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7783 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule18511 (meaning t m 1975) (meaning t m 2027) (meaning t m 2344) (meaning t m 2383) (meaning t m 3246) (meaning t m 3872) (meaning t m 3989) (meaning t m 4107) source

theorem rule18512 (p1975 p2027 p2202 p2417 p2437 p2440 p4107 : Prop) (h : (¬ p2437) ∨ p2202 ∨ (¬ p1975) ∨ (¬ p4107) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2417)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7784 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18512 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2437) (meaning t m 2440) (meaning t m 4107) source

theorem rule18513 (p2015 p2027 p2964 p3093 p3276 p3834 p4321 : Prop) (h : (¬ p4321) ∨ (¬ p2015) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3834) ∨ p2964 ∨ (¬ p3276)) : (¬ p2015) ∨ (p2027) ∨ (p2964) ∨ (¬ p3093) ∨ (¬ p3276) ∨ (¬ p3834) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial18513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory7785 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 4 9) (m.theta 9 10)
  exact rule18513 (meaning t m 2015) (meaning t m 2027) (meaning t m 2964) (meaning t m 3093) (meaning t m 3276) (meaning t m 3834) (meaning t m 4321) source

theorem rule18514 (p1982 p2027 p2187 p2363 p2542 p2545 p2563 : Prop) (h : (¬ p2542) ∨ p2545 ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p1982) ∨ (¬ p2187)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial18514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory7786 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18514 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 2542) (meaning t m 2545) (meaning t m 2563) source

theorem rule18518 (p1975 p2027 p2187 p2202 p2307 p2387 p2563 : Prop) (h : (¬ p2387) ∨ (¬ p1975) ∨ (¬ p2307) ∨ p2202 ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2187)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2187) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial18518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory7790 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18518 (meaning t m 1975) (meaning t m 2027) (meaning t m 2187) (meaning t m 2202) (meaning t m 2307) (meaning t m 2387) (meaning t m 2563) source

theorem rule18519 (p1990 p2027 p2233 p2437 p2573 p3097 p3574 p4710 : Prop) (h : (¬ p1990) ∨ (¬ p3097) ∨ p2233 ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2437) ∨ (¬ p4710)) : (¬ p1990) ∨ (p2027) ∨ (p2233) ∨ (¬ p2437) ∨ (¬ p2573) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial18519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory7791 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule18519 (meaning t m 1990) (meaning t m 2027) (meaning t m 2233) (meaning t m 2437) (meaning t m 2573) (meaning t m 3097) (meaning t m 3574) (meaning t m 4710) source

theorem rule18523 (p2000 p2027 p2462 p2542 p2589 p3742 p4278 : Prop) (h : (¬ p2000) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3742) ∨ p2462 ∨ (¬ p4278)) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial18523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory7795 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule18523 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2542) (meaning t m 2589) (meaning t m 3742) (meaning t m 4278) source

theorem rule18524 (p1977 p2027 p2765 p2901 p3238 p3402 p3952 p4235 : Prop) (h : (¬ p3952) ∨ (¬ p4235) ∨ (¬ p3402) ∨ p2027 ∨ p2765 ∨ (¬ p3238) ∨ (¬ p1977) ∨ (¬ p2901)) : (¬ p1977) ∨ (p2027) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3952) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7796 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18524 (meaning t m 1977) (meaning t m 2027) (meaning t m 2765) (meaning t m 2901) (meaning t m 3238) (meaning t m 3402) (meaning t m 3952) (meaning t m 4235) source

theorem rule18525 (p1995 p2027 p2766 p3379 p3548 p4348 p4366 : Prop) (h : (¬ p1995) ∨ (¬ p4348) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4366) ∨ p2027 ∨ p2766) : (¬ p1995) ∨ (p2027) ∨ (p2766) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7797 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18525 (meaning t m 1995) (meaning t m 2027) (meaning t m 2766) (meaning t m 3379) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) source

theorem rule18528 (p1991 p2027 p2187 p2765 p2901 p2950 p3324 p3556 p4153 : Prop) (h : (¬ p1991) ∨ p2765 ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p2950) ∨ (¬ p4153)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2187) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3324) ∨ (¬ p3556) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial18528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory7800 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule18528 (meaning t m 1991) (meaning t m 2027) (meaning t m 2187) (meaning t m 2765) (meaning t m 2901) (meaning t m 2950) (meaning t m 3324) (meaning t m 3556) (meaning t m 4153) source

theorem rule18529 (p1997 p2027 p2187 p2406 p2499 p2765 p3956 : Prop) (h : p2765 ∨ (¬ p2499) ∨ (¬ p2187) ∨ (¬ p1997) ∨ (¬ p3956) ∨ (¬ p2406) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (p2765) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7801 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule18529 (meaning t m 1997) (meaning t m 2027) (meaning t m 2187) (meaning t m 2406) (meaning t m 2499) (meaning t m 2765) (meaning t m 3956) source

theorem rule18531 (p1981 p2027 p2608 p2699 p3537 p3609 p4347 : Prop) (h : (¬ p1981) ∨ p2699 ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p3537) ∨ (¬ p4347)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7803 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18531 (meaning t m 1981) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3537) (meaning t m 3609) (meaning t m 4347) source

theorem rule18532 (p2018 p3537 p3818 p4866 : Prop) (h : p3818 ∨ p4866 ∨ (¬ p3537) ∨ (¬ p2018)) : (¬ p2018) ∨ (¬ p3537) ∨ (p3818) ∨ (p4866) := by
  classical
  tauto

theorem initial18532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (¬ (meaning t m 3537)) ∨ (meaning t m 3818) ∨ (meaning t m 4866) := by
  have source := ElevenTheory.theory7804 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 8)
  exact rule18532 (meaning t m 2018) (meaning t m 3537) (meaning t m 3818) (meaning t m 4866) source

theorem rule18533 (p3549 p3923 p3955 : Prop) (h : (¬ p3549) ∨ (¬ p3955) ∨ p3923) : (¬ p3549) ∨ (p3923) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial18533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3549)) ∨ (meaning t m 3923) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory7805 (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18533 (meaning t m 3549) (meaning t m 3923) (meaning t m 3955) source

theorem rule18536 (p1975 p2027 p2122 p2383 p2786 p2842 p3055 p3923 p4024 : Prop) (h : p2842 ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2786) ∨ (¬ p1975) ∨ (¬ p3055) ∨ (¬ p4024) ∨ (¬ p2383) ∨ (¬ p3923)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3923) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial18536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2786)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory7808 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18536 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2383) (meaning t m 2786) (meaning t m 2842) (meaning t m 3055) (meaning t m 3923) (meaning t m 4024) source

theorem rule18538 (p1975 p2027 p2122 p2785 p3115 p3497 p3578 p3946 p5045 : Prop) (h : (¬ p5045) ∨ (¬ p2785) ∨ (¬ p2122) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p3115) ∨ p3578 ∨ (¬ p3946)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2785) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (p3578) ∨ (¬ p3946) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial18538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory7810 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule18538 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2785) (meaning t m 3115) (meaning t m 3497) (meaning t m 3578) (meaning t m 3946) (meaning t m 5045) source

theorem rule18539 (p2518 p3222 p3358 : Prop) (h : (¬ p3358) ∨ (¬ p2518) ∨ p3222) : (¬ p2518) ∨ (p3222) ∨ (¬ p3358) := by
  classical
  tauto

theorem initial18539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (meaning t m 3222) ∨ (¬ (meaning t m 3358)) := by
  have source := ElevenTheory.theory7811 (m.theta 1 4) (m.theta 4 8) (m.theta 4 9)
  exact rule18539 (meaning t m 2518) (meaning t m 3222) (meaning t m 3358) source

theorem rule18540 (p1975 p2027 p2383 p2553 p2622 p2797 p3567 p3956 : Prop) (h : p2027 ∨ p2622 ∨ (¬ p2383) ∨ (¬ p1975) ∨ (¬ p2797) ∨ (¬ p2553) ∨ (¬ p3567) ∨ (¬ p3956)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7812 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18540 (meaning t m 1975) (meaning t m 2027) (meaning t m 2383) (meaning t m 2553) (meaning t m 2622) (meaning t m 2797) (meaning t m 3567) (meaning t m 3956) source

theorem rule18541 (p2619 p3156 p4316 : Prop) (h : (¬ p4316) ∨ (¬ p2619) ∨ p3156) : (¬ p2619) ∨ (p3156) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial18541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory7813 (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule18541 (meaning t m 2619) (meaning t m 3156) (meaning t m 4316) source

theorem rule18545 (p1983 p2027 p2417 p2579 p2842 p3389 p3422 : Prop) (h : (¬ p2417) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2579) ∨ (¬ p3422) ∨ p2842) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2579) ∨ (p2842) ∨ (¬ p3389) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial18545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory7817 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule18545 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2579) (meaning t m 2842) (meaning t m 3389) (meaning t m 3422) source

theorem rule18546 (p1998 p2027 p2545 p2579 p2911 p3016 p3389 : Prop) (h : p2027 ∨ (¬ p3016) ∨ (¬ p2911) ∨ p2545 ∨ (¬ p1998) ∨ (¬ p2579) ∨ (¬ p3389)) : (¬ p1998) ∨ (p2027) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3016) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial18546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory7818 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule18546 (meaning t m 1998) (meaning t m 2027) (meaning t m 2545) (meaning t m 2579) (meaning t m 2911) (meaning t m 3016) (meaning t m 3389) source

theorem rule18548 (p1998 p2027 p2177 p2417 p2437 p2545 p4107 : Prop) (h : (¬ p2417) ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p4107) ∨ p2027 ∨ p2545 ∨ (¬ p2437)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7820 t (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18548 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2417) (meaning t m 2437) (meaning t m 2545) (meaning t m 4107) source

theorem rule18549 (p1987 p2027 p2233 p2470 p2737 p3585 p3874 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p3585) ∨ (¬ p1987) ∨ (¬ p2737) ∨ (¬ p2470) ∨ (¬ p3874)) : (¬ p1987) ∨ (p2027) ∨ (p2233) ∨ (¬ p2470) ∨ (¬ p2737) ∨ (¬ p3585) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial18549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory7821 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 8)
  exact rule18549 (meaning t m 1987) (meaning t m 2027) (meaning t m 2233) (meaning t m 2470) (meaning t m 2737) (meaning t m 3585) (meaning t m 3874) source

theorem rule18551 (p1982 p2027 p2842 p3055 p3619 p3670 p4444 : Prop) (h : (¬ p3619) ∨ (¬ p4444) ∨ (¬ p3055) ∨ (¬ p1982) ∨ (¬ p3670) ∨ p2027 ∨ p2842) : (¬ p1982) ∨ (p2027) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7823 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18551 (meaning t m 1982) (meaning t m 2027) (meaning t m 2842) (meaning t m 3055) (meaning t m 3619) (meaning t m 3670) (meaning t m 4444) source

theorem rule18552 (p1988 p2027 p2493 p2699 p3379 p3461 p3564 : Prop) (h : p2027 ∨ (¬ p1988) ∨ (¬ p3461) ∨ p2699 ∨ (¬ p2493) ∨ (¬ p3564) ∨ (¬ p3379)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial18552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory7824 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule18552 (meaning t m 1988) (meaning t m 2027) (meaning t m 2493) (meaning t m 2699) (meaning t m 3379) (meaning t m 3461) (meaning t m 3564) source

theorem rule18553 (p2001 p2027 p2619 p2699 p3093 p4053 p4193 p4329 : Prop) (h : (¬ p2001) ∨ p2699 ∨ p2027 ∨ (¬ p4053) ∨ (¬ p2619) ∨ (¬ p4193) ∨ (¬ p4329) ∨ (¬ p3093)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2619) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4193) ∨ (¬ p4329) := by
  classical
  tauto

theorem initial18553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4329)) := by
  have source := ElevenTheory.theory7825 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 10)
  exact rule18553 (meaning t m 2001) (meaning t m 2027) (meaning t m 2619) (meaning t m 2699) (meaning t m 3093) (meaning t m 4053) (meaning t m 4193) (meaning t m 4329) source

theorem rule18554 (p1985 p2027 p2284 p2427 p2504 p2545 p2590 p3413 p3737 p4435 : Prop) (h : (¬ p1985) ∨ (¬ p3413) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2284) ∨ p2545 ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3737) ∨ (¬ p4435)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2427) ∨ (¬ p2504) ∨ (p2545) ∨ (¬ p2590) ∨ (¬ p3413) ∨ (¬ p3737) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial18554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2504)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory7826 t (m.theta 1 6) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10)
  exact rule18554 (meaning t m 1985) (meaning t m 2027) (meaning t m 2284) (meaning t m 2427) (meaning t m 2504) (meaning t m 2545) (meaning t m 2590) (meaning t m 3413) (meaning t m 3737) (meaning t m 4435) source

theorem rule18556 (p2005 p2027 p2233 p2588 p3212 p3309 p4338 p4363 p4399 : Prop) (h : p2233 ∨ (¬ p4363) ∨ (¬ p2588) ∨ (¬ p3212) ∨ (¬ p4338) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p2005) ∨ (¬ p3309)) : (¬ p2005) ∨ (p2027) ∨ (p2233) ∨ (¬ p2588) ∨ (¬ p3212) ∨ (¬ p3309) ∨ (¬ p4338) ∨ (¬ p4363) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial18556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory7828 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7)
  exact rule18556 (meaning t m 2005) (meaning t m 2027) (meaning t m 2233) (meaning t m 2588) (meaning t m 3212) (meaning t m 3309) (meaning t m 4338) (meaning t m 4363) (meaning t m 4399) source

theorem rule18557 (p1999 p2027 p2406 p2563 p2699 p3125 p3379 : Prop) (h : (¬ p2563) ∨ (¬ p1999) ∨ (¬ p3379) ∨ p2699 ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3125)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p3125) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial18557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory7829 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule18557 (meaning t m 1999) (meaning t m 2027) (meaning t m 2406) (meaning t m 2563) (meaning t m 2699) (meaning t m 3125) (meaning t m 3379) source

theorem rule18558 (p1977 p2027 p2331 p2633 p3414 p3553 p4154 : Prop) (h : (¬ p4154) ∨ p2633 ∨ (¬ p1977) ∨ (¬ p2331) ∨ (¬ p3553) ∨ (¬ p3414) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial18558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory7830 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule18558 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2633) (meaning t m 3414) (meaning t m 3553) (meaning t m 4154) source

theorem rule18559 (p2001 p2027 p2373 p2622 p2630 p2656 p3212 p4399 p4948 : Prop) (h : (¬ p4399) ∨ p2622 ∨ (¬ p2001) ∨ (¬ p2373) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4948) ∨ (¬ p3212)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2373) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial18559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7831 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule18559 (meaning t m 2001) (meaning t m 2027) (meaning t m 2373) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3212) (meaning t m 4399) (meaning t m 4948) source

theorem rule18562 (p1992 p2027 p2743 p2764 p3361 p3414 p3947 p4381 : Prop) (h : (¬ p2743) ∨ (¬ p3414) ∨ p2764 ∨ (¬ p3361) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3947) ∨ (¬ p4381)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7834 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18562 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2764) (meaning t m 3361) (meaning t m 3414) (meaning t m 3947) (meaning t m 4381) source

theorem rule18564 (p1977 p2027 p2764 p2807 p2996 p3292 p5284 : Prop) (h : (¬ p1977) ∨ (¬ p5284) ∨ p2764 ∨ (¬ p2996) ∨ (¬ p3292) ∨ (¬ p2807) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (p2764) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3292) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7836 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 9 10)
  exact rule18564 (meaning t m 1977) (meaning t m 2027) (meaning t m 2764) (meaning t m 2807) (meaning t m 2996) (meaning t m 3292) (meaning t m 5284) source

theorem rule18565 (p1985 p2027 p2156 p2427 p2622 p2951 p3136 p4110 : Prop) (h : p2027 ∨ (¬ p4110) ∨ (¬ p2156) ∨ (¬ p1985) ∨ (¬ p2427) ∨ (¬ p2951) ∨ (¬ p3136) ∨ p2622) : (¬ p1985) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7837 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18565 (meaning t m 1985) (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) (meaning t m 4110) source

theorem rule18566 (p1976 p2027 p2122 p2313 p2778 p3982 p4358 p5580 : Prop) (h : p3982 ∨ (¬ p1976) ∨ (¬ p5580) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2778) ∨ (¬ p2313)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (p3982) ∨ (¬ p4358) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7838 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule18566 (meaning t m 1976) (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2778) (meaning t m 3982) (meaning t m 4358) (meaning t m 5580) source

theorem rule18568 (p1975 p2027 p2284 p2766 p2954 p3125 p3204 p3309 p3553 p3556 p3946 p4333 p4348 : Prop) (h : p2027 ∨ (¬ p3309) ∨ (¬ p3946) ∨ (¬ p3204) ∨ p2766 ∨ (¬ p4333) ∨ (¬ p3125) ∨ (¬ p2284) ∨ (¬ p4348) ∨ (¬ p2954) ∨ (¬ p3556) ∨ (¬ p3553) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2284) ∨ (p2766) ∨ (¬ p2954) ∨ (¬ p3125) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p3946) ∨ (¬ p4333) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7840 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule18568 (meaning t m 1975) (meaning t m 2027) (meaning t m 2284) (meaning t m 2766) (meaning t m 2954) (meaning t m 3125) (meaning t m 3204) (meaning t m 3309) (meaning t m 3553) (meaning t m 3556) (meaning t m 3946) (meaning t m 4333) (meaning t m 4348) source

theorem rule18570 (p1987 p2027 p2459 p2633 p2737 p3588 p3857 p3959 p3961 : Prop) (h : (¬ p3961) ∨ (¬ p3857) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p2459) ∨ p2633 ∨ p2027 ∨ (¬ p2737) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3588) ∨ (¬ p3857) ∨ (¬ p3959) ∨ (¬ p3961) := by
  classical
  tauto

theorem initial18570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 3961)) := by
  have source := ElevenTheory.theory7842 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18570 (meaning t m 1987) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2737) (meaning t m 3588) (meaning t m 3857) (meaning t m 3959) (meaning t m 3961) source

theorem rule18573 (p2001 p2027 p2373 p2545 p2839 p3193 p3343 p3695 p4257 : Prop) (h : (¬ p2839) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4257) ∨ (¬ p2001) ∨ (¬ p3695) ∨ (¬ p3343) ∨ (¬ p3193) ∨ p2545) : (¬ p2001) ∨ (p2027) ∨ (¬ p2373) ∨ (p2545) ∨ (¬ p2839) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3695) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial18573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory7845 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 8)
  exact rule18573 (meaning t m 2001) (meaning t m 2027) (meaning t m 2373) (meaning t m 2545) (meaning t m 2839) (meaning t m 3193) (meaning t m 3343) (meaning t m 3695) (meaning t m 4257) source

theorem rule18574 (p1985 p2027 p2144 p2191 p2220 p2842 p2870 p3055 p4243 : Prop) (h : (¬ p3055) ∨ p2027 ∨ p2842 ∨ (¬ p2220) ∨ (¬ p1985) ∨ (¬ p2870) ∨ (¬ p4243) ∨ (¬ p2144) ∨ (¬ p2191)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (p2842) ∨ (¬ p2870) ∨ (¬ p3055) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial18574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory7846 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule18574 (meaning t m 1985) (meaning t m 2027) (meaning t m 2144) (meaning t m 2191) (meaning t m 2220) (meaning t m 2842) (meaning t m 2870) (meaning t m 3055) (meaning t m 4243) source

theorem rule18575 (p2003 p2027 p2387 p2668 p2766 p3266 p5274 p5284 : Prop) (h : (¬ p2668) ∨ (¬ p2003) ∨ p2766 ∨ p2027 ∨ (¬ p2387) ∨ (¬ p5284) ∨ (¬ p3266) ∨ (¬ p5274)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7847 t (m.theta 0 6) (m.theta 3 6) (m.theta 3 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18575 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2766) (meaning t m 3266) (meaning t m 5274) (meaning t m 5284) source

theorem rule18576 (p2001 p2027 p2518 p2528 p2699 p3379 p3692 : Prop) (h : (¬ p2518) ∨ p2699 ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2001) ∨ (¬ p2528) ∨ (¬ p3692)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial18576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7848 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18576 (meaning t m 2001) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2699) (meaning t m 3379) (meaning t m 3692) source

theorem rule18577 (p1992 p2027 p2608 p2765 p2870 p3758 p4366 p4909 : Prop) (h : p2027 ∨ (¬ p4909) ∨ (¬ p1992) ∨ (¬ p4366) ∨ p2765 ∨ (¬ p2870) ∨ (¬ p2608) ∨ (¬ p3758)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4366) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial18577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory7849 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18577 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2765) (meaning t m 2870) (meaning t m 3758) (meaning t m 4366) (meaning t m 4909) source

theorem rule18578 (p1997 p2027 p2341 p2542 p3360 p3644 p3742 : Prop) (h : p2027 ∨ p3360 ∨ (¬ p1997) ∨ (¬ p3644) ∨ (¬ p2542) ∨ (¬ p2341) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2542) ∨ (p3360) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial18578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory7850 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule18578 (meaning t m 1997) (meaning t m 2027) (meaning t m 2341) (meaning t m 2542) (meaning t m 3360) (meaning t m 3644) (meaning t m 3742) source

theorem rule18580 (p1982 p2027 p2363 p2409 p3063 p3093 p3452 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p3063) ∨ (¬ p3452) ∨ (¬ p2363) ∨ (¬ p3093) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2409) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial18580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory7852 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18580 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2409) (meaning t m 3063) (meaning t m 3093) (meaning t m 3452) source

theorem rule18581 (p2015 p2241 p2641 p2699 p4757 : Prop) (h : (¬ p2241) ∨ p2699 ∨ (¬ p2641) ∨ (¬ p2015) ∨ p4757) : (¬ p2015) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (p2699) ∨ (p4757) := by
  classical
  tauto

theorem initial18581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) ∨ (meaning t m 4757) := by
  have source := ElevenTheory.theory7853 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule18581 (meaning t m 2015) (meaning t m 2241) (meaning t m 2641) (meaning t m 2699) (meaning t m 4757) source

theorem rule18582 (p1976 p2027 p2462 p3414 p3690 p4129 p4236 p4391 : Prop) (h : p2462 ∨ (¬ p4236) ∨ (¬ p3414) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p4129) ∨ (¬ p3690) ∨ (¬ p4391)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4129) ∨ (¬ p4236) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial18582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory7854 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18582 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 3414) (meaning t m 3690) (meaning t m 4129) (meaning t m 4236) (meaning t m 4391) source

theorem rule18583 (p2002 p2027 p2633 p2774 p3365 p3553 p3572 : Prop) (h : (¬ p2002) ∨ (¬ p3572) ∨ (¬ p3365) ∨ p2633 ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2774)) : (¬ p2002) ∨ (p2027) ∨ (p2633) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial18583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory7855 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 7) (m.theta 7 8)
  exact rule18583 (meaning t m 2002) (meaning t m 2027) (meaning t m 2633) (meaning t m 2774) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) source

theorem rule18584 (p1981 p2027 p2409 p3073 p3449 p3452 p4347 : Prop) (h : (¬ p3073) ∨ p2409 ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4347) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (p2409) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7856 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18584 (meaning t m 1981) (meaning t m 2027) (meaning t m 2409) (meaning t m 3073) (meaning t m 3449) (meaning t m 3452) (meaning t m 4347) source

theorem rule18586 (p1975 p2027 p2493 p2545 p2553 p3193 p3343 : Prop) (h : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3193) ∨ (¬ p2493) ∨ (¬ p3343) ∨ p2545) : (¬ p1975) ∨ (p2027) ∨ (¬ p2493) ∨ (p2545) ∨ (¬ p2553) ∨ (¬ p3193) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial18586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory7858 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7)
  exact rule18586 (meaning t m 1975) (meaning t m 2027) (meaning t m 2493) (meaning t m 2545) (meaning t m 2553) (meaning t m 3193) (meaning t m 3343) source

theorem rule18589 (p1992 p2027 p2608 p3105 p3578 p3694 p3834 p4388 : Prop) (h : (¬ p4388) ∨ (¬ p1992) ∨ (¬ p3694) ∨ p3578 ∨ (¬ p3105) ∨ p2027 ∨ (¬ p3834) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p3105) ∨ (p3578) ∨ (¬ p3694) ∨ (¬ p3834) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial18589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3105)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory7861 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 5) (m.theta 5 8) (m.theta 5 9)
  exact rule18589 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 3105) (meaning t m 3578) (meaning t m 3694) (meaning t m 3834) (meaning t m 4388) source

theorem rule18590 (p2010 p2027 p2545 p2685 p2810 p3931 p5503 : Prop) (h : (¬ p2810) ∨ (¬ p2010) ∨ p2545 ∨ p2027 ∨ (¬ p5503) ∨ (¬ p2685) ∨ (¬ p3931)) : (¬ p2010) ∨ (p2027) ∨ (p2545) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3931) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial18590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory7862 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10)
  exact rule18590 (meaning t m 2010) (meaning t m 2027) (meaning t m 2545) (meaning t m 2685) (meaning t m 2810) (meaning t m 3931) (meaning t m 5503) source

theorem rule18591 (p1988 p2027 p2545 p2573 p2810 p3414 p3461 p3564 p4236 p4253 p4391 p4419 p4781 : Prop) (h : (¬ p2573) ∨ (¬ p4781) ∨ p2027 ∨ (¬ p2810) ∨ p2545 ∨ (¬ p4419) ∨ (¬ p1988) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4253) ∨ (¬ p3414) ∨ (¬ p4236) ∨ (¬ p4391)) : (¬ p1988) ∨ (p2027) ∨ (p2545) ∨ (¬ p2573) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4236) ∨ (¬ p4253) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial18591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory7863 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule18591 (meaning t m 1988) (meaning t m 2027) (meaning t m 2545) (meaning t m 2573) (meaning t m 2810) (meaning t m 3414) (meaning t m 3461) (meaning t m 3564) (meaning t m 4236) (meaning t m 4253) (meaning t m 4391) (meaning t m 4419) (meaning t m 4781) source

theorem rule18593 (p1976 p2027 p2459 p2633 p3365 p3877 p4118 : Prop) (h : p2027 ∨ (¬ p3365) ∨ (¬ p1976) ∨ (¬ p4118) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p3877)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial18593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7865 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18593 (meaning t m 1976) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) source

theorem rule18595 (p1997 p2027 p2166 p2210 p2409 p3452 p3880 : Prop) (h : (¬ p3452) ∨ p2409 ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p1997) ∨ (¬ p3880)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p3452) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial18595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory7867 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule18595 (meaning t m 1997) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2409) (meaning t m 3452) (meaning t m 3880) source

theorem rule18596 (p1982 p2027 p2352 p2363 p2573 p2765 p3292 p3755 p3952 p4236 p4315 p4419 : Prop) (h : (¬ p3292) ∨ p2765 ∨ p2027 ∨ (¬ p2352) ∨ (¬ p4419) ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p4315) ∨ (¬ p4236) ∨ (¬ p3755) ∨ (¬ p3952)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (p2765) ∨ (¬ p3292) ∨ (¬ p3755) ∨ (¬ p3952) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial18596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory7868 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18596 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2765) (meaning t m 3292) (meaning t m 3755) (meaning t m 3952) (meaning t m 4236) (meaning t m 4315) (meaning t m 4419) source

theorem rule18597 (p1982 p2027 p2233 p2573 p3461 p3564 p4444 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p3564) ∨ (¬ p1982) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2233) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7869 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18597 (meaning t m 1982) (meaning t m 2027) (meaning t m 2233) (meaning t m 2573) (meaning t m 3461) (meaning t m 3564) (meaning t m 4444) source

theorem rule18598 (p1981 p2027 p2088 p2545 p2797 p2810 p3567 p4114 p4347 : Prop) (h : (¬ p1981) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2810) ∨ p2545 ∨ (¬ p2797) ∨ (¬ p2088)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2088) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7870 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18598 (meaning t m 1981) (meaning t m 2027) (meaning t m 2088) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 3567) (meaning t m 4114) (meaning t m 4347) source

theorem rule18602 (p1992 p2027 p2287 p2295 p2608 p3549 p3591 : Prop) (h : (¬ p3591) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3549) ∨ (¬ p2608) ∨ p2287) : (¬ p1992) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2608) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial18602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory7874 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule18602 (meaning t m 1992) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2608) (meaning t m 3549) (meaning t m 3591) source

theorem rule18603 (p1987 p2027 p2737 p2764 p3588 p4324 p4381 : Prop) (h : (¬ p4324) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2737) ∨ p2764 ∨ (¬ p1987) ∨ (¬ p3588)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2764) ∨ (¬ p3588) ∨ (¬ p4324) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7875 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18603 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2764) (meaning t m 3588) (meaning t m 4324) (meaning t m 4381) source

theorem rule18604 (p1990 p2027 p2230 p2505 p2699 p3097 p3238 p3309 p4079 : Prop) (h : (¬ p2505) ∨ p2699 ∨ p2027 ∨ (¬ p4079) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p3309)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2505) ∨ (p2699) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial18604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2505)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory7876 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule18604 (meaning t m 1990) (meaning t m 2027) (meaning t m 2230) (meaning t m 2505) (meaning t m 2699) (meaning t m 3097) (meaning t m 3238) (meaning t m 3309) (meaning t m 4079) source

theorem rule18606 (p1990 p2027 p2233 p2470 p2542 p2563 p4256 : Prop) (h : p2233 ∨ p2027 ∨ (¬ p1990) ∨ (¬ p4256) ∨ (¬ p2563) ∨ (¬ p2542) ∨ (¬ p2470)) : (¬ p1990) ∨ (p2027) ∨ (p2233) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7878 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule18606 (meaning t m 1990) (meaning t m 2027) (meaning t m 2233) (meaning t m 2470) (meaning t m 2542) (meaning t m 2563) (meaning t m 4256) source

theorem rule18607 (p1992 p2027 p2202 p2696 p2743 p3055 p3684 : Prop) (h : p2027 ∨ p2202 ∨ (¬ p2696) ∨ (¬ p3684) ∨ (¬ p1992) ∨ (¬ p2743) ∨ (¬ p3055)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial18607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7879 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule18607 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2696) (meaning t m 2743) (meaning t m 3055) (meaning t m 3684) source

theorem rule18609 (p1976 p2027 p2352 p2588 p2780 p2997 p4358 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p4358) ∨ (¬ p2352) ∨ (¬ p2780)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7881 t (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18609 (meaning t m 1976) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2780) (meaning t m 2997) (meaning t m 4358) source

theorem rule18611 (p1998 p2027 p2264 p2622 p2807 p2952 p3136 : Prop) (h : (¬ p1998) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p3136) ∨ p2622 ∨ (¬ p2952) ∨ (¬ p2264)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2622) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial18611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory7883 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule18611 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2622) (meaning t m 2807) (meaning t m 2952) (meaning t m 3136) source

theorem rule18612 (p1988 p2027 p2622 p2952 p3136 p3286 p3680 p4039 : Prop) (h : p2622 ∨ (¬ p4039) ∨ (¬ p3680) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3286) ∨ (¬ p3136) ∨ (¬ p2952)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3286) ∨ (¬ p3680) ∨ (¬ p4039) := by
  classical
  tauto

theorem initial18612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4039)) := by
  have source := ElevenTheory.theory7884 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule18612 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2952) (meaning t m 3136) (meaning t m 3286) (meaning t m 3680) (meaning t m 4039) source

theorem rule18615 (p2023 p2027 p2202 p2528 p3641 p3684 p4261 : Prop) (h : (¬ p3684) ∨ (¬ p2023) ∨ p2202 ∨ (¬ p2528) ∨ (¬ p4261) ∨ (¬ p3641) ∨ p2027) : (¬ p2023) ∨ (p2027) ∨ (p2202) ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial18615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory7887 t (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule18615 (meaning t m 2023) (meaning t m 2027) (meaning t m 2202) (meaning t m 2528) (meaning t m 3641) (meaning t m 3684) (meaning t m 4261) source

theorem rule18617 (p2027 p2307 p2952 p3568 p3987 p4566 : Prop) (h : (¬ p3568) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p4566) ∨ (¬ p3987) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2952) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial18617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory7889 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule18617 (meaning t m 2027) (meaning t m 2307) (meaning t m 2952) (meaning t m 3568) (meaning t m 3987) (meaning t m 4566) source

theorem rule18619 (p2001 p2027 p2608 p2699 p3537 p3609 p3692 : Prop) (h : (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3537) ∨ p2027 ∨ p2699 ∨ (¬ p2608) ∨ (¬ p2001)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial18619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7891 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18619 (meaning t m 2001) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3537) (meaning t m 3609) (meaning t m 3692) source

theorem rule18622 (p1987 p2027 p2633 p2651 p2810 p3414 p3553 : Prop) (h : (¬ p2651) ∨ (¬ p3553) ∨ (¬ p2810) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p1987) ∨ p2633) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial18622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory7894 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule18622 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2651) (meaning t m 2810) (meaning t m 3414) (meaning t m 3553) source

theorem rule18625 (p1987 p2027 p2766 p2810 p3347 p3487 p3540 p3644 p4348 : Prop) (h : p2027 ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p4348) ∨ (¬ p3644) ∨ p2766 ∨ (¬ p1987) ∨ (¬ p2810) ∨ (¬ p3487)) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7897 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18625 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 2810) (meaning t m 3347) (meaning t m 3487) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) source

theorem rule18627 (p1987 p2027 p2462 p2656 p2737 p3363 p3585 p3742 p4278 : Prop) (h : (¬ p2656) ∨ (¬ p3742) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p1987) ∨ (¬ p3363) ∨ p2462 ∨ (¬ p4278)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2656) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial18627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory7899 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule18627 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2656) (meaning t m 2737) (meaning t m 3363) (meaning t m 3585) (meaning t m 3742) (meaning t m 4278) source

theorem rule18628 (p1987 p2027 p2202 p2563 p2737 p3363 p3585 p3646 p3904 : Prop) (h : (¬ p3904) ∨ (¬ p3646) ∨ (¬ p2737) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3363) ∨ (¬ p3585) ∨ p2202 ∨ (¬ p2563)) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial18628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory7900 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule18628 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2737) (meaning t m 3363) (meaning t m 3585) (meaning t m 3646) (meaning t m 3904) source

theorem rule18630 (p2001 p2027 p2202 p3641 p3684 p4149 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p3641) ∨ (¬ p2001) ∨ p2202 ∨ (¬ p3684) ∨ p2027 ∨ (¬ p4149)) : (¬ p2001) ∨ (p2027) ∨ (p2202) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4149) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7902 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule18630 (meaning t m 2001) (meaning t m 2027) (meaning t m 2202) (meaning t m 3641) (meaning t m 3684) (meaning t m 4149) (meaning t m 5568) source

theorem rule18631 (p1992 p2027 p2534 p2657 p2743 p2766 p3361 p4256 : Prop) (h : (¬ p1992) ∨ (¬ p3361) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2743) ∨ p2766) : (¬ p1992) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p3361) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7903 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule18631 (meaning t m 1992) (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 2743) (meaning t m 2766) (meaning t m 3361) (meaning t m 4256) source

theorem rule18634 (p1992 p2027 p2657 p2743 p2764 p3359 p3361 p4425 : Prop) (h : p2027 ∨ (¬ p4425) ∨ (¬ p1992) ∨ (¬ p2657) ∨ (¬ p3361) ∨ (¬ p2743) ∨ p2764 ∨ (¬ p3359)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p3359) ∨ (¬ p3361) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial18634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory7906 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule18634 (meaning t m 1992) (meaning t m 2027) (meaning t m 2657) (meaning t m 2743) (meaning t m 2764) (meaning t m 3359) (meaning t m 3361) (meaning t m 4425) source

theorem rule18637 (p2013 p2027 p2598 p3425 p3437 p3585 p3599 : Prop) (h : p2027 ∨ p3437 ∨ (¬ p3425) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p2013) ∨ (¬ p3599)) : (¬ p2013) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p3425) ∨ (p3437) ∨ (¬ p3585) ∨ (¬ p3599) := by
  classical
  tauto

theorem initial18637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2013)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3425)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3599)) := by
  have source := ElevenTheory.theory7909 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 2 9)
  exact rule18637 (meaning t m 2013) (meaning t m 2027) (meaning t m 2598) (meaning t m 3425) (meaning t m 3437) (meaning t m 3585) (meaning t m 3599) source

theorem rule18638 (p1992 p2027 p2598 p2633 p3425 p3585 p3644 p4106 : Prop) (h : (¬ p3644) ∨ p2633 ∨ (¬ p4106) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4106) := by
  classical
  tauto

theorem initial18638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4106)) := by
  have source := ElevenTheory.theory7910 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule18638 (meaning t m 1992) (meaning t m 2027) (meaning t m 2598) (meaning t m 2633) (meaning t m 3425) (meaning t m 3585) (meaning t m 3644) (meaning t m 4106) source

theorem rule18641 (p1991 p2287 p2952 p4563 : Prop) (h : (¬ p1991) ∨ p2287 ∨ (¬ p2952) ∨ p4563) : (¬ p1991) ∨ (p2287) ∨ (¬ p2952) ∨ (p4563) := by
  classical
  tauto

theorem initial18641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 4563) := by
  have source := ElevenTheory.theory7913 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule18641 (meaning t m 1991) (meaning t m 2287) (meaning t m 2952) (meaning t m 4563) source

theorem rule18643 (p1975 p2027 p2299 p2608 p2699 p2707 p2717 : Prop) (h : (¬ p2707) ∨ p2027 ∨ (¬ p2299) ∨ p2699 ∨ (¬ p1975) ∨ (¬ p2717) ∨ (¬ p2608)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) := by
  classical
  tauto

theorem initial18643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) := by
  have source := ElevenTheory.theory7915 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule18643 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) source

theorem rule18644 (p2022 p2027 p2449 p2911 p2914 p3553 p3821 : Prop) (h : p2027 ∨ (¬ p2022) ∨ (¬ p3821) ∨ (¬ p2449) ∨ p2914 ∨ (¬ p2911) ∨ (¬ p3553)) : (¬ p2022) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3553) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial18644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory7916 t (m.theta 0 7) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18644 (meaning t m 2022) (meaning t m 2027) (meaning t m 2449) (meaning t m 2911) (meaning t m 2914) (meaning t m 3553) (meaning t m 3821) source

theorem rule18646 (p2743 p2839 p4392 : Prop) (h : (¬ p4392) ∨ (¬ p2839) ∨ (¬ p2743)) : (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial18646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory7918 (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule18646 (meaning t m 2743) (meaning t m 2839) (meaning t m 4392) source

theorem rule18647 (p1992 p2027 p2169 p2553 p3688 p3822 p3956 : Prop) (h : (¬ p3688) ∨ p2169 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3956) ∨ (¬ p3822) ∨ (¬ p2553)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7919 t (m.theta 1 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18647 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 3688) (meaning t m 3822) (meaning t m 3956) source

theorem rule18650 (p1975 p2027 p3008 p3201 p3584 p3868 p4260 : Prop) (h : p3008 ∨ (¬ p4260) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3868) ∨ (¬ p1975) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (p3008) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3868) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial18650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory7922 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10)
  exact rule18650 (meaning t m 1975) (meaning t m 2027) (meaning t m 3008) (meaning t m 3201) (meaning t m 3584) (meaning t m 3868) (meaning t m 4260) source

theorem rule18652 (p1983 p2027 p2264 p2299 p2323 p2396 p2807 : Prop) (h : (¬ p2299) ∨ p2323 ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p1983) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (p2323) ∨ (¬ p2396) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial18652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory7924 t (m.theta 0 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18652 (meaning t m 1983) (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2323) (meaning t m 2396) (meaning t m 2807) source

theorem rule18654 (p1995 p2027 p3008 p3193 p3584 p3670 p4425 p5165 : Prop) (h : (¬ p3193) ∨ p2027 ∨ (¬ p5165) ∨ (¬ p4425) ∨ p3008 ∨ (¬ p1995) ∨ (¬ p3670) ∨ (¬ p3584)) : (¬ p1995) ∨ (p2027) ∨ (p3008) ∨ (¬ p3193) ∨ (¬ p3584) ∨ (¬ p3670) ∨ (¬ p4425) ∨ (¬ p5165) := by
  classical
  tauto

theorem initial18654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5165)) := by
  have source := ElevenTheory.theory7926 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 9) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule18654 (meaning t m 1995) (meaning t m 2027) (meaning t m 3008) (meaning t m 3193) (meaning t m 3584) (meaning t m 3670) (meaning t m 4425) (meaning t m 5165) source

theorem rule18655 (p1982 p2027 p2331 p2363 p2668 p3055 p3684 p3880 p3982 p4786 p5568 : Prop) (h : (¬ p2668) ∨ (¬ p3684) ∨ (¬ p3055) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p4786) ∨ (¬ p5568) ∨ (¬ p2331) ∨ p2027 ∨ p3982 ∨ (¬ p3880)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (p3982) ∨ (¬ p4786) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7927 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18655 (meaning t m 1982) (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3055) (meaning t m 3684) (meaning t m 3880) (meaning t m 3982) (meaning t m 4786) (meaning t m 5568) source

theorem rule18657 (p1982 p2027 p2247 p2363 p2688 p3998 p5242 p5580 : Prop) (h : (¬ p2247) ∨ p2688 ∨ (¬ p5242) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (p2688) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7929 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 3) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18657 (meaning t m 1982) (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2688) (meaning t m 3998) (meaning t m 5242) (meaning t m 5580) source

theorem rule18663 (p2590 p2850 p3422 : Prop) (h : (¬ p3422) ∨ (¬ p2590) ∨ p2850) : (¬ p2590) ∨ (p2850) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial18663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2590)) ∨ (meaning t m 2850) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory7935 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule18663 (meaning t m 2590) (meaning t m 2850) (meaning t m 3422) source

theorem rule18664 (p1992 p2027 p2202 p2563 p2608 p3555 p4173 : Prop) (h : (¬ p1992) ∨ (¬ p3555) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2563) ∨ p2202) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial18664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7936 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule18664 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2608) (meaning t m 3555) (meaning t m 4173) source

theorem rule18672 (p2005 p2027 p2122 p2169 p2312 p3016 p3742 p4279 p4358 : Prop) (h : (¬ p4279) ∨ (¬ p2312) ∨ (¬ p2122) ∨ p2027 ∨ p2169 ∨ (¬ p2005) ∨ (¬ p4358) ∨ (¬ p3742) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (p2169) ∨ (¬ p2312) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7944 t (m.theta 0 7) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule18672 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2169) (meaning t m 2312) (meaning t m 3016) (meaning t m 3742) (meaning t m 4279) (meaning t m 4358) source

theorem rule18675 (p2005 p2027 p2122 p2588 p2622 p2774 p3365 : Prop) (h : (¬ p3365) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2122) ∨ p2622 ∨ (¬ p2588) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial18675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory7947 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule18675 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2622) (meaning t m 2774) (meaning t m 3365) source

theorem rule18676 (p1975 p2027 p2274 p2323 p2573 p2663 p3888 p4393 : Prop) (h : p2323 ∨ (¬ p2274) ∨ (¬ p4393) ∨ (¬ p3888) ∨ (¬ p2663) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2323) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3888) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial18676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory7948 t (m.theta 0 3) (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7)
  exact rule18676 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2323) (meaning t m 2573) (meaning t m 2663) (meaning t m 3888) (meaning t m 4393) source

theorem rule18679 (p2319 p2962 p4988 : Prop) (h : (¬ p2962) ∨ (¬ p2319) ∨ p4988) : (¬ p2319) ∨ (¬ p2962) ∨ (p4988) := by
  classical
  tauto

theorem initial18679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2962)) ∨ (meaning t m 4988) := by
  have source := ElevenTheory.theory7951 (m.theta 0 5) (m.theta 0 6) (m.theta 0 7)
  exact rule18679 (meaning t m 2319) (meaning t m 2962) (meaning t m 4988) source

theorem rule18681 (p1990 p2027 p2122 p2169 p2563 p4235 p4275 p4358 : Prop) (h : (¬ p4235) ∨ (¬ p2563) ∨ (¬ p4358) ∨ (¬ p4275) ∨ p2169 ∨ (¬ p2122) ∨ p2027 ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2122) ∨ (p2169) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7953 t (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule18681 (meaning t m 1990) (meaning t m 2027) (meaning t m 2122) (meaning t m 2169) (meaning t m 2563) (meaning t m 4235) (meaning t m 4275) (meaning t m 4358) source

theorem rule18683 (p2005 p2027 p2230 p2440 p2964 p3016 p3346 : Prop) (h : (¬ p3016) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2005) ∨ p2964 ∨ (¬ p3346)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2964) ∨ (¬ p3016) ∨ (¬ p3346) := by
  classical
  tauto

theorem initial18683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3346)) := by
  have source := ElevenTheory.theory7955 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule18683 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2964) (meaning t m 3016) (meaning t m 3346) source

theorem rule18685 (p1976 p2027 p2387 p2766 p2778 p3941 p4348 p5580 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p5580) ∨ (¬ p2778) ∨ (¬ p3941) ∨ (¬ p2387) ∨ p2766 ∨ (¬ p4348)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2387) ∨ (p2766) ∨ (¬ p2778) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7957 t (m.theta 0 2) (m.theta 0 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18685 (meaning t m 1976) (meaning t m 2027) (meaning t m 2387) (meaning t m 2766) (meaning t m 2778) (meaning t m 3941) (meaning t m 4348) (meaning t m 5580) source

theorem rule18688 (p1982 p2027 p2323 p3146 p3166 p4009 p5568 : Prop) (h : (¬ p3146) ∨ (¬ p3166) ∨ p2323 ∨ (¬ p4009) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p5568)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p3146) ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7960 t (m.theta 0 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18688 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 3146) (meaning t m 3166) (meaning t m 4009) (meaning t m 5568) source

theorem rule18691 (p2001 p2027 p2247 p2688 p3449 p4149 p4687 p5568 : Prop) (h : (¬ p3449) ∨ (¬ p4687) ∨ (¬ p2001) ∨ (¬ p4149) ∨ p2027 ∨ (¬ p2247) ∨ p2688 ∨ (¬ p5568)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3449) ∨ (¬ p4149) ∨ (¬ p4687) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4687)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7963 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule18691 (meaning t m 2001) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3449) (meaning t m 4149) (meaning t m 4687) (meaning t m 5568) source

theorem rule18695 (p1990 p2284 p3474 p5053 : Prop) (h : p3474 ∨ (¬ p2284) ∨ (¬ p1990) ∨ p5053) : (¬ p1990) ∨ (¬ p2284) ∨ (p3474) ∨ (p5053) := by
  classical
  tauto

theorem initial18695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 3474) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory7967 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule18695 (meaning t m 1990) (meaning t m 2284) (meaning t m 3474) (meaning t m 5053) source

theorem rule18696 (p2027 p2104 p2284 p2946 p3737 p4340 p4444 p4786 p5250 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p2284) ∨ (¬ p5250) ∨ (¬ p2946) ∨ (¬ p3737) ∨ (¬ p4786) ∨ (¬ p4340) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3737) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial18696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory7968 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule18696 (meaning t m 2027) (meaning t m 2104) (meaning t m 2284) (meaning t m 2946) (meaning t m 3737) (meaning t m 4340) (meaning t m 4444) (meaning t m 4786) (meaning t m 5250) source

theorem rule18697 (p2027 p2437 p2573 p3551 p3574 p3609 p3820 p4348 p4419 p4805 p5087 : Prop) (h : (¬ p3820) ∨ (¬ p4805) ∨ (¬ p2437) ∨ (¬ p3609) ∨ (¬ p5087) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4419) ∨ (¬ p3551) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2573) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p3609) ∨ (¬ p3820) ∨ (¬ p4348) ∨ (¬ p4419) ∨ (¬ p4805) ∨ (¬ p5087) := by
  classical
  tauto

theorem initial18697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5087)) := by
  have source := ElevenTheory.theory7969 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 2 7) (m.theta 2 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18697 (meaning t m 2027) (meaning t m 2437) (meaning t m 2573) (meaning t m 3551) (meaning t m 3574) (meaning t m 3609) (meaning t m 3820) (meaning t m 4348) (meaning t m 4419) (meaning t m 4805) (meaning t m 5087) source

theorem rule18699 (p1992 p2027 p2589 p2608 p2633 p3570 p4108 p4235 : Prop) (h : (¬ p2608) ∨ (¬ p4108) ∨ (¬ p1992) ∨ (¬ p2589) ∨ p2027 ∨ p2633 ∨ (¬ p4235) ∨ (¬ p3570)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p4108) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7971 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule18699 (meaning t m 1992) (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2633) (meaning t m 3570) (meaning t m 4108) (meaning t m 4235) source

theorem rule18702 (p2005 p2027 p2169 p2662 p3016 p3309 p3540 p3921 p3923 : Prop) (h : (¬ p3921) ∨ (¬ p3309) ∨ p2169 ∨ (¬ p3540) ∨ (¬ p3923) ∨ (¬ p2005) ∨ (¬ p2662) ∨ (¬ p3016) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (p2169) ∨ (¬ p2662) ∨ (¬ p3016) ∨ (¬ p3309) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial18702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory7974 t (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule18702 (meaning t m 2005) (meaning t m 2027) (meaning t m 2169) (meaning t m 2662) (meaning t m 3016) (meaning t m 3309) (meaning t m 3540) (meaning t m 3921) (meaning t m 3923) source

theorem rule18704 (p1975 p2027 p2274 p2284 p2811 p2946 p3042 p3877 : Prop) (h : (¬ p2284) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2946) ∨ (¬ p2811) ∨ (¬ p3877) ∨ p3042) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (p3042) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial18704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory7976 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7)
  exact rule18704 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2811) (meaning t m 2946) (meaning t m 3042) (meaning t m 3877) source

theorem rule18707 (p1988 p2027 p2230 p2622 p2630 p2656 p2982 p3680 : Prop) (h : (¬ p2630) ∨ p2622 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2982) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial18707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory7979 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule18707 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2982) (meaning t m 3680) source

theorem rule18708 (p2010 p2230 p2233 p4646 : Prop) (h : (¬ p2230) ∨ (¬ p2010) ∨ p2233 ∨ p4646) : (¬ p2010) ∨ (¬ p2230) ∨ (p2233) ∨ (p4646) := by
  classical
  tauto

theorem initial18708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (meaning t m 4646) := by
  have source := ElevenTheory.theory7980 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule18708 (meaning t m 2010) (meaning t m 2230) (meaning t m 2233) (meaning t m 4646) source

theorem rule18709 (p1990 p2027 p2563 p2622 p2630 p3212 p3519 p4116 p4399 p4948 : Prop) (h : (¬ p3519) ∨ (¬ p4116) ∨ (¬ p4948) ∨ (¬ p4399) ∨ (¬ p3212) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2563) ∨ p2622) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3212) ∨ (¬ p3519) ∨ (¬ p4116) ∨ (¬ p4399) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial18709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7981 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule18709 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2622) (meaning t m 2630) (meaning t m 3212) (meaning t m 3519) (meaning t m 4116) (meaning t m 4399) (meaning t m 4948) source

theorem rule18710 (p1984 p2027 p2396 p2997 p3588 p3954 p4324 : Prop) (h : (¬ p3588) ∨ (¬ p1984) ∨ (¬ p2396) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4324) ∨ p2997) : (¬ p1984) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial18710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory7982 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18710 (meaning t m 1984) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) source

end SunPrize.SMT
