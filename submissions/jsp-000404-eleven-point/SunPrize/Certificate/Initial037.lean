import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory021
import SunPrize.Certificate.Theory022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule17218 (p1991 p2027 p2440 p2476 p2655 p2938 p3083 p4235 : Prop) (h : (¬ p1991) ∨ (¬ p3083) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p4235) ∨ (¬ p2440) ∨ p2938) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (p2938) ∨ (¬ p3083) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6490 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7)
  exact rule17218 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2476) (meaning t m 2655) (meaning t m 2938) (meaning t m 3083) (meaning t m 4235) source

theorem rule17221 (p2000 p2027 p2588 p2997 p3343 p3346 p3574 : Prop) (h : (¬ p3574) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p2000) ∨ p2997 ∨ (¬ p2588) ∨ (¬ p3343)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial17221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory6493 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7)
  exact rule17221 (meaning t m 2000) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3343) (meaning t m 3346) (meaning t m 3574) source

theorem rule17222 (p2000 p2027 p2542 p2589 p2764 p3359 p4322 p4947 : Prop) (h : p2764 ∨ (¬ p4947) ∨ (¬ p4322) ∨ (¬ p2542) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p2000) ∨ (¬ p2589)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p3359) ∨ (¬ p4322) ∨ (¬ p4947) := by
  classical
  tauto

theorem initial17222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4947)) := by
  have source := ElevenTheory.theory6494 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule17222 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2764) (meaning t m 3359) (meaning t m 4322) (meaning t m 4947) source

theorem rule17223 (p1977 p2027 p2241 p2914 p3227 p3343 p3742 p3834 : Prop) (h : (¬ p3343) ∨ p2914 ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2241) ∨ (¬ p3227) ∨ (¬ p3834) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2914) ∨ (¬ p3227) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3834) := by
  classical
  tauto

theorem initial17223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3834)) := by
  have source := ElevenTheory.theory6495 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule17223 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2914) (meaning t m 3227) (meaning t m 3343) (meaning t m 3742) (meaning t m 3834) source

theorem rule17225 (p2027 p2476 p2659 p2810 p3005 p4346 : Prop) (h : (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p4346) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial17225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory6497 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule17225 (meaning t m 2027) (meaning t m 2476) (meaning t m 2659) (meaning t m 2810) (meaning t m 3005) (meaning t m 4346) source

theorem rule17227 (p1975 p2027 p2202 p2563 p3516 p3646 p4107 p4988 : Prop) (h : (¬ p4988) ∨ (¬ p1975) ∨ (¬ p4107) ∨ (¬ p3516) ∨ p2027 ∨ p2202 ∨ (¬ p3646) ∨ (¬ p2563)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3516) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial17227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory6499 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17227 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3516) (meaning t m 3646) (meaning t m 4107) (meaning t m 4988) source

theorem rule17228 (p1975 p2027 p2299 p2499 p2911 p2922 p3008 : Prop) (h : (¬ p2499) ∨ p3008 ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2299) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2499) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (p3008) := by
  classical
  tauto

theorem initial17228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 3008) := by
  have source := ElevenTheory.theory6500 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17228 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2499) (meaning t m 2911) (meaning t m 2922) (meaning t m 3008) source

theorem rule17229 (p1985 p2027 p2192 p2210 p2699 p2870 p3758 : Prop) (h : p2699 ∨ (¬ p2210) ∨ (¬ p2870) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2870) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory6501 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17229 (meaning t m 1985) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2699) (meaning t m 2870) (meaning t m 3758) source

theorem rule17230 (p1975 p2027 p2114 p2192 p2210 p2274 p3954 : Prop) (h : p2114 ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p3954) ∨ (¬ p2192)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6502 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule17230 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 3954) source

theorem rule17231 (p1975 p2027 p2284 p2299 p2388 p3527 p4173 p4431 : Prop) (h : (¬ p2299) ∨ p2027 ∨ p2388 ∨ (¬ p2284) ∨ (¬ p3527) ∨ (¬ p1975) ∨ (¬ p4173) ∨ (¬ p4431)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2299) ∨ (p2388) ∨ (¬ p3527) ∨ (¬ p4173) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial17231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory6503 t (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17231 (meaning t m 1975) (meaning t m 2027) (meaning t m 2284) (meaning t m 2299) (meaning t m 2388) (meaning t m 3527) (meaning t m 4173) (meaning t m 4431) source

theorem rule17233 (p2000 p2027 p2299 p2579 p2588 p2766 p4348 : Prop) (h : (¬ p2299) ∨ (¬ p4348) ∨ p2766 ∨ (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2588)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2766) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6505 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17233 (meaning t m 2000) (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2766) (meaning t m 4348) source

theorem rule17237 (p1976 p2027 p2534 p2657 p3146 p3578 p4236 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p1976) ∨ (¬ p4236) ∨ p3578 ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2534) ∨ (¬ p3146)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p4236) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial17237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory6509 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17237 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 3146) (meaning t m 3578) (meaning t m 4236) (meaning t m 4256) source

theorem rule17239 (p1976 p2027 p2657 p2765 p3727 p4110 p4236 p4700 p5740 : Prop) (h : (¬ p4236) ∨ (¬ p5740) ∨ (¬ p2657) ∨ (¬ p1976) ∨ (¬ p4700) ∨ (¬ p3727) ∨ p2027 ∨ p2765 ∨ (¬ p4110)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p3727) ∨ (¬ p4110) ∨ (¬ p4236) ∨ (¬ p4700) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial17239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory6511 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 10) (m.theta 5 6)
  exact rule17239 (meaning t m 1976) (meaning t m 2027) (meaning t m 2657) (meaning t m 2765) (meaning t m 3727) (meaning t m 4110) (meaning t m 4236) (meaning t m 4700) (meaning t m 5740) source

theorem rule17240 (p1976 p2027 p3055 p3684 p4110 p4206 p4393 : Prop) (h : (¬ p1976) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p4110) ∨ p4206 ∨ (¬ p4393) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (p4206) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial17240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4206) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory6512 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 10)
  exact rule17240 (meaning t m 1976) (meaning t m 2027) (meaning t m 3055) (meaning t m 3684) (meaning t m 4110) (meaning t m 4206) (meaning t m 4393) source

theorem rule17244 (p1992 p2027 p2287 p2608 p2668 p3591 p3923 : Prop) (h : (¬ p3591) ∨ (¬ p1992) ∨ (¬ p3923) ∨ (¬ p2608) ∨ p2027 ∨ p2287 ∨ (¬ p2668)) : (¬ p1992) ∨ (p2027) ∨ (p2287) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial17244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory6516 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 6 8)
  exact rule17244 (meaning t m 1992) (meaning t m 2027) (meaning t m 2287) (meaning t m 2608) (meaning t m 2668) (meaning t m 3591) (meaning t m 3923) source

theorem rule17245 (p1976 p2027 p2765 p2881 p3365 p3553 p3572 p3872 : Prop) (h : (¬ p3572) ∨ p2765 ∨ (¬ p1976) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial17245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory6517 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule17245 (meaning t m 1976) (meaning t m 2027) (meaning t m 2765) (meaning t m 2881) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 3872) source

theorem rule17248 (p1982 p2027 p3008 p3276 p3333 p3584 p4444 : Prop) (h : (¬ p1982) ∨ (¬ p3584) ∨ p3008 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4444) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (p3008) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6520 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17248 (meaning t m 1982) (meaning t m 2027) (meaning t m 3008) (meaning t m 3276) (meaning t m 3333) (meaning t m 3584) (meaning t m 4444) source

theorem rule17249 (p1975 p2027 p2299 p2765 p2881 p2901 p3952 : Prop) (h : (¬ p2881) ∨ p2765 ∨ (¬ p2299) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2901) ∨ (¬ p3952)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial17249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6521 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17249 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2765) (meaning t m 2881) (meaning t m 2901) (meaning t m 3952) source

theorem rule17252 (p1997 p2027 p2192 p2233 p2928 p3389 p3948 p4110 : Prop) (h : (¬ p2928) ∨ p2233 ∨ (¬ p3389) ∨ (¬ p2192) ∨ (¬ p3948) ∨ (¬ p4110) ∨ (¬ p1997) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2192) ∨ (p2233) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3948) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6524 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule17252 (meaning t m 1997) (meaning t m 2027) (meaning t m 2192) (meaning t m 2233) (meaning t m 2928) (meaning t m 3389) (meaning t m 3948) (meaning t m 4110) source

theorem rule17256 (p1989 p2938 p4320 p4957 : Prop) (h : p2938 ∨ (¬ p1989) ∨ (¬ p4320) ∨ p4957) : (¬ p1989) ∨ (p2938) ∨ (¬ p4320) ∨ (p4957) := by
  classical
  tauto

theorem initial17256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4320)) ∨ (meaning t m 4957) := by
  have source := ElevenTheory.theory6528 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule17256 (meaning t m 1989) (meaning t m 2938) (meaning t m 4320) (meaning t m 4957) source

theorem rule17258 (p2001 p2027 p2373 p2406 p2437 p2545 p2928 : Prop) (h : (¬ p2437) ∨ p2545 ∨ (¬ p2373) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2001) ∨ (¬ p2928)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2928) := by
  classical
  tauto

theorem initial17258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2928)) := by
  have source := ElevenTheory.theory6530 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8)
  exact rule17258 (meaning t m 2001) (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2437) (meaning t m 2545) (meaning t m 2928) source

theorem rule17262 (p1976 p2027 p2633 p2810 p3365 p3644 p3742 : Prop) (h : (¬ p3365) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2810) ∨ p2633 ∨ (¬ p3742)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial17262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory6534 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule17262 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 2810) (meaning t m 3365) (meaning t m 3644) (meaning t m 3742) source

theorem rule17264 (p1976 p2027 p3008 p3055 p3083 p3574 p3874 : Prop) (h : (¬ p3083) ∨ p2027 ∨ (¬ p1976) ∨ p3008 ∨ (¬ p3874) ∨ (¬ p3574) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial17264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory6536 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule17264 (meaning t m 1976) (meaning t m 2027) (meaning t m 3008) (meaning t m 3055) (meaning t m 3083) (meaning t m 3574) (meaning t m 3874) source

theorem rule17265 (p1978 p2027 p2588 p2619 p2997 p3758 p4120 p4203 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p1978) ∨ (¬ p3758) ∨ (¬ p4203) ∨ (¬ p2588) ∨ p2997) : (¬ p1978) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2619) ∨ (p2997) ∨ (¬ p3758) ∨ (¬ p4120) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial17265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory6537 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule17265 (meaning t m 1978) (meaning t m 2027) (meaning t m 2588) (meaning t m 2619) (meaning t m 2997) (meaning t m 3758) (meaning t m 4120) (meaning t m 4203) source

theorem rule17268 (p1976 p2027 p2810 p3128 p3365 p3574 p4137 : Prop) (h : p2027 ∨ (¬ p3365) ∨ (¬ p2810) ∨ (¬ p4137) ∨ (¬ p3574) ∨ p3128 ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2810) ∨ (p3128) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial17268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory6540 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule17268 (meaning t m 1976) (meaning t m 2027) (meaning t m 2810) (meaning t m 3128) (meaning t m 3365) (meaning t m 3574) (meaning t m 4137) source

theorem rule17270 (p2015 p2233 p2493 p2501 p3347 : Prop) (h : (¬ p2015) ∨ p2233 ∨ (¬ p3347) ∨ p2501 ∨ (¬ p2493)) : (¬ p2015) ∨ (p2233) ∨ (¬ p2493) ∨ (p2501) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial17270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2501) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory6542 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule17270 (meaning t m 2015) (meaning t m 2233) (meaning t m 2493) (meaning t m 2501) (meaning t m 3347) source

theorem rule17271 (p1998 p2911 p2997 p4276 : Prop) (h : (¬ p1998) ∨ p2997 ∨ (¬ p2911) ∨ p4276) : (¬ p1998) ∨ (¬ p2911) ∨ (p2997) ∨ (p4276) := by
  classical
  tauto

theorem initial17271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2997) ∨ (meaning t m 4276) := by
  have source := ElevenTheory.theory6543 t (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17271 (meaning t m 1998) (meaning t m 2911) (meaning t m 2997) (meaning t m 4276) source

theorem rule17272 (p1998 p2027 p2287 p2295 p2396 p2911 p4278 : Prop) (h : p2287 ∨ (¬ p1998) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p2396) ∨ (¬ p4278)) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2911) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial17272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6544 t (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17272 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2396) (meaning t m 2911) (meaning t m 4278) source

theorem rule17273 (p1986 p2027 p2766 p3266 p3366 p3367 p4232 p5387 : Prop) (h : (¬ p3266) ∨ (¬ p1986) ∨ (¬ p3367) ∨ (¬ p3366) ∨ (¬ p5387) ∨ p2027 ∨ p2766 ∨ (¬ p4232)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4232) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial17273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory6545 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17273 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3366) (meaning t m 3367) (meaning t m 4232) (meaning t m 5387) source

theorem rule17274 (p1986 p2027 p2462 p2598 p2761 p4232 p5387 : Prop) (h : (¬ p4232) ∨ (¬ p2761) ∨ (¬ p5387) ∨ p2462 ∨ (¬ p2598) ∨ (¬ p1986) ∨ p2027) : (¬ p1986) ∨ (p2027) ∨ (p2462) ∨ (¬ p2598) ∨ (¬ p2761) ∨ (¬ p4232) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial17274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory6546 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 9) (m.theta 7 9) (m.theta 9 10)
  exact rule17274 (meaning t m 1986) (meaning t m 2027) (meaning t m 2462) (meaning t m 2598) (meaning t m 2761) (meaning t m 4232) (meaning t m 5387) source

theorem rule17276 (p1979 p2027 p2166 p2622 p2797 p3497 p4154 p4365 : Prop) (h : p2622 ∨ (¬ p4154) ∨ (¬ p2797) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p4365) ∨ (¬ p2166) ∨ (¬ p3497)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2166) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3497) ∨ (¬ p4154) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial17276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory6548 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule17276 (meaning t m 1979) (meaning t m 2027) (meaning t m 2166) (meaning t m 2622) (meaning t m 2797) (meaning t m 3497) (meaning t m 4154) (meaning t m 4365) source

theorem rule17277 (p1998 p2027 p2264 p2622 p2797 p2807 p2963 : Prop) (h : (¬ p1998) ∨ p2622 ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2797) ∨ (¬ p2963)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial17277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory6549 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule17277 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2622) (meaning t m 2797) (meaning t m 2807) (meaning t m 2963) source

theorem rule17278 (p1992 p2027 p2476 p2534 p3146 p3363 p3578 p3585 : Prop) (h : p2027 ∨ p3578 ∨ (¬ p2534) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p1992) ∨ (¬ p2476) ∨ (¬ p3146)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3363) ∨ (p3578) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3363)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6550 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17278 (meaning t m 1992) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 3146) (meaning t m 3363) (meaning t m 3578) (meaning t m 3585) source

theorem rule17282 (p1990 p2027 p2553 p2611 p2651 p3097 p3422 p4117 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p3097) ∨ p2027 ∨ p2611 ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2553) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p3422) ∨ (¬ p4117) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial17282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory6554 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17282 (meaning t m 1990) (meaning t m 2027) (meaning t m 2553) (meaning t m 2611) (meaning t m 2651) (meaning t m 3097) (meaning t m 3422) (meaning t m 4117) (meaning t m 4343) source

theorem rule17283 (p2230 p2441 p3389 : Prop) (h : (¬ p3389) ∨ (¬ p2441) ∨ p2230) : (p2230) ∨ (¬ p2441) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial17283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2230) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory6555 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule17283 (meaning t m 2230) (meaning t m 2441) (meaning t m 3389) source

theorem rule17284 (p1986 p2027 p2579 p2588 p2997 p3389 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p2579)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3389) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial17284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory6556 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule17284 (meaning t m 1986) (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) (meaning t m 3389) (meaning t m 3876) source

theorem rule17285 (p1996 p2027 p2611 p2696 p2743 p3527 p3553 p3687 : Prop) (h : (¬ p3527) ∨ p2611 ∨ (¬ p1996) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2696) ∨ (¬ p3687) ∨ (¬ p2743)) : (¬ p1996) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p3687) := by
  classical
  tauto

theorem initial17285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3687)) := by
  have source := ElevenTheory.theory6557 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule17285 (meaning t m 1996) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 3527) (meaning t m 3553) (meaning t m 3687) source

theorem rule17287 (p1990 p2027 p2132 p2284 p2611 p3105 p4208 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p4208) ∨ (¬ p2284) ∨ (¬ p1990) ∨ (¬ p2132) ∨ (¬ p3105)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (p2611) ∨ (¬ p3105) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial17287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory6559 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule17287 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2284) (meaning t m 2611) (meaning t m 3105) (meaning t m 4208) source

theorem rule17288 (p1994 p2027 p2573 p2589 p2938 p3574 p4235 : Prop) (h : (¬ p1994) ∨ (¬ p4235) ∨ p2027 ∨ p2938 ∨ (¬ p2589) ∨ (¬ p2573) ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (p2938) ∨ (¬ p3574) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6560 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule17288 (meaning t m 1994) (meaning t m 2027) (meaning t m 2573) (meaning t m 2589) (meaning t m 2938) (meaning t m 3574) (meaning t m 4235) source

theorem rule17289 (p1983 p2027 p2611 p2696 p2707 p2743 p3434 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p3434) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2707) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) := by
  classical
  tauto

theorem initial17289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3434)) := by
  have source := ElevenTheory.theory6561 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule17289 (meaning t m 1983) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2707) (meaning t m 2743) (meaning t m 3434) source

theorem rule17290 (p2008 p2611 p2696 p4782 : Prop) (h : p2611 ∨ (¬ p2008) ∨ (¬ p2696) ∨ p4782) : (¬ p2008) ∨ (p2611) ∨ (¬ p2696) ∨ (p4782) := by
  classical
  tauto

theorem initial17290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 4782) := by
  have source := ElevenTheory.theory6562 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7)
  exact rule17290 (meaning t m 2008) (meaning t m 2611) (meaning t m 2696) (meaning t m 4782) source

theorem rule17292 (p1995 p2027 p2313 p2386 p2499 p2764 p4107 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p2386) ∨ (¬ p2313) ∨ (¬ p2499) ∨ (¬ p4107) ∨ (¬ p1995) ∨ p2764 ∨ p2027) : (¬ p1995) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6564 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17292 (meaning t m 1995) (meaning t m 2027) (meaning t m 2313) (meaning t m 2386) (meaning t m 2499) (meaning t m 2764) (meaning t m 4107) (meaning t m 4381) source

theorem rule17293 (p1990 p2027 p2202 p2573 p2589 p3564 p3744 : Prop) (h : (¬ p3564) ∨ (¬ p1990) ∨ p2202 ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p2589)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3564) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial17293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory6565 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule17293 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2573) (meaning t m 2589) (meaning t m 3564) (meaning t m 3744) source

theorem rule17294 (p1988 p2027 p2608 p2699 p2839 p3105 p3680 : Prop) (h : (¬ p2839) ∨ (¬ p3680) ∨ p2699 ∨ (¬ p1988) ∨ (¬ p3105) ∨ (¬ p2608) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial17294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory6566 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule17294 (meaning t m 1988) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 3105) (meaning t m 3680) source

theorem rule17295 (p1994 p2027 p2608 p2699 p2727 p2829 p4154 p4328 : Prop) (h : (¬ p2829) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p1994) ∨ (¬ p4154) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p4328)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2829) ∨ (¬ p4154) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial17295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory6567 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6)
  exact rule17295 (meaning t m 1994) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2727) (meaning t m 2829) (meaning t m 4154) (meaning t m 4328) source

theorem rule17296 (p1975 p2027 p2132 p2299 p2611 p2881 p2891 p4418 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2891) ∨ (¬ p2881) ∨ (¬ p4418) ∨ (¬ p2132) ∨ (¬ p1975) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2299) ∨ (p2611) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial17296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory6568 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17296 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2299) (meaning t m 2611) (meaning t m 2881) (meaning t m 2891) (meaning t m 4418) source

theorem rule17299 (p1994 p2027 p2331 p2355 p2727 p3414 p4154 : Prop) (h : (¬ p2727) ∨ (¬ p1994) ∨ (¬ p3414) ∨ p2355 ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2331)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2331) ∨ (p2355) ∨ (¬ p2727) ∨ (¬ p3414) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial17299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory6571 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule17299 (meaning t m 1994) (meaning t m 2027) (meaning t m 2331) (meaning t m 2355) (meaning t m 2727) (meaning t m 3414) (meaning t m 4154) source

theorem rule17301 (p2027 p2132 p2737 p2780 p3583 p4842 : Prop) (h : (¬ p2132) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4842) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial17301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory6573 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6)
  exact rule17301 (meaning t m 2027) (meaning t m 2132) (meaning t m 2737) (meaning t m 2780) (meaning t m 3583) (meaning t m 4842) source

theorem rule17302 (p1988 p2027 p2295 p2323 p2331 p2396 p2761 : Prop) (h : p2323 ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2295)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial17302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory6574 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17302 (meaning t m 1988) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2331) (meaning t m 2396) (meaning t m 2761) source

theorem rule17303 (p1982 p2027 p2192 p2873 p3125 p3461 p4444 : Prop) (h : (¬ p2192) ∨ (¬ p4444) ∨ (¬ p3461) ∨ p2873 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3125)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2192) ∨ (p2873) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6575 t (m.theta 1 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17303 (meaning t m 1982) (meaning t m 2027) (meaning t m 2192) (meaning t m 2873) (meaning t m 3125) (meaning t m 3461) (meaning t m 4444) source

theorem rule17304 (p1975 p2027 p2274 p2641 p2668 p2688 p3989 : Prop) (h : (¬ p2641) ∨ (¬ p1975) ∨ (¬ p2668) ∨ p2027 ∨ p2688 ∨ (¬ p2274) ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (p2688) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6576 t (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17304 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2641) (meaning t m 2668) (meaning t m 2688) (meaning t m 3989) source

theorem rule17305 (p1984 p2027 p2202 p2563 p3583 p3758 p3954 : Prop) (h : (¬ p2563) ∨ (¬ p3954) ∨ p2027 ∨ p2202 ∨ (¬ p3583) ∨ (¬ p1984) ∨ (¬ p3758)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6577 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule17305 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3583) (meaning t m 3758) (meaning t m 3954) source

theorem rule17307 (p1983 p2027 p2148 p2156 p2901 p3246 p3952 : Prop) (h : p2148 ∨ (¬ p3246) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2901) ∨ (¬ p2156)) : (¬ p1983) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial17307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6579 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule17307 (meaning t m 1983) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2901) (meaning t m 3246) (meaning t m 3952) source

theorem rule17308 (p2020 p2027 p2202 p2220 p2563 p3646 p3969 : Prop) (h : p2202 ∨ (¬ p2020) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3969)) : (¬ p2020) ∨ (p2027) ∨ (p2202) ∨ (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial17308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory6580 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule17308 (meaning t m 2020) (meaning t m 2027) (meaning t m 2202) (meaning t m 2220) (meaning t m 2563) (meaning t m 3646) (meaning t m 3969) source

theorem rule17309 (p1984 p2027 p2417 p2633 p3644 p3817 p4366 : Prop) (h : (¬ p2417) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p1984) ∨ p2633 ∨ (¬ p3817) ∨ (¬ p4366)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p3644) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial17309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory6581 t (m.theta 0 1) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17309 (meaning t m 1984) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 3644) (meaning t m 3817) (meaning t m 4366) source

theorem rule17311 (p1984 p2027 p2766 p3193 p3266 p3452 p4425 : Prop) (h : (¬ p3266) ∨ p2766 ∨ (¬ p3452) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p4425)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3193) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial17311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory6583 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17311 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3193) (meaning t m 3266) (meaning t m 3452) (meaning t m 4425) source

theorem rule17313 (p2009 p2027 p2622 p2743 p3537 p3609 p3857 : Prop) (h : (¬ p2009) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2743) ∨ p2622 ∨ (¬ p3609) ∨ (¬ p3537)) : (¬ p2009) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial17313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory6585 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 8 9)
  exact rule17313 (meaning t m 2009) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3537) (meaning t m 3609) (meaning t m 3857) source

theorem rule17314 (p1979 p2027 p2766 p3497 p4019 p4340 p5568 : Prop) (h : (¬ p1979) ∨ (¬ p4340) ∨ (¬ p3497) ∨ (¬ p4019) ∨ p2027 ∨ (¬ p5568) ∨ p2766) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p3497) ∨ (¬ p4019) ∨ (¬ p4340) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial17314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory6586 t (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17314 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 3497) (meaning t m 4019) (meaning t m 4340) (meaning t m 5568) source

theorem rule17316 (p1975 p2027 p2148 p2264 p2299 p2962 p3654 p4037 p4156 : Prop) (h : p2148 ∨ (¬ p2299) ∨ (¬ p1975) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3654) ∨ (¬ p2962) ∨ (¬ p4156) ∨ (¬ p4037)) : (¬ p1975) ∨ (p2027) ∨ (p2148) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4037) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial17316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory6588 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule17316 (meaning t m 1975) (meaning t m 2027) (meaning t m 2148) (meaning t m 2264) (meaning t m 2299) (meaning t m 2962) (meaning t m 3654) (meaning t m 4037) (meaning t m 4156) source

theorem rule17318 (p1975 p2027 p2299 p2622 p2881 p3365 p3471 p4344 : Prop) (h : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p4344) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p1975) ∨ (¬ p3471) ∨ p2622) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial17318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory6590 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17318 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2622) (meaning t m 2881) (meaning t m 3365) (meaning t m 3471) (meaning t m 4344) source

theorem rule17319 (p1984 p2027 p2202 p2563 p3583 p3872 p3954 p4244 : Prop) (h : (¬ p2563) ∨ (¬ p3954) ∨ p2027 ∨ p2202 ∨ (¬ p1984) ∨ (¬ p3872) ∨ (¬ p3583) ∨ (¬ p4244)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3583) ∨ (¬ p3872) ∨ (¬ p3954) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial17319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6591 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17319 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3583) (meaning t m 3872) (meaning t m 3954) (meaning t m 4244) source

theorem rule17320 (p2020 p2027 p2148 p2156 p3156 p3952 p3969 : Prop) (h : (¬ p2020) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3952) ∨ (¬ p3969) ∨ p2148) : (¬ p2020) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial17320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory6592 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule17320 (meaning t m 2020) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 3156) (meaning t m 3952) (meaning t m 3969) source

theorem rule17321 (p1979 p2027 p2098 p2138 p2765 p3497 p3758 p4188 : Prop) (h : p2027 ∨ (¬ p3758) ∨ (¬ p2138) ∨ (¬ p4188) ∨ p2765 ∨ (¬ p1979) ∨ (¬ p3497) ∨ (¬ p2098)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (p2765) ∨ (¬ p3497) ∨ (¬ p3758) ∨ (¬ p4188) := by
  classical
  tauto

theorem initial17321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4188)) := by
  have source := ElevenTheory.theory6593 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17321 (meaning t m 1979) (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 2765) (meaning t m 3497) (meaning t m 3758) (meaning t m 4188) source

theorem rule17324 (p1998 p2027 p2177 p2323 p2449 p2807 p4107 : Prop) (h : (¬ p4107) ∨ p2323 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2807) ∨ (¬ p2449)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial17324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6596 t (m.theta 0 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17324 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2323) (meaning t m 2449) (meaning t m 2807) (meaning t m 4107) source

theorem rule17327 (p1976 p2027 p2588 p2997 p3055 p3367 p3688 p4342 : Prop) (h : (¬ p4342) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial17327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory6599 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule17327 (meaning t m 1976) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3055) (meaning t m 3367) (meaning t m 3688) (meaning t m 4342) source

theorem rule17329 (p1984 p2027 p2766 p3688 p3954 p4347 p4358 : Prop) (h : (¬ p4347) ∨ (¬ p1984) ∨ p2766 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p4358)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial17329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory6601 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17329 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3688) (meaning t m 3954) (meaning t m 4347) (meaning t m 4358) source

theorem rule17330 (p3051 p4192 p4323 p4380 : Prop) (h : (¬ p4380) ∨ (¬ p3051) ∨ (¬ p4323) ∨ (¬ p4192)) : (¬ p3051) ∨ (¬ p4192) ∨ (¬ p4323) ∨ (¬ p4380) := by
  classical
  tauto

theorem initial17330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4323)) ∨ (¬ (meaning t m 4380)) := by
  have source := ElevenTheory.theory6602 (m.theta 0 5) (m.theta 0 9) (m.theta 5 7) (m.theta 5 9)
  exact rule17330 (meaning t m 3051) (meaning t m 4192) (meaning t m 4323) (meaning t m 4380) source

theorem rule17333 (p1988 p2027 p2202 p2563 p3212 p3461 p3646 p5045 : Prop) (h : (¬ p5045) ∨ (¬ p1988) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3461) ∨ p2202 ∨ (¬ p3212) ∨ (¬ p2563)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3212) ∨ (¬ p3461) ∨ (¬ p3646) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial17333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory6605 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule17333 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3212) (meaning t m 3461) (meaning t m 3646) (meaning t m 5045) source

theorem rule17337 (p1995 p2027 p2202 p2509 p2534 p3609 p3684 p4354 : Prop) (h : p2027 ∨ (¬ p2509) ∨ p2202 ∨ (¬ p1995) ∨ (¬ p3684) ∨ (¬ p3609) ∨ (¬ p2534) ∨ (¬ p4354)) : (¬ p1995) ∨ (p2027) ∨ (p2202) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3609) ∨ (¬ p3684) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial17337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory6609 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule17337 (meaning t m 1995) (meaning t m 2027) (meaning t m 2202) (meaning t m 2509) (meaning t m 2534) (meaning t m 3609) (meaning t m 3684) (meaning t m 4354) source

theorem rule17338 (p1975 p2027 p2114 p2230 p2274 p2563 p3367 p3759 : Prop) (h : (¬ p3367) ∨ p2027 ∨ (¬ p1975) ∨ p2114 ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p3759) ∨ (¬ p2563)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6610 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule17338 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 3367) (meaning t m 3759) source

theorem rule17339 (p1993 p2027 p2088 p2202 p2427 p3556 p4118 p4238 : Prop) (h : (¬ p4118) ∨ (¬ p1993) ∨ p2027 ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2088) ∨ (¬ p4238) ∨ (¬ p3556)) : (¬ p1993) ∨ (p2027) ∨ (¬ p2088) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4118) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial17339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory6611 t (m.theta 0 5) (m.theta 0 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 8 9)
  exact rule17339 (meaning t m 1993) (meaning t m 2027) (meaning t m 2088) (meaning t m 2202) (meaning t m 2427) (meaning t m 3556) (meaning t m 4118) (meaning t m 4238) source

theorem rule17341 (p1998 p2027 p2177 p2202 p2563 p2901 p3952 p4140 : Prop) (h : (¬ p3952) ∨ (¬ p2563) ∨ p2202 ∨ p2027 ∨ (¬ p2901) ∨ (¬ p4140) ∨ (¬ p1998) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial17341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory6613 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17341 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2563) (meaning t m 2901) (meaning t m 3952) (meaning t m 4140) source

theorem rule17343 (p1991 p2027 p2202 p2440 p2797 p2810 p2963 : Prop) (h : p2202 ∨ (¬ p1991) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2810) ∨ (¬ p2797)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial17343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory6615 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule17343 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2797) (meaning t m 2810) (meaning t m 2963) source

theorem rule17344 (p1998 p2027 p2177 p2307 p2622 p2743 p2779 p2829 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2829) ∨ (¬ p2779) ∨ (¬ p2743)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial17344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory6616 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17344 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2622) (meaning t m 2743) (meaning t m 2779) (meaning t m 2829) source

theorem rule17345 (p1998 p2027 p2122 p2177 p2622 p2743 p2839 p3985 : Prop) (h : (¬ p2177) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3985) ∨ p2622 ∨ (¬ p2122)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial17345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory6617 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17345 (meaning t m 1998) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3985) source

theorem rule17346 (p1998 p2027 p2177 p2688 p2891 p4129 p4260 p4365 : Prop) (h : (¬ p4129) ∨ (¬ p4365) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p4260) ∨ (¬ p2891) ∨ p2688) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2688) ∨ (¬ p2891) ∨ (¬ p4129) ∨ (¬ p4260) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial17346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory6618 t (m.theta 1 3) (m.theta 1 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule17346 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2688) (meaning t m 2891) (meaning t m 4129) (meaning t m 4260) (meaning t m 4365) source

theorem rule17347 (p1976 p2027 p2459 p2534 p2633 p3055 p3874 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p3874) ∨ (¬ p3055) ∨ (¬ p2534) ∨ (¬ p2459) ∨ p2633) : (¬ p1976) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3055) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial17347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory6619 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17347 (meaning t m 1976) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 3055) (meaning t m 3874) source

theorem rule17348 (p1994 p2027 p2528 p2651 p3172 p3498 p4118 : Prop) (h : p2027 ∨ (¬ p1994) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p2528) ∨ p3498) : (¬ p1994) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (p3498) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory6620 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule17348 (meaning t m 1994) (meaning t m 2027) (meaning t m 2528) (meaning t m 2651) (meaning t m 3172) (meaning t m 3498) (meaning t m 4118) source

theorem rule17350 (p1984 p2027 p2191 p2373 p2765 p3452 p4110 p4202 : Prop) (h : p2027 ∨ (¬ p3452) ∨ (¬ p1984) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p4202) ∨ (¬ p2191) ∨ (¬ p2373)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial17350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory6622 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17350 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2373) (meaning t m 2765) (meaning t m 3452) (meaning t m 4110) (meaning t m 4202) source

theorem rule17352 (p1990 p2027 p2284 p2622 p2946 p3005 p3172 : Prop) (h : (¬ p3172) ∨ p2622 ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p1990) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2622) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3172) := by
  classical
  tauto

theorem initial17352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) := by
  have source := ElevenTheory.theory6624 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule17352 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2622) (meaning t m 2946) (meaning t m 3005) (meaning t m 3172) source

theorem rule17353 (p1998 p2027 p2114 p2737 p2881 p2951 p3051 p3136 : Prop) (h : (¬ p2881) ∨ (¬ p3136) ∨ p2114 ∨ (¬ p1998) ∨ (¬ p2951) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2737)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial17353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory6625 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17353 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2881) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) source

theorem rule17355 (p1998 p2027 p2114 p2707 p2881 p3516 p3577 p3690 : Prop) (h : (¬ p3577) ∨ p2114 ∨ (¬ p2707) ∨ (¬ p3516) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2707) ∨ (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3577) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial17355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory6627 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17355 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2707) (meaning t m 2881) (meaning t m 3516) (meaning t m 3577) (meaning t m 3690) source

theorem rule17356 (p1998 p2027 p2177 p2319 p2622 p2797 p3516 p3567 p4107 : Prop) (h : (¬ p1998) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p2319) ∨ (¬ p2797) ∨ p2622 ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2319) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial17356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2319)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6628 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17356 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2319) (meaning t m 2622) (meaning t m 2797) (meaning t m 3516) (meaning t m 3567) (meaning t m 4107) source

theorem rule17357 (p1998 p2027 p2622 p2881 p2951 p3136 p3516 p3690 p4988 : Prop) (h : (¬ p2951) ∨ (¬ p2881) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4988) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p3136) ∨ p2622) : (¬ p1998) ∨ (p2027) ∨ (p2622) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial17357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory6629 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17357 (meaning t m 1998) (meaning t m 2027) (meaning t m 2622) (meaning t m 2881) (meaning t m 2951) (meaning t m 3136) (meaning t m 3516) (meaning t m 3690) (meaning t m 4988) source

theorem rule17359 (p1994 p2027 p2417 p2651 p2914 p3037 p3172 p3817 p4044 : Prop) (h : (¬ p3172) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2651) ∨ (¬ p2417) ∨ p2914 ∨ (¬ p4044) ∨ (¬ p3817) ∨ (¬ p3037)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (p2914) ∨ (¬ p3037) ∨ (¬ p3172) ∨ (¬ p3817) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial17359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory6631 t (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9)
  exact rule17359 (meaning t m 1994) (meaning t m 2027) (meaning t m 2417) (meaning t m 2651) (meaning t m 2914) (meaning t m 3037) (meaning t m 3172) (meaning t m 3817) (meaning t m 4044) source

theorem rule17363 (p1998 p2027 p2144 p2156 p2611 p2870 p2881 p3758 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2144) ∨ (¬ p2881) ∨ (¬ p2870) ∨ (¬ p2156) ∨ (¬ p3758)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory6635 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule17363 (meaning t m 1998) (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2611) (meaning t m 2870) (meaning t m 2881) (meaning t m 3758) source

theorem rule17364 (p1981 p2027 p2132 p2187 p2753 p2842 p2860 p3585 : Prop) (h : p2842 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p1981) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2753) ∨ (p2842) ∨ (¬ p2860) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6636 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule17364 (meaning t m 1981) (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2753) (meaning t m 2842) (meaning t m 2860) (meaning t m 3585) source

theorem rule17367 (p1994 p2027 p2202 p2427 p2651 p2952 p4320 : Prop) (h : (¬ p2651) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p4320) ∨ (¬ p2427) ∨ p2202) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial17367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory6639 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule17367 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2651) (meaning t m 2952) (meaning t m 4320) source

theorem rule17368 (p2009 p2027 p2528 p3008 p3584 p3641 p3857 : Prop) (h : (¬ p3857) ∨ (¬ p2009) ∨ p3008 ∨ p2027 ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p2528)) : (¬ p2009) ∨ (p2027) ∨ (¬ p2528) ∨ (p3008) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial17368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory6640 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule17368 (meaning t m 2009) (meaning t m 2027) (meaning t m 2528) (meaning t m 3008) (meaning t m 3584) (meaning t m 3641) (meaning t m 3857) source

theorem rule17377 (p1983 p2027 p2341 p2688 p3027 p3246 p3570 p4066 : Prop) (h : (¬ p3027) ∨ p2688 ∨ (¬ p4066) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p1983) ∨ (¬ p3570) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2341) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial17377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory6649 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17377 (meaning t m 1983) (meaning t m 2027) (meaning t m 2341) (meaning t m 2688) (meaning t m 3027) (meaning t m 3246) (meaning t m 3570) (meaning t m 4066) source

theorem rule17378 (p1994 p2027 p2651 p2764 p2963 p4037 p4191 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4191) ∨ p2764 ∨ (¬ p4037) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial17378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6650 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule17378 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 2963) (meaning t m 4037) (meaning t m 4191) source

theorem rule17381 (p1985 p2027 p2114 p3399 p3527 p3570 p3954 : Prop) (h : p2114 ∨ (¬ p1985) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p3527)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6653 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17381 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) (meaning t m 3954) source

theorem rule17382 (p1987 p2027 p2579 p2662 p2766 p2810 p3956 p4347 : Prop) (h : (¬ p1987) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p2579) ∨ p2766 ∨ (¬ p2662) ∨ p2027 ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial17382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6654 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17382 (meaning t m 1987) (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2766) (meaning t m 2810) (meaning t m 3956) (meaning t m 4347) source

theorem rule17383 (p1988 p2027 p2341 p2761 p3246 p3360 p3570 : Prop) (h : p3360 ∨ (¬ p2341) ∨ (¬ p2761) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p3570)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2761) ∨ (¬ p3246) ∨ (p3360) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial17383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3246)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory6655 t (m.theta 0 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule17383 (meaning t m 1988) (meaning t m 2027) (meaning t m 2341) (meaning t m 2761) (meaning t m 3246) (meaning t m 3360) (meaning t m 3570) source

theorem rule17386 (p1990 p2027 p2230 p2563 p2622 p2743 p3367 p3759 : Prop) (h : (¬ p1990) ∨ (¬ p2230) ∨ (¬ p2743) ∨ p2622 ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6658 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule17386 (meaning t m 1990) (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3759) source

theorem rule17387 (p1982 p2027 p2137 p2220 p2622 p2743 p2839 p3146 : Prop) (h : (¬ p2839) ∨ (¬ p2743) ∨ p2027 ∨ p2622 ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p1982) ∨ (¬ p2137)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial17387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory6659 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule17387 (meaning t m 1982) (meaning t m 2027) (meaning t m 2137) (meaning t m 2220) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3146) source

theorem rule17388 (p1975 p2027 p2553 p2573 p2622 p2743 p3367 p3759 : Prop) (h : p2027 ∨ (¬ p2743) ∨ (¬ p1975) ∨ (¬ p2573) ∨ p2622 ∨ (¬ p2553) ∨ (¬ p3759) ∨ (¬ p3367)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6660 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule17388 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3759) source

theorem rule17390 (p1990 p2027 p2137 p2341 p2622 p2743 p2839 p3570 p4204 p4988 : Prop) (h : (¬ p2839) ∨ p2622 ∨ (¬ p2137) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2743) ∨ (¬ p1990) ∨ (¬ p4204) ∨ (¬ p3570)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2341) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial17390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory6662 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule17390 (meaning t m 1990) (meaning t m 2027) (meaning t m 2137) (meaning t m 2341) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3570) (meaning t m 4204) (meaning t m 4988) source

theorem rule17391 (p2011 p2027 p2323 p2449 p2761 p2807 p4322 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p4322) ∨ (¬ p2011) ∨ (¬ p2761)) : (¬ p2011) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial17391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory6663 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule17391 (meaning t m 2011) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 4322) source

theorem rule17392 (p1976 p2780 p3437 p4472 : Prop) (h : p4472 ∨ (¬ p1976) ∨ (¬ p2780) ∨ p3437) : (¬ p1976) ∨ (¬ p2780) ∨ (p3437) ∨ (p4472) := by
  classical
  tauto

theorem initial17392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3437) ∨ (meaning t m 4472) := by
  have source := ElevenTheory.theory6664 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7)
  exact rule17392 (meaning t m 1976) (meaning t m 2780) (meaning t m 3437) (meaning t m 4472) source

theorem rule17393 (p1984 p2027 p2462 p3688 p3822 p3954 p4107 : Prop) (h : (¬ p3822) ∨ p2027 ∨ p2462 ∨ (¬ p3954) ∨ (¬ p3688) ∨ (¬ p1984) ∨ (¬ p4107)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial17393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6665 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17393 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) (meaning t m 4107) source

theorem rule17397 (p1990 p2027 p2284 p3360 p3516 p3690 p4320 : Prop) (h : p3360 ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4320) ∨ (¬ p3690) ∨ (¬ p1990) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p3360) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial17397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory6669 t (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule17397 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 3360) (meaning t m 3516) (meaning t m 3690) (meaning t m 4320) source

theorem rule17398 (p1990 p2027 p2563 p2622 p2743 p2850 p3367 : Prop) (h : (¬ p2743) ∨ (¬ p1990) ∨ p2622 ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2563) ∨ (¬ p2850)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2850) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial17398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory6670 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule17398 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2622) (meaning t m 2743) (meaning t m 2850) (meaning t m 3367) source

theorem rule17407 (p1982 p2027 p2323 p2459 p2881 p2901 p2946 : Prop) (h : p2323 ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial17407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory6679 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17407 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2459) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) source

theorem rule17409 (p1982 p2027 p2323 p2958 p3051 p3146 p3156 p4320 : Prop) (h : p2323 ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial17409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory6681 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule17409 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2958) (meaning t m 3051) (meaning t m 3146) (meaning t m 3156) (meaning t m 4320) source

theorem rule17412 (p1975 p2027 p2274 p2699 p3093 p3319 p3744 : Prop) (h : (¬ p3093) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p1975) ∨ p2699 ∨ (¬ p2274) ∨ (¬ p3744)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial17412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory6684 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule17412 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 3744) source

theorem rule17413 (p1990 p2027 p2202 p2307 p2440 p2578 p3016 p3097 : Prop) (h : p2202 ∨ (¬ p2307) ∨ (¬ p3016) ∨ (¬ p1990) ∨ (¬ p2578) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial17413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory6685 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17413 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2307) (meaning t m 2440) (meaning t m 2578) (meaning t m 3016) (meaning t m 3097) source

theorem rule17414 (p1986 p2027 p2534 p2766 p3016 p3584 p4256 : Prop) (h : (¬ p2534) ∨ (¬ p3016) ∨ p2027 ∨ p2766 ∨ (¬ p4256) ∨ (¬ p1986) ∨ (¬ p3584)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3016) ∨ (¬ p3584) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial17414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory6686 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule17414 (meaning t m 1986) (meaning t m 2027) (meaning t m 2534) (meaning t m 2766) (meaning t m 3016) (meaning t m 3584) (meaning t m 4256) source

theorem rule17415 (p1975 p2027 p2307 p2387 p2633 p3941 p5580 : Prop) (h : (¬ p3941) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p1975) ∨ (¬ p5580) ∨ p2633) : (¬ p1975) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (p2633) ∨ (¬ p3941) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial17415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory6687 t (m.theta 0 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule17415 (meaning t m 1975) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2633) (meaning t m 3941) (meaning t m 5580) source

theorem rule17416 (p1991 p2027 p2459 p2534 p2633 p2657 p4256 : Prop) (h : (¬ p1991) ∨ p2633 ∨ (¬ p2534) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2459)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial17416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory6688 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17416 (meaning t m 1991) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 2657) (meaning t m 4256) source

theorem rule17417 (p1991 p2027 p2177 p2657 p2997 p3644 p3742 : Prop) (h : (¬ p3644) ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2027 ∨ p2997 ∨ (¬ p3742) ∨ (¬ p2177)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2657) ∨ (p2997) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial17417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory6689 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17417 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2657) (meaning t m 2997) (meaning t m 3644) (meaning t m 3742) source

theorem rule17418 (p1992 p2027 p2462 p2608 p2761 p3834 p4321 : Prop) (h : (¬ p2608) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p3834) ∨ p2462 ∨ (¬ p2761)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3834) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial17418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory6690 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule17418 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2608) (meaning t m 2761) (meaning t m 3834) (meaning t m 4321) source

theorem rule17419 (p1975 p2027 p2122 p2132 p2699 p2829 p3583 p3589 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p1975) ∨ (¬ p2132) ∨ (¬ p2122) ∨ (¬ p3583) ∨ (¬ p2829) ∨ (¬ p3589)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (p2699) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial17419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory6691 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule17419 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2132) (meaning t m 2699) (meaning t m 2829) (meaning t m 3583) (meaning t m 3589) source

theorem rule17420 (p1987 p2027 p2699 p2810 p3707 p3830 p5170 p5284 : Prop) (h : (¬ p1987) ∨ (¬ p3707) ∨ p2699 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p5170) ∨ (¬ p3830) ∨ (¬ p5284)) : (¬ p1987) ∨ (p2027) ∨ (p2699) ∨ (¬ p2810) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p5170) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial17420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 5170)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory6692 t (m.theta 0 1) (m.theta 1 9) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule17420 (meaning t m 1987) (meaning t m 2027) (meaning t m 2699) (meaning t m 2810) (meaning t m 3707) (meaning t m 3830) (meaning t m 5170) (meaning t m 5284) source

theorem rule17421 (p1986 p2027 p2132 p2493 p2611 p3541 p3583 p3584 : Prop) (h : (¬ p3584) ∨ p2611 ∨ p2027 ∨ (¬ p1986) ∨ (¬ p2132) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p2493)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2493) ∨ (p2611) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial17421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory6693 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule17421 (meaning t m 1986) (meaning t m 2027) (meaning t m 2132) (meaning t m 2493) (meaning t m 2611) (meaning t m 3541) (meaning t m 3583) (meaning t m 3584) source

theorem rule17423 (p1987 p2027 p2737 p2911 p2914 p3551 p3588 p3959 : Prop) (h : (¬ p3959) ∨ p2914 ∨ (¬ p2737) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p3588)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial17423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory6695 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule17423 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2911) (meaning t m 2914) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) source

theorem rule17424 (p1975 p2027 p2192 p2274 p2388 p3115 p3645 p4032 : Prop) (h : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3115) ∨ (¬ p2274) ∨ (¬ p4032) ∨ p2027 ∨ (¬ p1975) ∨ p2388) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (p2388) ∨ (¬ p3115) ∨ (¬ p3645) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial17424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory6696 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule17424 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2274) (meaning t m 2388) (meaning t m 3115) (meaning t m 3645) (meaning t m 4032) source

theorem rule17425 (p2010 p2027 p2132 p2611 p3201 p3367 p3583 : Prop) (h : (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p2010) ∨ (¬ p2132) ∨ p2611 ∨ p2027) : (¬ p2010) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial17425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory6697 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7)
  exact rule17425 (meaning t m 2010) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 3201) (meaning t m 3367) (meaning t m 3583) source

theorem rule17426 (p1998 p2027 p2132 p2699 p2707 p2717 p3583 p3589 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2699 ∨ (¬ p2717) ∨ (¬ p2132) ∨ (¬ p3589) ∨ (¬ p3583) ∨ (¬ p2707)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3583) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial17426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory6698 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8)
  exact rule17426 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) (meaning t m 3583) (meaning t m 3589) source

theorem rule17428 (p2002 p2027 p2132 p2699 p3309 p3583 p3589 p3822 p4869 : Prop) (h : (¬ p3583) ∨ p2699 ∨ p2027 ∨ (¬ p3309) ∨ (¬ p4869) ∨ (¬ p2132) ∨ (¬ p2002) ∨ (¬ p3822) ∨ (¬ p3589)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2132) ∨ (p2699) ∨ (¬ p3309) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p3822) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial17428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory6700 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule17428 (meaning t m 2002) (meaning t m 2027) (meaning t m 2132) (meaning t m 2699) (meaning t m 3309) (meaning t m 3583) (meaning t m 3589) (meaning t m 3822) (meaning t m 4869) source

theorem rule17429 (p1995 p2027 p2299 p2633 p2928 p3791 p5503 : Prop) (h : (¬ p2928) ∨ (¬ p3791) ∨ p2027 ∨ (¬ p1995) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p5503)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3791) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial17429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory6701 t (m.theta 1 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule17429 (meaning t m 1995) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2928) (meaning t m 3791) (meaning t m 5503) source

theorem rule17431 (p1990 p2027 p2166 p2210 p2284 p2699 p3497 : Prop) (h : p2699 ∨ (¬ p2166) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p1990) ∨ (¬ p2284) ∨ (¬ p2210)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial17431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory6703 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17431 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2284) (meaning t m 2699) (meaning t m 3497) source

theorem rule17432 (p1991 p2027 p2579 p2655 p2764 p3016 p3359 p4022 p4191 : Prop) (h : (¬ p3359) ∨ (¬ p1991) ∨ (¬ p4022) ∨ p2764 ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p4191)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (p2764) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial17432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6704 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule17432 (meaning t m 1991) (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2764) (meaning t m 3016) (meaning t m 3359) (meaning t m 4022) (meaning t m 4191) source

theorem rule17433 (p2001 p2027 p2202 p2440 p2528 p3083 p3692 : Prop) (h : (¬ p2440) ∨ p2202 ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2001) ∨ (¬ p2528) ∨ (¬ p3083)) : (¬ p2001) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial17433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory6705 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17433 (meaning t m 2001) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2528) (meaning t m 3083) (meaning t m 3692) source

theorem rule17437 (p2000 p2027 p2437 p2764 p3359 p3540 p4425 : Prop) (h : (¬ p2000) ∨ (¬ p2437) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p3359) ∨ (¬ p4425) ∨ p2764) : (¬ p2000) ∨ (p2027) ∨ (¬ p2437) ∨ (p2764) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial17437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory6709 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 9 10)
  exact rule17437 (meaning t m 2000) (meaning t m 2027) (meaning t m 2437) (meaning t m 2764) (meaning t m 3359) (meaning t m 3540) (meaning t m 4425) source

theorem rule17439 (p1990 p2027 p2210 p2284 p2699 p2972 p4208 : Prop) (h : (¬ p2972) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2284) ∨ p2699 ∨ (¬ p2210) ∨ (¬ p4208)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2972) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial17439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory6711 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule17439 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2284) (meaning t m 2699) (meaning t m 2972) (meaning t m 4208) source

theorem rule17440 (p2024 p2027 p2417 p2633 p2761 p3644 p5284 : Prop) (h : (¬ p2024) ∨ (¬ p5284) ∨ p2027 ∨ p2633 ∨ (¬ p2761) ∨ (¬ p2417) ∨ (¬ p3644)) : (¬ p2024) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p2761) ∨ (¬ p3644) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial17440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory6712 t (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule17440 (meaning t m 2024) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 2761) (meaning t m 3644) (meaning t m 5284) source

theorem rule17441 (p1990 p2027 p2253 p2331 p2699 p3027 p3097 p3552 p4154 : Prop) (h : (¬ p3027) ∨ (¬ p2253) ∨ p2699 ∨ p2027 ∨ (¬ p4154) ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p2331) ∨ (¬ p3552)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial17441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory6713 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule17441 (meaning t m 1990) (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 2699) (meaning t m 3027) (meaning t m 3097) (meaning t m 3552) (meaning t m 4154) source

theorem rule17442 (p1998 p2027 p2241 p2699 p2881 p2901 p2992 : Prop) (h : p2027 ∨ (¬ p2901) ∨ (¬ p2241) ∨ (¬ p2992) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial17442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory6714 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17442 (meaning t m 1998) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2881) (meaning t m 2901) (meaning t m 2992) source

theorem rule17443 (p2005 p2027 p2202 p2440 p2476 p2573 p3083 : Prop) (h : p2027 ∨ (¬ p2005) ∨ p2202 ∨ (¬ p3083) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2573)) : (¬ p2005) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial17443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory6715 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule17443 (meaning t m 2005) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2476) (meaning t m 2573) (meaning t m 3083) source

theorem rule17445 (p1975 p2027 p2192 p2274 p3105 p3474 p4363 : Prop) (h : (¬ p3105) ∨ p3474 ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p4363)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p3105) ∨ (p3474) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial17445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3105)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory6717 t (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule17445 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2274) (meaning t m 3105) (meaning t m 3474) (meaning t m 4363) source

theorem rule17447 (p2001 p2027 p2202 p2440 p2475 p3083 p3998 p5568 : Prop) (h : (¬ p5568) ∨ p2202 ∨ (¬ p2001) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p2475) ∨ (¬ p3998) ∨ (¬ p2440)) : (¬ p2001) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3998) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial17447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory6719 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule17447 (meaning t m 2001) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2475) (meaning t m 3083) (meaning t m 3998) (meaning t m 5568) source

theorem rule17448 (p2000 p2027 p2202 p2440 p2579 p2668 p3019 p3956 : Prop) (h : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p3019) ∨ (¬ p3956) ∨ (¬ p2668)) : (¬ p2000) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial17448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory6720 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule17448 (meaning t m 2000) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2579) (meaning t m 2668) (meaning t m 3019) (meaning t m 3956) source

theorem rule17449 (p2012 p2027 p2202 p2437 p2440 p3355 p3540 : Prop) (h : (¬ p2440) ∨ (¬ p2437) ∨ (¬ p3540) ∨ p2027 ∨ p2202 ∨ (¬ p2012) ∨ (¬ p3355)) : (¬ p2012) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3355) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial17449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory6721 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 9)
  exact rule17449 (meaning t m 2012) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 3355) (meaning t m 3540) source

theorem rule17453 (p2007 p2027 p2202 p2437 p2440 p2470 p3540 : Prop) (h : (¬ p2440) ∨ (¬ p2437) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2007) ∨ p2202 ∨ (¬ p2470)) : (¬ p2007) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2470) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial17453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory6725 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule17453 (meaning t m 2007) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2470) (meaning t m 3540) source

theorem rule17454 (p2192 p2972 p4334 : Prop) (h : (¬ p4334) ∨ (¬ p2192) ∨ p2972) : (¬ p2192) ∨ (p2972) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial17454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (meaning t m 2972) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory6726 (m.theta 1 5) (m.theta 5 6) (m.theta 5 9)
  exact rule17454 (meaning t m 2192) (meaning t m 2972) (meaning t m 4334) source

theorem rule17455 (p1975 p2027 p2202 p2299 p2437 p2440 p2911 : Prop) (h : (¬ p2299) ∨ (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial17455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory6727 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17455 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2437) (meaning t m 2440) (meaning t m 2911) source

theorem rule17458 (p2009 p2027 p2202 p2440 p3083 p4149 p5590 : Prop) (h : p2027 ∨ (¬ p2009) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p5590)) : (¬ p2009) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial17458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory6730 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 10)
  exact rule17458 (meaning t m 2009) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3083) (meaning t m 4149) (meaning t m 5590) source

theorem rule17461 (p2024 p2027 p2202 p2440 p2476 p2655 p3083 p3286 : Prop) (h : p2027 ∨ (¬ p2024) ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p2655) ∨ (¬ p3286) ∨ (¬ p2476)) : (¬ p2024) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p3083) ∨ (¬ p3286) := by
  classical
  tauto

theorem initial17461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3286)) := by
  have source := ElevenTheory.theory6733 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 8)
  exact rule17461 (meaning t m 2024) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2476) (meaning t m 2655) (meaning t m 3083) (meaning t m 3286) source

theorem rule17463 (p1991 p2027 p2766 p3172 p3979 p4347 p5600 : Prop) (h : (¬ p3979) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p4347) ∨ p2766 ∨ (¬ p3172) ∨ (¬ p5600)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial17463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory6735 t (m.theta 0 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17463 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 3172) (meaning t m 3979) (meaning t m 4347) (meaning t m 5600) source

theorem rule17464 (p2000 p2202 p2440 p2659 : Prop) (h : (¬ p2440) ∨ (¬ p2000) ∨ p2202 ∨ p2659) : (¬ p2000) ∨ (p2202) ∨ (¬ p2440) ∨ (p2659) := by
  classical
  tauto

theorem initial17464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2659) := by
  have source := ElevenTheory.theory6736 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5)
  exact rule17464 (meaning t m 2000) (meaning t m 2202) (meaning t m 2440) (meaning t m 2659) source

theorem rule17466 (p1992 p2027 p2202 p2440 p2476 p2655 p2743 p3083 p3361 : Prop) (h : p2027 ∨ (¬ p2743) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p1992) ∨ (¬ p3361) ∨ (¬ p2655) ∨ (¬ p2476) ∨ (¬ p3083)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (¬ p3083) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial17466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory6738 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule17466 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2476) (meaning t m 2655) (meaning t m 2743) (meaning t m 3083) (meaning t m 3361) source

theorem rule17468 (p3580 p4661 p5176 : Prop) (h : (¬ p4661) ∨ (¬ p3580) ∨ p5176) : (¬ p3580) ∨ (¬ p4661) ∨ (p5176) := by
  classical
  tauto

theorem initial17468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4661)) ∨ (meaning t m 5176) := by
  have source := ElevenTheory.theory6740 (m.theta 3 4) (m.theta 3 7) (m.theta 3 9)
  exact rule17468 (meaning t m 3580) (meaning t m 4661) (meaning t m 5176) source

theorem rule17469 (p2437 p3192 p3343 : Prop) (h : (¬ p3192) ∨ (¬ p2437) ∨ p3343) : (¬ p2437) ∨ (¬ p3192) ∨ (p3343) := by
  classical
  tauto

theorem initial17469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3192)) ∨ (meaning t m 3343) := by
  have source := ElevenTheory.theory6741 (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule17469 (meaning t m 2437) (meaning t m 3192) (meaning t m 3343) source

theorem rule17473 (p1995 p2148 p3379 p4521 : Prop) (h : (¬ p1995) ∨ (¬ p3379) ∨ p2148 ∨ p4521) : (¬ p1995) ∨ (p2148) ∨ (¬ p3379) ∨ (p4521) := by
  classical
  tauto

theorem initial17473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 4521) := by
  have source := ElevenTheory.theory6745 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4)
  exact rule17473 (meaning t m 1995) (meaning t m 2148) (meaning t m 3379) (meaning t m 4521) source

theorem rule17476 (p1992 p2027 p2202 p2608 p2927 p3201 p3684 p4366 : Prop) (h : (¬ p1992) ∨ p2202 ∨ (¬ p2608) ∨ (¬ p3684) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2927)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2608) ∨ (¬ p2927) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial17476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory6748 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule17476 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2608) (meaning t m 2927) (meaning t m 3201) (meaning t m 3684) (meaning t m 4366) source

theorem rule17481 (p1981 p2027 p2138 p2187 p3366 p3474 p3687 p4075 p4204 p5660 : Prop) (h : p3474 ∨ (¬ p3366) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2187) ∨ (¬ p2138) ∨ (¬ p4204) ∨ (¬ p3687) ∨ (¬ p4075) ∨ (¬ p5660)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2187) ∨ (¬ p3366) ∨ (p3474) ∨ (¬ p3687) ∨ (¬ p4075) ∨ (¬ p4204) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial17481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3366)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory6753 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 10)
  exact rule17481 (meaning t m 1981) (meaning t m 2027) (meaning t m 2138) (meaning t m 2187) (meaning t m 3366) (meaning t m 3474) (meaning t m 3687) (meaning t m 4075) (meaning t m 4204) (meaning t m 5660) source

theorem rule17483 (p1995 p2202 p2440 p4811 : Prop) (h : p2202 ∨ (¬ p2440) ∨ (¬ p1995) ∨ p4811) : (¬ p1995) ∨ (p2202) ∨ (¬ p2440) ∨ (p4811) := by
  classical
  tauto

theorem initial17483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 4811) := by
  have source := ElevenTheory.theory6755 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule17483 (meaning t m 1995) (meaning t m 2202) (meaning t m 2440) (meaning t m 4811) source

theorem rule17487 (p1992 p2027 p2202 p2440 p3083 p3585 p3874 : Prop) (h : (¬ p3083) ∨ (¬ p2440) ∨ p2027 ∨ p2202 ∨ (¬ p3585) ∨ (¬ p1992) ∨ (¬ p3874)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3585) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial17487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory6759 t (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule17487 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3083) (meaning t m 3585) (meaning t m 3874) source

theorem rule17488 (p2010 p2027 p2202 p2440 p2476 p3083 p3389 : Prop) (h : (¬ p2476) ∨ (¬ p3083) ∨ p2027 ∨ p2202 ∨ (¬ p2010) ∨ (¬ p2440) ∨ (¬ p3389)) : (¬ p2010) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial17488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory6760 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule17488 (meaning t m 2010) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2476) (meaning t m 3083) (meaning t m 3389) source

theorem rule17491 (p1987 p2027 p2202 p2476 p2518 p2696 p3238 p3905 : Prop) (h : (¬ p2476) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3238) ∨ p2202 ∨ (¬ p3905) ∨ (¬ p1987) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2696) ∨ (¬ p3238) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial17491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory6763 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 4 5) (m.theta 4 8)
  exact rule17491 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2476) (meaning t m 2518) (meaning t m 2696) (meaning t m 3238) (meaning t m 3905) source

theorem rule17493 (p1991 p2027 p2177 p2579 p2655 p2997 p3016 p4256 p4383 : Prop) (h : p2997 ∨ (¬ p2177) ∨ (¬ p4383) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p2579) ∨ (¬ p1991) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial17493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory6765 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule17493 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2579) (meaning t m 2655) (meaning t m 2997) (meaning t m 3016) (meaning t m 4256) (meaning t m 4383) source

theorem rule17494 (p3115 p3156 p4335 : Prop) (h : (¬ p3115) ∨ (¬ p4335) ∨ p3156) : (¬ p3115) ∨ (p3156) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial17494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3115)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory6766 (m.theta 3 5) (m.theta 5 8) (m.theta 5 9)
  exact rule17494 (meaning t m 3115) (meaning t m 3156) (meaning t m 4335) source

theorem rule17495 (p1990 p2027 p2169 p2284 p2363 p3497 p3692 : Prop) (h : (¬ p2363) ∨ (¬ p2284) ∨ (¬ p3692) ∨ p2169 ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3497)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2284) ∨ (¬ p2363) ∨ (¬ p3497) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial17495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory6767 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17495 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2284) (meaning t m 2363) (meaning t m 3497) (meaning t m 3692) source

theorem rule17500 (p1983 p2027 p2699 p3093 p3309 p3461 p4187 p4381 : Prop) (h : (¬ p4187) ∨ (¬ p3461) ∨ (¬ p1983) ∨ p2027 ∨ p2699 ∨ (¬ p4381) ∨ (¬ p3093) ∨ (¬ p3309)) : (¬ p1983) ∨ (p2027) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6772 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule17500 (meaning t m 1983) (meaning t m 2027) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) (meaning t m 3461) (meaning t m 4187) (meaning t m 4381) source

theorem rule17505 (p2012 p2027 p2579 p2914 p3016 p3355 p3742 : Prop) (h : (¬ p3742) ∨ (¬ p2012) ∨ p2027 ∨ p2914 ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p3355)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2579) ∨ (p2914) ∨ (¬ p3016) ∨ (¬ p3355) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial17505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory6777 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 4 9)
  exact rule17505 (meaning t m 2012) (meaning t m 2027) (meaning t m 2579) (meaning t m 2914) (meaning t m 3016) (meaning t m 3355) (meaning t m 3742) source

theorem rule17506 (p1991 p2027 p2579 p2655 p2911 p2914 p3016 p3553 p4112 : Prop) (h : p2914 ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2655) ∨ (¬ p2579) ∨ (¬ p4112)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial17506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory6778 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule17506 (meaning t m 1991) (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2911) (meaning t m 2914) (meaning t m 3016) (meaning t m 3553) (meaning t m 4112) source

theorem rule17508 (p2319 p2786 p3819 : Prop) (h : p3819 ∨ (¬ p2319) ∨ (¬ p2786)) : (¬ p2319) ∨ (¬ p2786) ∨ (p3819) := by
  classical
  tauto

theorem initial17508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2786)) ∨ (meaning t m 3819) := by
  have source := ElevenTheory.theory6780 (m.theta 0 2) (m.theta 0 6) (m.theta 0 7)
  exact rule17508 (meaning t m 2319) (meaning t m 2786) (meaning t m 3819) source

theorem rule17511 (p1991 p2027 p2588 p2963 p2997 p3564 p4037 : Prop) (h : (¬ p2588) ∨ (¬ p4037) ∨ (¬ p1991) ∨ p2027 ∨ p2997 ∨ (¬ p3564) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial17511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory6783 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule17511 (meaning t m 1991) (meaning t m 2027) (meaning t m 2588) (meaning t m 2963) (meaning t m 2997) (meaning t m 3564) (meaning t m 4037) source

theorem rule17516 (p1987 p2027 p2284 p2388 p2737 p3583 p3758 : Prop) (h : (¬ p1987) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3583) ∨ p2388 ∨ (¬ p3758)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory6788 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule17516 (meaning t m 1987) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 2737) (meaning t m 3583) (meaning t m 3758) source

theorem rule17517 (p2177 p2911 p4710 : Prop) (h : (¬ p2177) ∨ (¬ p4710) ∨ p2911) : (¬ p2177) ∨ (p2911) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial17517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (meaning t m 2911) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory6789 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17517 (meaning t m 2177) (meaning t m 2911) (meaning t m 4710) source

theorem rule17519 (p1987 p2027 p2132 p2737 p3583 p3589 p3834 p4023 : Prop) (h : p2027 ∨ (¬ p3583) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p1987) ∨ p4023 ∨ (¬ p3589) ∨ (¬ p3834)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p3834) ∨ (p4023) := by
  classical
  tauto

theorem initial17519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3834)) ∨ (meaning t m 4023) := by
  have source := ElevenTheory.theory6791 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 2 5)
  exact rule17519 (meaning t m 1987) (meaning t m 2027) (meaning t m 2132) (meaning t m 2737) (meaning t m 3583) (meaning t m 3589) (meaning t m 3834) (meaning t m 4023) source

theorem rule17522 (p1987 p2027 p2143 p2284 p2388 p2737 p3583 p3646 : Prop) (h : p2388 ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p1987) ∨ (¬ p2143)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial17522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory6794 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule17522 (meaning t m 1987) (meaning t m 2027) (meaning t m 2143) (meaning t m 2284) (meaning t m 2388) (meaning t m 2737) (meaning t m 3583) (meaning t m 3646) source

theorem rule17523 (p1982 p2027 p2528 p2622 p2743 p3367 p3641 : Prop) (h : (¬ p2528) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3641) ∨ (¬ p3367) ∨ p2622 ∨ (¬ p2743)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial17523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory6795 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9)
  exact rule17523 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3641) source

theorem rule17526 (p1981 p2027 p2114 p2668 p2737 p2774 p3365 p4328 : Prop) (h : p2027 ∨ (¬ p2737) ∨ p2114 ∨ (¬ p1981) ∨ (¬ p2668) ∨ (¬ p4328) ∨ (¬ p2774) ∨ (¬ p3365)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial17526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory6798 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule17526 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2668) (meaning t m 2737) (meaning t m 2774) (meaning t m 3365) (meaning t m 4328) source

theorem rule17529 (p1984 p2027 p2764 p3486 p3555 p3690 p4381 : Prop) (h : (¬ p1984) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4381) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6801 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17529 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4381) source

theorem rule17534 (p1982 p2027 p2323 p2946 p3005 p3256 p4315 : Prop) (h : (¬ p4315) ∨ p2323 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p2946)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial17534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory6806 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule17534 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3005) (meaning t m 3256) (meaning t m 4315) source

theorem rule17536 (p1985 p2027 p2114 p2137 p2156 p2427 p2839 p4110 : Prop) (h : (¬ p1985) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2839) ∨ p2114 ∨ (¬ p2137) ∨ (¬ p2156)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2839) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6808 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17536 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2156) (meaning t m 2427) (meaning t m 2839) (meaning t m 4110) source

theorem rule17539 (p1994 p2027 p2230 p2440 p2622 p2743 p3367 p3759 : Prop) (h : (¬ p2230) ∨ (¬ p3759) ∨ (¬ p3367) ∨ p2622 ∨ (¬ p2743) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6811 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule17539 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3759) source

theorem rule17540 (p1990 p2027 p2122 p2829 p3097 p3474 p3583 : Prop) (h : (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2829) ∨ p3474 ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2122)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (p3474) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial17540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory6812 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17540 (meaning t m 1990) (meaning t m 2027) (meaning t m 2122) (meaning t m 2829) (meaning t m 3097) (meaning t m 3474) (meaning t m 3583) source

theorem rule17541 (p1990 p2027 p2138 p2774 p2819 p3474 p3989 : Prop) (h : p3474 ∨ (¬ p3989) ∨ (¬ p2138) ∨ (¬ p2819) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2774)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (p3474) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6813 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule17541 (meaning t m 1990) (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 2819) (meaning t m 3474) (meaning t m 3989) source

theorem rule17543 (p1990 p2202 p2284 p4702 : Prop) (h : (¬ p1990) ∨ (¬ p2284) ∨ p2202 ∨ p4702) : (¬ p1990) ∨ (p2202) ∨ (¬ p2284) ∨ (p4702) := by
  classical
  tauto

theorem initial17543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 4702) := by
  have source := ElevenTheory.theory6815 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule17543 (meaning t m 1990) (meaning t m 2202) (meaning t m 2284) (meaning t m 4702) source

theorem rule17544 (p2001 p2027 p2088 p2202 p2563 p3646 p3692 p4238 : Prop) (h : (¬ p2088) ∨ p2202 ∨ (¬ p3692) ∨ (¬ p2001) ∨ (¬ p4238) ∨ (¬ p3646) ∨ (¬ p2563) ∨ p2027) : (¬ p2001) ∨ (p2027) ∨ (¬ p2088) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial17544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory6816 t (m.theta 0 5) (m.theta 0 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule17544 (meaning t m 2001) (meaning t m 2027) (meaning t m 2088) (meaning t m 2202) (meaning t m 2563) (meaning t m 3646) (meaning t m 3692) (meaning t m 4238) source

theorem rule17545 (p1982 p2363 p3498 p4384 : Prop) (h : p3498 ∨ (¬ p2363) ∨ (¬ p1982) ∨ p4384) : (¬ p1982) ∨ (¬ p2363) ∨ (p3498) ∨ (p4384) := by
  classical
  tauto

theorem initial17545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 3498) ∨ (meaning t m 4384) := by
  have source := ElevenTheory.theory6817 t (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17545 (meaning t m 1982) (meaning t m 2363) (meaning t m 3498) (meaning t m 4384) source

theorem rule17546 (p1984 p2027 p2284 p2388 p3583 p3758 p3954 : Prop) (h : p2388 ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p2284) ∨ (¬ p3758)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6818 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule17546 (meaning t m 1984) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 3583) (meaning t m 3758) (meaning t m 3954) source

theorem rule17549 (p1983 p2027 p2299 p2396 p2611 p2717 p3471 : Prop) (h : (¬ p2396) ∨ p2611 ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2299) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2611) ∨ (¬ p2717) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial17549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory6821 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17549 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2611) (meaning t m 2717) (meaning t m 3471) source

theorem rule17550 (p1991 p2027 p2437 p2440 p2655 p2765 p3540 p4110 : Prop) (h : (¬ p1991) ∨ p2027 ∨ (¬ p2440) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p3540) ∨ (¬ p2655) ∨ (¬ p2437)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2655) ∨ (p2765) ∨ (¬ p3540) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6822 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule17550 (meaning t m 1991) (meaning t m 2027) (meaning t m 2437) (meaning t m 2440) (meaning t m 2655) (meaning t m 2765) (meaning t m 3540) (meaning t m 4110) source

theorem rule17554 (p1989 p2027 p2137 p2553 p3008 p3212 p3822 p4193 p4363 : Prop) (h : p2027 ∨ (¬ p1989) ∨ (¬ p4363) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p3212) ∨ (¬ p2137) ∨ p3008 ∨ (¬ p2553)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3212) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial17554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory6826 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7)
  exact rule17554 (meaning t m 1989) (meaning t m 2027) (meaning t m 2137) (meaning t m 2553) (meaning t m 3008) (meaning t m 3212) (meaning t m 3822) (meaning t m 4193) (meaning t m 4363) source

theorem rule17557 (p1991 p2388 p2963 p4566 : Prop) (h : (¬ p2963) ∨ p2388 ∨ (¬ p1991) ∨ p4566) : (¬ p1991) ∨ (p2388) ∨ (¬ p2963) ∨ (p4566) := by
  classical
  tauto

theorem initial17557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 4566) := by
  have source := ElevenTheory.theory6829 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule17557 (meaning t m 1991) (meaning t m 2388) (meaning t m 2963) (meaning t m 4566) source

theorem rule17558 (p1988 p2027 p2608 p2699 p3266 p3537 p3609 : Prop) (h : (¬ p1988) ∨ p2699 ∨ p2027 ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3266) ∨ (¬ p2608)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3609) := by
  classical
  tauto

theorem initial17558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) := by
  have source := ElevenTheory.theory6830 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17558 (meaning t m 1988) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3266) (meaning t m 3537) (meaning t m 3609) source

theorem rule17560 (p1997 p2027 p2274 p2313 p2386 p2406 p2499 p2765 : Prop) (h : (¬ p2499) ∨ (¬ p2313) ∨ p2765 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2386) ∨ (¬ p1997) ∨ (¬ p2406)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (p2765) := by
  classical
  tauto

theorem initial17560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2765) := by
  have source := ElevenTheory.theory6832 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17560 (meaning t m 1997) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2386) (meaning t m 2406) (meaning t m 2499) (meaning t m 2765) source

theorem rule17561 (p2000 p2476 p2484 p4080 : Prop) (h : p4080 ∨ (¬ p2000) ∨ p2484 ∨ (¬ p2476)) : (¬ p2000) ∨ (¬ p2476) ∨ (p2484) ∨ (p4080) := by
  classical
  tauto

theorem initial17561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2484) ∨ (meaning t m 4080) := by
  have source := ElevenTheory.theory6833 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 8)
  exact rule17561 (meaning t m 2000) (meaning t m 2476) (meaning t m 2484) (meaning t m 4080) source

theorem rule17565 (p2000 p2027 p2579 p2668 p2997 p3568 p3956 : Prop) (h : p2027 ∨ (¬ p2000) ∨ (¬ p2668) ∨ p2997 ∨ (¬ p3956) ∨ (¬ p3568) ∨ (¬ p2579)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial17565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory6837 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17565 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3956) source

theorem rule17567 (p1980 p2027 p2797 p3146 p3177 p3578 p3857 p3877 : Prop) (h : (¬ p3857) ∨ (¬ p1980) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2797) ∨ p3578 ∨ (¬ p3177) ∨ (¬ p3146)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2797) ∨ (¬ p3146) ∨ (¬ p3177) ∨ (p3578) ∨ (¬ p3857) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial17567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3177)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory6839 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17567 (meaning t m 1980) (meaning t m 2027) (meaning t m 2797) (meaning t m 3146) (meaning t m 3177) (meaning t m 3578) (meaning t m 3857) (meaning t m 3877) source

theorem rule17569 (p1999 p2027 p2331 p2611 p3564 p4117 p4228 p5514 : Prop) (h : p2611 ∨ (¬ p1999) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4228) ∨ (¬ p5514)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2331) ∨ (p2611) ∨ (¬ p3564) ∨ (¬ p4117) ∨ (¬ p4228) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial17569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory6841 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 10) (m.theta 6 9)
  exact rule17569 (meaning t m 1999) (meaning t m 2027) (meaning t m 2331) (meaning t m 2611) (meaning t m 3564) (meaning t m 4117) (meaning t m 4228) (meaning t m 5514) source

theorem rule17570 (p1975 p2027 p2299 p2598 p2611 p2911 p3201 : Prop) (h : (¬ p2598) ∨ p2611 ∨ (¬ p2911) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2911) ∨ (¬ p3201) := by
  classical
  tauto

theorem initial17570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) := by
  have source := ElevenTheory.theory6842 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17570 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2598) (meaning t m 2611) (meaning t m 2911) (meaning t m 3201) source

theorem rule17571 (p2001 p2027 p2323 p2373 p2542 p2573 p2663 p3574 : Prop) (h : (¬ p2542) ∨ p2323 ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2001) ∨ (¬ p2373) ∨ (¬ p2663) ∨ (¬ p2573)) : (¬ p2001) ∨ (p2027) ∨ (p2323) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial17571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory6843 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule17571 (meaning t m 2001) (meaning t m 2027) (meaning t m 2323) (meaning t m 2373) (meaning t m 2542) (meaning t m 2573) (meaning t m 2663) (meaning t m 3574) source

theorem rule17572 (p1997 p2027 p2166 p2210 p2247 p2688 p3880 : Prop) (h : (¬ p2247) ∨ p2688 ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3880) ∨ (¬ p2210) ∨ (¬ p2166)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial17572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory6844 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule17572 (meaning t m 1997) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 3880) source

theorem rule17574 (p3093 p3369 p3370 p4512 : Prop) (h : (¬ p3369) ∨ (¬ p3093) ∨ (¬ p3370) ∨ (¬ p4512)) : (¬ p3093) ∨ (¬ p3369) ∨ (¬ p3370) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial17574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory6846 (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 1 6)
  exact rule17574 (meaning t m 3093) (meaning t m 3369) (meaning t m 3370) (meaning t m 4512) source

theorem rule17577 (p1987 p2027 p2589 p2662 p2766 p2810 p3692 p3880 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p3880) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p2662)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial17577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory6849 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule17577 (meaning t m 1987) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2766) (meaning t m 2810) (meaning t m 3692) (meaning t m 3880) source

theorem rule17580 (p1998 p2027 p2323 p2717 p2807 p3931 p4423 : Prop) (h : (¬ p2717) ∨ p2323 ∨ (¬ p1998) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p3931) ∨ (¬ p4423)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2717) ∨ (¬ p2807) ∨ (¬ p3931) ∨ (¬ p4423) := by
  classical
  tauto

theorem initial17580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4423)) := by
  have source := ElevenTheory.theory6852 t (m.theta 0 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 10) (m.theta 7 8)
  exact rule17580 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2717) (meaning t m 2807) (meaning t m 3931) (meaning t m 4423) source

theorem rule17587 (p1979 p2027 p2241 p2699 p2727 p2810 p3136 : Prop) (h : p2699 ∨ (¬ p2810) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p2727) ∨ (¬ p2241)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial17587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory6859 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule17587 (meaning t m 1979) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2727) (meaning t m 2810) (meaning t m 3136) source

theorem rule17588 (p2005 p2027 p2440 p2598 p2611 p2850 p3016 : Prop) (h : p2611 ∨ (¬ p2005) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial17588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory6860 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule17588 (meaning t m 2005) (meaning t m 2027) (meaning t m 2440) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 3016) source

theorem rule17589 (p2005 p2027 p2598 p2611 p3016 p3333 p3359 : Prop) (h : p2611 ∨ (¬ p3333) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3016) ∨ (¬ p3333) ∨ (¬ p3359) := by
  classical
  tauto

theorem initial17589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3359)) := by
  have source := ElevenTheory.theory6861 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule17589 (meaning t m 2005) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 3016) (meaning t m 3333) (meaning t m 3359) source

theorem rule17593 (p1987 p2027 p2699 p3093 p3309 p3568 p4195 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p3093) ∨ (¬ p1987) ∨ (¬ p3309)) : (¬ p1987) ∨ (p2027) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial17593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory6865 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule17593 (meaning t m 1987) (meaning t m 2027) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) (meaning t m 3568) (meaning t m 4195) source

theorem rule17595 (p1987 p2027 p2177 p2662 p2810 p2997 p3540 p3644 : Prop) (h : p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p3540) ∨ p2997 ∨ (¬ p3644) ∨ (¬ p2177)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p3540) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial17595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory6867 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17595 (meaning t m 1987) (meaning t m 2027) (meaning t m 2177) (meaning t m 2662) (meaning t m 2810) (meaning t m 2997) (meaning t m 3540) (meaning t m 3644) source

theorem rule17596 (p1987 p2027 p2323 p2641 p2946 p3662 p4195 : Prop) (h : (¬ p2641) ∨ (¬ p1987) ∨ p2027 ∨ p2323 ∨ (¬ p4195) ∨ (¬ p2946) ∨ (¬ p3662)) : (¬ p1987) ∨ (p2027) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial17596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory6868 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule17596 (meaning t m 1987) (meaning t m 2027) (meaning t m 2323) (meaning t m 2641) (meaning t m 2946) (meaning t m 3662) (meaning t m 4195) source

theorem rule17600 (p1987 p2027 p2563 p2810 p2938 p3487 p4173 p4202 p4235 : Prop) (h : p2938 ∨ (¬ p2810) ∨ (¬ p4235) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p1987) ∨ (¬ p3487)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2810) ∨ (p2938) ∨ (¬ p3487) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6872 t (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17600 (meaning t m 1987) (meaning t m 2027) (meaning t m 2563) (meaning t m 2810) (meaning t m 2938) (meaning t m 3487) (meaning t m 4173) (meaning t m 4202) (meaning t m 4235) source

theorem rule17601 (p1987 p2027 p2563 p2662 p2810 p2938 p3646 p3904 p4235 : Prop) (h : p2938 ∨ (¬ p3904) ∨ (¬ p1987) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3646)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p2938) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6873 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17601 (meaning t m 1987) (meaning t m 2027) (meaning t m 2563) (meaning t m 2662) (meaning t m 2810) (meaning t m 2938) (meaning t m 3646) (meaning t m 3904) (meaning t m 4235) source

theorem rule17602 (p3568 p3822 p4337 : Prop) (h : (¬ p4337) ∨ (¬ p3568) ∨ p3822) : (¬ p3568) ∨ (p3822) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial17602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3568)) ∨ (meaning t m 3822) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory6874 (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule17602 (meaning t m 3568) (meaning t m 3822) (meaning t m 4337) source

end SunPrize.SMT
