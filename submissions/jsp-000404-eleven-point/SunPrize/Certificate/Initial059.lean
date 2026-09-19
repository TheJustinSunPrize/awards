import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory043
import SunPrize.Certificate.Theory044
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule25417 (p2027 p2098 p2299 p3549 p3591 p3609 p3692 p4733 p4902 : Prop) (h : (¬ p2299) ∨ (¬ p3549) ∨ (¬ p4902) ∨ (¬ p4733) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3591) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial25417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory14673 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25417 (meaning t m 2027) (meaning t m 2098) (meaning t m 2299) (meaning t m 3549) (meaning t m 3591) (meaning t m 3609) (meaning t m 3692) (meaning t m 4733) (meaning t m 4902) source

theorem rule25419 (p2027 p2696 p3005 p3256 p3549 p3591 p4107 p4669 p4733 : Prop) (h : (¬ p3005) ∨ (¬ p2696) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p4733) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14675 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25419 (meaning t m 2027) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4669) (meaning t m 4733) source

theorem rule25420 (p2027 p2132 p2619 p3146 p3549 p3591 p4107 p4669 p4733 : Prop) (h : p2027 ∨ (¬ p4669) ∨ (¬ p4733) ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p3591) ∨ (¬ p3549) ∨ (¬ p2619) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14676 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25420 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 3146) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4669) (meaning t m 4733) source

theorem rule25421 (p2027 p2274 p2579 p2588 p2797 p2807 p3572 p4117 p4564 p4729 : Prop) (h : (¬ p4117) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p4564) ∨ (¬ p2274) ∨ (¬ p2807) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4729) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4564) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial25421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory14677 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule25421 (meaning t m 2027) (meaning t m 2274) (meaning t m 2579) (meaning t m 2588) (meaning t m 2797) (meaning t m 2807) (meaning t m 3572) (meaning t m 4117) (meaning t m 4564) (meaning t m 4729) source

theorem rule25422 (p2027 p2579 p2588 p2696 p2753 p3005 p3256 p3347 p4107 p4669 p5216 : Prop) (h : (¬ p4107) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3256) ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2753) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3347) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14678 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25422 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3347) (meaning t m 4107) (meaning t m 4669) (meaning t m 5216) source

theorem rule25424 (p3906 p3969 p4181 : Prop) (h : (¬ p4181) ∨ (¬ p3906) ∨ p3969) : (¬ p3906) ∨ (p3969) ∨ (¬ p4181) := by
  classical
  tauto

theorem initial25424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3906)) ∨ (meaning t m 3969) ∨ (¬ (meaning t m 4181)) := by
  have source := ElevenTheory.theory14680 (m.theta 1 8) (m.theta 5 8) (m.theta 8 10)
  exact rule25424 (meaning t m 3906) (meaning t m 3969) (meaning t m 4181) source

theorem rule25425 (p2027 p2363 p2589 p2753 p2774 p2819 p3347 p3880 p5118 p5216 p5568 : Prop) (h : (¬ p5118) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2589) ∨ (¬ p2819) ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p2363) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p5568)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3347) ∨ (¬ p3880) ∨ (¬ p5118) ∨ (¬ p5216) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial25425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory14681 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25425 (meaning t m 2027) (meaning t m 2363) (meaning t m 2589) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3347) (meaning t m 3880) (meaning t m 5118) (meaning t m 5216) (meaning t m 5568) source

theorem rule25427 (p2027 p2417 p2542 p3947 p4112 p4644 : Prop) (h : (¬ p2542) ∨ (¬ p4112) ∨ (¬ p4644) ∨ (¬ p3947) ∨ (¬ p2417) ∨ p2027) : (p2027) ∨ (¬ p2417) ∨ (¬ p2542) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial25427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory14683 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule25427 (meaning t m 2027) (meaning t m 2417) (meaning t m 2542) (meaning t m 3947) (meaning t m 4112) (meaning t m 4644) source

theorem rule25428 (p4208 p4385 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p4385) ∨ p4208) : (p4208) ∨ (¬ p4385) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial25428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4208) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory14684 (m.theta 2 5) (m.theta 3 5) (m.theta 5 9)
  exact rule25428 (meaning t m 4208) (meaning t m 4385) (meaning t m 5051) source

theorem rule25438 (p3434 p3657 p3659 : Prop) (h : (¬ p3659) ∨ (¬ p3657) ∨ (¬ p3434)) : (¬ p3434) ∨ (¬ p3657) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial25438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory14694 (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25438 (meaning t m 3434) (meaning t m 3657) (meaning t m 3659) source

theorem rule25441 (p1997 p2027 p2177 p2997 p3767 p3960 p4110 p4321 p4430 p4461 p4516 : Prop) (h : (¬ p2177) ∨ (¬ p4110) ∨ (¬ p1997) ∨ (¬ p4461) ∨ (¬ p4321) ∨ (¬ p4516) ∨ (¬ p3960) ∨ (¬ p4430) ∨ p2997 ∨ p2027 ∨ (¬ p3767)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3767) ∨ (¬ p3960) ∨ (¬ p4110) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4461) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial25441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4430)) ∨ (¬ (meaning t m 4461)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory14697 t (m.theta 0 8) (m.theta 0 9) (m.theta 1 6) (m.theta 1 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 9 10)
  exact rule25441 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3767) (meaning t m 3960) (meaning t m 4110) (meaning t m 4321) (meaning t m 4430) (meaning t m 4461) (meaning t m 4516) source

theorem rule25445 (p2027 p2144 p3212 p3365 p4030 p4202 p4363 p4752 : Prop) (h : p2027 ∨ (¬ p3365) ∨ (¬ p2144) ∨ (¬ p3212) ∨ (¬ p4030) ∨ (¬ p4363) ∨ (¬ p4752) ∨ (¬ p4202)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3212) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4363) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14701 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 9)
  exact rule25445 (meaning t m 2027) (meaning t m 2144) (meaning t m 3212) (meaning t m 3365) (meaning t m 4030) (meaning t m 4202) (meaning t m 4363) (meaning t m 4752) source

theorem rule25449 (p2027 p2241 p2727 p3343 p3646 p3989 p4332 p4347 p4524 : Prop) (h : p2027 ∨ (¬ p3989) ∨ (¬ p3343) ∨ (¬ p2727) ∨ (¬ p4524) ∨ (¬ p4332) ∨ (¬ p2241) ∨ (¬ p3646) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14705 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25449 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3343) (meaning t m 3646) (meaning t m 3989) (meaning t m 4332) (meaning t m 4347) (meaning t m 4524) source

theorem rule25450 (p2027 p2136 p2449 p2761 p2807 p3646 p3989 p4786 p5123 p5580 : Prop) (h : (¬ p2449) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p2136) ∨ (¬ p5580) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory14706 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25450 (meaning t m 2027) (meaning t m 2136) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3646) (meaning t m 3989) (meaning t m 4786) (meaning t m 5123) (meaning t m 5580) source

theorem rule25451 (p2027 p2138 p3286 p3506 p3692 p3694 p3950 p4381 p4786 : Prop) (h : (¬ p2138) ∨ (¬ p4786) ∨ (¬ p4381) ∨ (¬ p3950) ∨ (¬ p3506) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3286) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14707 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 9) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25451 (meaning t m 2027) (meaning t m 2138) (meaning t m 3286) (meaning t m 3506) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4381) (meaning t m 4786) source

theorem rule25452 (p2782 p3204 p4867 : Prop) (h : (¬ p4867) ∨ (¬ p3204) ∨ p2782) : (p2782) ∨ (¬ p3204) ∨ (¬ p4867) := by
  classical
  tauto

theorem initial25452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2782) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 4867)) := by
  have source := ElevenTheory.theory14708 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 6)
  exact rule25452 (meaning t m 2782) (meaning t m 3204) (meaning t m 4867) source

theorem rule25453 (p2027 p2960 p2992 p2996 p3051 p3699 : Prop) (h : (¬ p2960) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p3699) ∨ p2027) : (p2027) ∨ (¬ p2960) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial25453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory14709 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule25453 (meaning t m 2027) (meaning t m 2960) (meaning t m 2992) (meaning t m 2996) (meaning t m 3051) (meaning t m 3699) source

theorem rule25454 (p1992 p2699 p3379 p4376 : Prop) (h : (¬ p1992) ∨ p2699 ∨ (¬ p3379) ∨ p4376) : (¬ p1992) ∨ (p2699) ∨ (¬ p3379) ∨ (p4376) := by
  classical
  tauto

theorem initial25454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 4376) := by
  have source := ElevenTheory.theory14710 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4)
  exact rule25454 (meaning t m 1992) (meaning t m 2699) (meaning t m 3379) (meaning t m 4376) source

theorem rule25455 (p2027 p2241 p2579 p2588 p3189 p3256 p4107 p4669 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p4107) ∨ (¬ p2588) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2241) ∨ (¬ p3256) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial25455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory14711 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25455 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 2588) (meaning t m 3189) (meaning t m 3256) (meaning t m 4107) (meaning t m 4669) (meaning t m 5193) source

theorem rule25456 (p2027 p2534 p2901 p2946 p3055 p3246 p3874 p3950 p4786 : Prop) (h : (¬ p3246) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p2901) ∨ (¬ p3950) ∨ (¬ p4786) ∨ (¬ p2946) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14712 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25456 (meaning t m 2027) (meaning t m 2534) (meaning t m 2901) (meaning t m 2946) (meaning t m 3055) (meaning t m 3246) (meaning t m 3874) (meaning t m 3950) (meaning t m 4786) source

theorem rule25457 (p1998 p2027 p2387 p2534 p2766 p2778 p2881 p2901 p2946 p4149 p4786 p5580 : Prop) (h : (¬ p4149) ∨ (¬ p2778) ∨ (¬ p5580) ∨ (¬ p2387) ∨ p2766 ∨ p2027 ∨ (¬ p2881) ∨ (¬ p1998) ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p4786) ∨ (¬ p2534)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p2778) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4149) ∨ (¬ p4786) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory14713 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25457 (meaning t m 1998) (meaning t m 2027) (meaning t m 2387) (meaning t m 2534) (meaning t m 2766) (meaning t m 2778) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 4149) (meaning t m 4786) (meaning t m 5580) source

theorem rule25458 (p2027 p2946 p3055 p3115 p3680 p3874 p4286 p4786 p5123 : Prop) (h : (¬ p3680) ∨ (¬ p4786) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p4286) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4786) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial25458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory14714 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25458 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3115) (meaning t m 3680) (meaning t m 3874) (meaning t m 4286) (meaning t m 4786) (meaning t m 5123) source

theorem rule25459 (p2027 p2901 p2946 p3246 p3266 p3346 p3905 p3950 p4425 p4786 : Prop) (h : (¬ p2946) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3950) ∨ (¬ p3266) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p2901) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3905) ∨ (¬ p3950) ∨ (¬ p4425) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14715 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25459 (meaning t m 2027) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3266) (meaning t m 3346) (meaning t m 3905) (meaning t m 3950) (meaning t m 4425) (meaning t m 4786) source

theorem rule25460 (p2027 p2241 p3506 p3646 p3842 p3989 p4524 p5123 p5580 : Prop) (h : (¬ p3989) ∨ (¬ p5580) ∨ (¬ p3506) ∨ (¬ p5123) ∨ (¬ p3646) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3842)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3842) ∨ (¬ p3989) ∨ (¬ p4524) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory14716 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25460 (meaning t m 2027) (meaning t m 2241) (meaning t m 3506) (meaning t m 3646) (meaning t m 3842) (meaning t m 3989) (meaning t m 4524) (meaning t m 5123) (meaning t m 5580) source

theorem rule25463 (p2027 p2241 p3506 p3556 p3570 p3842 p4524 p5123 p5558 : Prop) (h : (¬ p3842) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2241) ∨ (¬ p3506) ∨ (¬ p4524) ∨ (¬ p5123) ∨ (¬ p3570) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3842) ∨ (¬ p4524) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial25463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory14719 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25463 (meaning t m 2027) (meaning t m 2241) (meaning t m 3506) (meaning t m 3556) (meaning t m 3570) (meaning t m 3842) (meaning t m 4524) (meaning t m 5123) (meaning t m 5558) source

theorem rule25464 (p2027 p3016 p3125 p3359 p3958 p4022 : Prop) (h : (¬ p3958) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3125) ∨ (¬ p4022)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3125) ∨ (¬ p3359) ∨ (¬ p3958) ∨ (¬ p4022) := by
  classical
  tauto

theorem initial25464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4022)) := by
  have source := ElevenTheory.theory14720 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9)
  exact rule25464 (meaning t m 2027) (meaning t m 3016) (meaning t m 3125) (meaning t m 3359) (meaning t m 3958) (meaning t m 4022) source

theorem rule25466 (p2027 p2136 p2417 p2437 p2619 p2651 p3951 p4120 p4385 p4786 : Prop) (h : (¬ p2417) ∨ (¬ p2136) ∨ (¬ p2651) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p2437) ∨ (¬ p2619) ∨ (¬ p4385) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2619) ∨ (¬ p2651) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4385) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14722 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule25466 (meaning t m 2027) (meaning t m 2136) (meaning t m 2417) (meaning t m 2437) (meaning t m 2619) (meaning t m 2651) (meaning t m 3951) (meaning t m 4120) (meaning t m 4385) (meaning t m 4786) source

theorem rule25468 (p3146 p3609 p4740 : Prop) (h : (¬ p4740) ∨ (¬ p3609) ∨ p3146) : (p3146) ∨ (¬ p3609) ∨ (¬ p4740) := by
  classical
  tauto

theorem initial25468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3146) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4740)) := by
  have source := ElevenTheory.theory14724 (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule25468 (meaning t m 3146) (meaning t m 3609) (meaning t m 4740) source

theorem rule25469 (p2663 p4104 p5201 : Prop) (h : (¬ p2663) ∨ (¬ p5201) ∨ p4104) : (¬ p2663) ∨ (p4104) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial25469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (meaning t m 4104) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory14725 (m.theta 0 3) (m.theta 0 4) (m.theta 0 7)
  exact rule25469 (meaning t m 2663) (meaning t m 4104) (meaning t m 5201) source

theorem rule25470 (p2027 p3246 p3568 p3872 p4107 p4564 : Prop) (h : (¬ p3568) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4564) ∨ (¬ p4107)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14726 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule25470 (meaning t m 2027) (meaning t m 3246) (meaning t m 3568) (meaning t m 3872) (meaning t m 4107) (meaning t m 4564) source

theorem rule25471 (p2027 p2427 p2608 p2819 p2829 p3556 p3880 p4134 p4524 : Prop) (h : (¬ p4134) ∨ (¬ p3556) ∨ (¬ p2829) ∨ (¬ p3880) ∨ (¬ p2819) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4524)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14727 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule25471 (meaning t m 2027) (meaning t m 2427) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 3556) (meaning t m 3880) (meaning t m 4134) (meaning t m 4524) source

theorem rule25472 (p2027 p2187 p2641 p4360 p4564 p4769 : Prop) (h : (¬ p4564) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4769)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4564) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial25472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory14728 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule25472 (meaning t m 2027) (meaning t m 2187) (meaning t m 2641) (meaning t m 4360) (meaning t m 4564) (meaning t m 4769) source

theorem rule25473 (p2027 p2156 p2187 p2363 p2928 p3452 p4278 p4521 p4669 : Prop) (h : (¬ p4521) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2187) ∨ (¬ p4278) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4521) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial25473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14729 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25473 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4521) (meaning t m 4669) source

theorem rule25475 (p2027 p2363 p2748 p2819 p2829 p2996 p3365 p3947 p4669 p4734 : Prop) (h : (¬ p2996) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2748) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14731 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25475 (meaning t m 2027) (meaning t m 2363) (meaning t m 2748) (meaning t m 2819) (meaning t m 2829) (meaning t m 2996) (meaning t m 3365) (meaning t m 3947) (meaning t m 4669) (meaning t m 4734) source

theorem rule25476 (p2027 p2295 p2331 p3055 p3791 p4425 p4786 p4826 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3055) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p4826) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p4826) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial25476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14732 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule25476 (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 3055) (meaning t m 3791) (meaning t m 4425) (meaning t m 4786) (meaning t m 4826) (meaning t m 5160) source

theorem rule25478 (p2027 p2139 p2156 p2274 p2396 p3266 p3346 p3905 p3950 p5164 p5387 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p5387) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3905) ∨ (¬ p2139) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p5164)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3905) ∨ (¬ p3950) ∨ (¬ p5164) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial25478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory14734 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25478 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 3266) (meaning t m 3346) (meaning t m 3905) (meaning t m 3950) (meaning t m 5164) (meaning t m 5387) source

theorem rule25479 (p2027 p2177 p2295 p2331 p3055 p3876 p4278 p4666 p4786 : Prop) (h : (¬ p3055) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4278) ∨ (¬ p4786) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14735 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25479 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) (meaning t m 4666) (meaning t m 4786) source

theorem rule25480 (p2027 p2132 p2619 p2753 p3146 p3379 p3817 p4366 p4669 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p2753) ∨ (¬ p4366) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2132) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14736 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25480 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2753) (meaning t m 3146) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) (meaning t m 5216) source

theorem rule25481 (p2027 p2132 p2619 p2753 p2761 p3146 p3346 p3347 p4425 p4669 p5216 : Prop) (h : (¬ p2619) ∨ (¬ p3346) ∨ (¬ p2132) ∨ (¬ p2761) ∨ (¬ p4425) ∨ (¬ p3146) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3146) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p4425) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14737 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25481 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2753) (meaning t m 2761) (meaning t m 3146) (meaning t m 3346) (meaning t m 3347) (meaning t m 4425) (meaning t m 4669) (meaning t m 5216) source

theorem rule25482 (p2027 p2246 p2313 p2553 p2577 p2619 p2749 p2946 p3146 p3347 p4137 p4316 p4396 p4669 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p4316) ∨ (¬ p4669) ∨ (¬ p3146) ∨ (¬ p2619) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2313) ∨ (¬ p4396) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2619) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p4316) ∨ (¬ p4396) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14738 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule25482 (meaning t m 2027) (meaning t m 2246) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2619) (meaning t m 2749) (meaning t m 2946) (meaning t m 3146) (meaning t m 3347) (meaning t m 4137) (meaning t m 4316) (meaning t m 4396) (meaning t m 4669) (meaning t m 5216) source

theorem rule25484 (p2027 p2696 p2753 p2761 p3005 p3256 p3346 p3347 p4425 p4669 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p3256) ∨ (¬ p4425) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p4425) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14740 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25484 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2761) (meaning t m 3005) (meaning t m 3256) (meaning t m 3346) (meaning t m 3347) (meaning t m 4425) (meaning t m 4669) (meaning t m 5216) source

theorem rule25485 (p2027 p2313 p2553 p2577 p2696 p2753 p3005 p3256 p3347 p4137 p4604 p5216 : Prop) (h : p2027 ∨ (¬ p2553) ∨ (¬ p2313) ∨ (¬ p3256) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p2696) ∨ (¬ p5216) ∨ (¬ p2577) ∨ (¬ p2753) ∨ (¬ p4604) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial25485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14741 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule25485 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3347) (meaning t m 4137) (meaning t m 4604) (meaning t m 5216) source

theorem rule25487 (p2027 p2528 p2598 p3549 p3591 p3641 p4107 p4669 p4733 : Prop) (h : (¬ p3549) ∨ (¬ p2598) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4107) ∨ (¬ p3641) ∨ (¬ p4733) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14743 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25487 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 3549) (meaning t m 3591) (meaning t m 3641) (meaning t m 4107) (meaning t m 4669) (meaning t m 4733) source

theorem rule25488 (p2027 p2249 p2387 p2641 p2668 p3983 : Prop) (h : (¬ p3983) ∨ (¬ p2668) ∨ (¬ p2387) ∨ (¬ p2641) ∨ (¬ p2249) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p2387) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial25488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory14744 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8)
  exact rule25488 (meaning t m 2027) (meaning t m 2249) (meaning t m 2387) (meaning t m 2641) (meaning t m 2668) (meaning t m 3983) source

theorem rule25489 (p2027 p2191 p2249 p2264 p2459 p2657 p3027 p3487 p4202 p5118 p5568 : Prop) (h : (¬ p2657) ∨ (¬ p2459) ∨ (¬ p5118) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p4202) ∨ (¬ p2264) ∨ (¬ p3487) ∨ (¬ p3027) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2249) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3487) ∨ (¬ p4202) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial25489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory14745 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25489 (meaning t m 2027) (meaning t m 2191) (meaning t m 2249) (meaning t m 2264) (meaning t m 2459) (meaning t m 2657) (meaning t m 3027) (meaning t m 3487) (meaning t m 4202) (meaning t m 5118) (meaning t m 5568) source

theorem rule25490 (p2027 p2249 p2579 p2655 p2727 p3016 : Prop) (h : (¬ p2249) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2727) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial25490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory14746 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6)
  exact rule25490 (meaning t m 2027) (meaning t m 2249) (meaning t m 2579) (meaning t m 2655) (meaning t m 2727) (meaning t m 3016) source

theorem rule25493 (p2027 p2696 p2928 p3005 p3256 p3452 p4278 p4669 p4733 : Prop) (h : (¬ p4733) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p4669) ∨ (¬ p4278) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2928) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14749 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25493 (meaning t m 2027) (meaning t m 2696) (meaning t m 2928) (meaning t m 3005) (meaning t m 3256) (meaning t m 3452) (meaning t m 4278) (meaning t m 4669) (meaning t m 4733) source

theorem rule25494 (p1979 p2027 p2187 p2387 p2667 p2765 p3136 p4195 : Prop) (h : (¬ p1979) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4195) ∨ (¬ p3136) ∨ (¬ p2667) ∨ p2765) : (¬ p1979) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (p2765) ∨ (¬ p3136) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial25494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory14750 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule25494 (meaning t m 1979) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2667) (meaning t m 2765) (meaning t m 3136) (meaning t m 4195) source

theorem rule25495 (p1999 p2027 p2249 p2641 p2657 p2764 p3125 p3193 p3487 p4228 p4393 p4425 : Prop) (h : (¬ p4228) ∨ (¬ p2249) ∨ (¬ p4425) ∨ (¬ p3193) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p3487) ∨ (¬ p4393) ∨ p2764 ∨ (¬ p1999) ∨ (¬ p2657) ∨ (¬ p3125)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p3125) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p4228) ∨ (¬ p4393) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial25495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory14751 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 10) (m.theta 6 9) (m.theta 9 10)
  exact rule25495 (meaning t m 1999) (meaning t m 2027) (meaning t m 2249) (meaning t m 2641) (meaning t m 2657) (meaning t m 2764) (meaning t m 3125) (meaning t m 3193) (meaning t m 3487) (meaning t m 4228) (meaning t m 4393) (meaning t m 4425) source

theorem rule25496 (p2027 p2156 p2187 p2249 p2459 p2951 p2992 p3172 p4133 p4261 p4288 : Prop) (h : p2027 ∨ (¬ p2187) ∨ (¬ p3172) ∨ (¬ p2156) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2249) ∨ (¬ p4261) ∨ (¬ p4288)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2249) ∨ (¬ p2459) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3172) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial25496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory14752 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25496 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2249) (meaning t m 2459) (meaning t m 2951) (meaning t m 2992) (meaning t m 3172) (meaning t m 4133) (meaning t m 4261) (meaning t m 4288) source

theorem rule25497 (p2027 p2247 p2363 p2774 p2819 p2996 p3947 p4669 p4733 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4733) ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2996) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14753 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25497 (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 2996) (meaning t m 3947) (meaning t m 4669) (meaning t m 4733) source

theorem rule25501 (p1975 p2299 p3498 p4438 : Prop) (h : p3498 ∨ p4438 ∨ (¬ p1975) ∨ (¬ p2299)) : (¬ p1975) ∨ (¬ p2299) ∨ (p3498) ∨ (p4438) := by
  classical
  tauto

theorem initial25501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 3498) ∨ (meaning t m 4438) := by
  have source := ElevenTheory.theory14757 t (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule25501 (meaning t m 1975) (meaning t m 2299) (meaning t m 3498) (meaning t m 4438) source

theorem rule25502 (p2027 p2132 p2619 p2928 p3146 p3452 p4278 p4669 p4733 : Prop) (h : (¬ p2132) ∨ (¬ p3146) ∨ (¬ p4733) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2928) ∨ (¬ p4278) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2928) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14758 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25502 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2928) (meaning t m 3146) (meaning t m 3452) (meaning t m 4278) (meaning t m 4669) (meaning t m 4733) source

theorem rule25506 (p2663 p4419 p4786 : Prop) (h : (¬ p4786) ∨ (¬ p2663) ∨ p4419) : (¬ p2663) ∨ (p4419) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (meaning t m 4419) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14762 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4)
  exact rule25506 (meaning t m 2663) (meaning t m 4419) (meaning t m 4786) source

theorem rule25507 (p2509 p2928 p3875 : Prop) (h : (¬ p3875) ∨ (¬ p2509) ∨ p2928) : (¬ p2509) ∨ (p2928) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial25507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (meaning t m 2928) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory14763 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule25507 (meaning t m 2509) (meaning t m 2928) (meaning t m 3875) source

theorem rule25508 (p2027 p2177 p2249 p2307 p2641 p2657 p2928 p3487 p3567 p4278 p4666 : Prop) (h : (¬ p2657) ∨ (¬ p2928) ∨ (¬ p2307) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p3487) ∨ (¬ p2249) ∨ (¬ p3567) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial25508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory14764 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25508 (meaning t m 2027) (meaning t m 2177) (meaning t m 2249) (meaning t m 2307) (meaning t m 2641) (meaning t m 2657) (meaning t m 2928) (meaning t m 3487) (meaning t m 3567) (meaning t m 4278) (meaning t m 4666) source

theorem rule25509 (p2027 p2191 p2249 p2641 p2952 p3323 p3461 p4282 p5123 p5568 : Prop) (h : (¬ p2191) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p5568) ∨ (¬ p2952) ∨ (¬ p4282) ∨ (¬ p3323) ∨ (¬ p5123) ∨ (¬ p2249) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p4282) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial25509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory14765 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25509 (meaning t m 2027) (meaning t m 2191) (meaning t m 2249) (meaning t m 2641) (meaning t m 2952) (meaning t m 3323) (meaning t m 3461) (meaning t m 4282) (meaning t m 5123) (meaning t m 5568) source

theorem rule25512 (p2685 p3755 p4661 : Prop) (h : (¬ p4661) ∨ (¬ p2685) ∨ p3755) : (¬ p2685) ∨ (p3755) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial25512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (meaning t m 3755) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory14768 (m.theta 2 3) (m.theta 3 7) (m.theta 3 9)
  exact rule25512 (meaning t m 2685) (meaning t m 3755) (meaning t m 4661) source

theorem rule25513 (p1998 p2027 p2764 p2881 p2963 p3471 p4037 p4191 p4253 p4789 p5660 : Prop) (h : (¬ p1998) ∨ p2764 ∨ (¬ p2881) ∨ (¬ p3471) ∨ (¬ p5660) ∨ (¬ p4253) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p4037) ∨ (¬ p2963)) : (¬ p1998) ∨ (p2027) ∨ (p2764) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p3471) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4789) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial25513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory14769 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule25513 (meaning t m 1998) (meaning t m 2027) (meaning t m 2764) (meaning t m 2881) (meaning t m 2963) (meaning t m 3471) (meaning t m 4037) (meaning t m 4191) (meaning t m 4253) (meaning t m 4789) (meaning t m 5660) source

theorem rule25514 (p1997 p2027 p2850 p2997 p3362 p3389 p3568 p3591 p3876 p4228 p4435 p4733 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p4228) ∨ (¬ p3568) ∨ (¬ p3362) ∨ (¬ p1997) ∨ (¬ p2850) ∨ (¬ p4733) ∨ (¬ p3876) ∨ (¬ p3389) ∨ (¬ p3591) ∨ (¬ p4435)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2850) ∨ (p2997) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p3876) ∨ (¬ p4228) ∨ (¬ p4435) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14770 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 10) (m.theta 6 7)
  exact rule25514 (meaning t m 1997) (meaning t m 2027) (meaning t m 2850) (meaning t m 2997) (meaning t m 3362) (meaning t m 3389) (meaning t m 3568) (meaning t m 3591) (meaning t m 3876) (meaning t m 4228) (meaning t m 4435) (meaning t m 4733) source

theorem rule25516 (p2027 p2249 p3073 p3172 p3859 p4118 : Prop) (h : (¬ p3172) ∨ (¬ p3073) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p3859)) : (p2027) ∨ (¬ p2249) ∨ (¬ p3073) ∨ (¬ p3172) ∨ (¬ p3859) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial25516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory14772 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule25516 (meaning t m 2027) (meaning t m 2249) (meaning t m 3073) (meaning t m 3172) (meaning t m 3859) (meaning t m 4118) source

theorem rule25517 (p1976 p2027 p2633 p2737 p3365 p3553 p3588 p4777 : Prop) (h : (¬ p1976) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2737) ∨ (¬ p4777) ∨ p2633 ∨ (¬ p3553)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3588) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial25517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory14773 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule25517 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 2737) (meaning t m 3365) (meaning t m 3553) (meaning t m 3588) (meaning t m 4777) source

theorem rule25518 (p2027 p2528 p2598 p3486 p3555 p3641 p3690 p4669 p4733 : Prop) (h : (¬ p2528) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3690) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4733) ∨ (¬ p3641) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14774 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule25518 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 3486) (meaning t m 3555) (meaning t m 3641) (meaning t m 3690) (meaning t m 4669) (meaning t m 4733) source

theorem rule25519 (p2027 p2249 p2341 p2657 p3027 p3193 p3487 p3941 p4066 p4425 p5119 : Prop) (h : (¬ p3027) ∨ (¬ p3487) ∨ (¬ p3193) ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p4066)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p3941) ∨ (¬ p4066) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14775 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25519 (meaning t m 2027) (meaning t m 2249) (meaning t m 2341) (meaning t m 2657) (meaning t m 3027) (meaning t m 3193) (meaning t m 3487) (meaning t m 3941) (meaning t m 4066) (meaning t m 4425) (meaning t m 5119) source

theorem rule25522 (p2996 p3662 p4386 : Prop) (h : (¬ p3662) ∨ (¬ p4386) ∨ p2996) : (p2996) ∨ (¬ p3662) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial25522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2996) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory14778 (m.theta 1 3) (m.theta 3 5) (m.theta 3 7)
  exact rule25522 (meaning t m 2996) (meaning t m 3662) (meaning t m 4386) source

theorem rule25523 (p2027 p2363 p2774 p2819 p3486 p3555 p3690 p4669 p4733 : Prop) (h : (¬ p3486) ∨ (¬ p4733) ∨ (¬ p2819) ∨ (¬ p3690) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2774) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial25523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory14779 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25523 (meaning t m 2027) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4669) (meaning t m 4733) source

theorem rule25525 (p1988 p2027 p2249 p2963 p2997 p3027 p3097 p3276 p3333 p3686 p3737 p3922 p4325 p4435 : Prop) (h : p4325 ∨ (¬ p3097) ∨ (¬ p3333) ∨ (¬ p3027) ∨ p2997 ∨ (¬ p3737) ∨ (¬ p4435) ∨ (¬ p3276) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p3686) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2249)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2249) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3686) ∨ (¬ p3737) ∨ (¬ p3922) ∨ (p4325) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial25525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3922)) ∨ (meaning t m 4325) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory14781 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 3 7) (m.theta 4 9) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7) (m.theta 9 10)
  exact rule25525 (meaning t m 1988) (meaning t m 2027) (meaning t m 2249) (meaning t m 2963) (meaning t m 2997) (meaning t m 3027) (meaning t m 3097) (meaning t m 3276) (meaning t m 3333) (meaning t m 3686) (meaning t m 3737) (meaning t m 3922) (meaning t m 4325) (meaning t m 4435) source

theorem rule25527 (p2005 p2027 p2249 p2474 p2657 p2764 p3189 p3193 p3256 p3363 p3422 p3487 p3857 p4022 p4191 : Prop) (h : p2027 ∨ (¬ p2005) ∨ (¬ p3363) ∨ (¬ p3422) ∨ (¬ p3487) ∨ (¬ p4022) ∨ (¬ p2657) ∨ (¬ p2474) ∨ (¬ p4191) ∨ (¬ p3857) ∨ (¬ p3193) ∨ (¬ p2249) ∨ p2764 ∨ (¬ p3189) ∨ (¬ p3256)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2249) ∨ (¬ p2474) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p3189) ∨ (¬ p3193) ∨ (¬ p3256) ∨ (¬ p3363) ∨ (¬ p3422) ∨ (¬ p3487) ∨ (¬ p3857) ∨ (¬ p4022) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial25527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory14783 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 8) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25527 (meaning t m 2005) (meaning t m 2027) (meaning t m 2249) (meaning t m 2474) (meaning t m 2657) (meaning t m 2764) (meaning t m 3189) (meaning t m 3193) (meaning t m 3256) (meaning t m 3363) (meaning t m 3422) (meaning t m 3487) (meaning t m 3857) (meaning t m 4022) (meaning t m 4191) source

theorem rule25528 (p2027 p2249 p2881 p2951 p2963 p2992 p3051 p3549 p3922 p4107 p4666 : Prop) (h : (¬ p2881) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p4666) ∨ (¬ p3051) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial25528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory14784 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25528 (meaning t m 2027) (meaning t m 2249) (meaning t m 2881) (meaning t m 2951) (meaning t m 2963) (meaning t m 2992) (meaning t m 3051) (meaning t m 3549) (meaning t m 3922) (meaning t m 4107) (meaning t m 4666) source

theorem rule25530 (p2027 p2187 p2284 p2387 p2954 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p2187) ∨ (¬ p2954) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2387) ∨ (¬ p2954) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial25530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory14786 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule25530 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2387) (meaning t m 2954) (meaning t m 4198) source

theorem rule25531 (p2027 p2187 p3422 p3874 p3958 p4432 : Prop) (h : (¬ p3422) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3958) ∨ (¬ p4432) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3958) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial25531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory14787 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule25531 (meaning t m 2027) (meaning t m 2187) (meaning t m 3422) (meaning t m 3874) (meaning t m 3958) (meaning t m 4432) source

theorem rule25532 (p1982 p2027 p2202 p2220 p2363 p2563 p3646 p4441 : Prop) (h : (¬ p3646) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p4441) ∨ (¬ p2363) ∨ (¬ p2220)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2220) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial25532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory14788 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule25532 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2220) (meaning t m 2363) (meaning t m 2563) (meaning t m 3646) (meaning t m 4441) source

theorem rule25533 (p1984 p2247 p2688 p2811 p4790 : Prop) (h : p2688 ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p2811) ∨ p4790) : (¬ p1984) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2811) ∨ (p4790) := by
  classical
  tauto

theorem initial25533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2811)) ∨ (meaning t m 4790) := by
  have source := ElevenTheory.theory14789 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule25533 (meaning t m 1984) (meaning t m 2247) (meaning t m 2688) (meaning t m 2811) (meaning t m 4790) source

theorem rule25536 (p2027 p2245 p2608 p2641 p2744 p2963 : Prop) (h : p2027 ∨ (¬ p2245) ∨ (¬ p2744) ∨ (¬ p2963) ∨ (¬ p2608) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2744) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial25536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory14792 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6)
  exact rule25536 (meaning t m 2027) (meaning t m 2245) (meaning t m 2608) (meaning t m 2641) (meaning t m 2744) (meaning t m 2963) source

theorem rule25537 (p2027 p2608 p3367 p3555 p4418 p4881 : Prop) (h : (¬ p2608) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p4881) ∨ (¬ p4418)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3555) ∨ (¬ p4418) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial25537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory14793 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5)
  exact rule25537 (meaning t m 2027) (meaning t m 2608) (meaning t m 3367) (meaning t m 3555) (meaning t m 4418) (meaning t m 4881) source

theorem rule25539 (p2027 p3192 p3276 p4107 p4381 p4712 : Prop) (h : (¬ p4381) ∨ (¬ p4712) ∨ (¬ p3276) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3192)) : (p2027) ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial25539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory14795 t (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule25539 (meaning t m 2027) (meaning t m 3192) (meaning t m 3276) (meaning t m 4107) (meaning t m 4381) (meaning t m 4712) source

theorem rule25540 (p2662 p2663 p2952 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2662) ∨ (¬ p2952) ∨ (¬ p2663)) : (¬ p2662) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial25540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory14796 (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5)
  exact rule25540 (meaning t m 2662) (meaning t m 2663) (meaning t m 2952) (meaning t m 3413) source

theorem rule25541 (p2027 p2363 p3325 p3570 p4348 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p3325) ∨ (¬ p4348) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial25541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory14797 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25541 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3570) (meaning t m 4348) (meaning t m 4556) source

theorem rule25544 (p2010 p2545 p2922 p4811 : Prop) (h : (¬ p2010) ∨ p2545 ∨ (¬ p2922) ∨ p4811) : (¬ p2010) ∨ (p2545) ∨ (¬ p2922) ∨ (p4811) := by
  classical
  tauto

theorem initial25544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 4811) := by
  have source := ElevenTheory.theory14800 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule25544 (meaning t m 2010) (meaning t m 2545) (meaning t m 2922) (meaning t m 4811) source

theorem rule25546 (p2027 p3115 p4135 p4277 p4278 p4320 : Prop) (h : (¬ p4278) ∨ (¬ p4277) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p4135)) : (p2027) ∨ (¬ p3115) ∨ (¬ p4135) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial25546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory14802 t (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule25546 (meaning t m 2027) (meaning t m 3115) (meaning t m 4135) (meaning t m 4277) (meaning t m 4278) (meaning t m 4320) source

theorem rule25547 (p2027 p2499 p2573 p2922 p3365 p4079 p4277 p4315 p4320 p4736 : Prop) (h : (¬ p4079) ∨ (¬ p4315) ∨ (¬ p2922) ∨ (¬ p2499) ∨ (¬ p4736) ∨ (¬ p4320) ∨ (¬ p4277) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2922) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4277) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14803 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7)
  exact rule25547 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2922) (meaning t m 3365) (meaning t m 4079) (meaning t m 4277) (meaning t m 4315) (meaning t m 4320) (meaning t m 4736) source

theorem rule25548 (p2027 p2573 p3362 p3584 p3585 p4737 : Prop) (h : (¬ p3585) ∨ (¬ p4737) ∨ (¬ p2573) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p3584)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory14804 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6)
  exact rule25548 (meaning t m 2027) (meaning t m 2573) (meaning t m 3362) (meaning t m 3584) (meaning t m 3585) (meaning t m 4737) source

theorem rule25549 (p2717 p3548 p3576 : Prop) (h : (¬ p2717) ∨ (¬ p3576) ∨ (¬ p3548)) : (¬ p2717) ∨ (¬ p3548) ∨ (¬ p3576) := by
  classical
  tauto

theorem initial25549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) := by
  have source := ElevenTheory.theory14805 (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule25549 (meaning t m 2717) (meaning t m 3548) (meaning t m 3576) source

theorem rule25554 (p2027 p2241 p2406 p2589 p2750 p3541 p4108 : Prop) (h : (¬ p2750) ∨ p2027 ∨ (¬ p3541) ∨ (¬ p2406) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial25554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory14810 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5)
  exact rule25554 (meaning t m 2027) (meaning t m 2241) (meaning t m 2406) (meaning t m 2589) (meaning t m 2750) (meaning t m 3541) (meaning t m 4108) source

theorem rule25555 (p2027 p2132 p2247 p2744 p3583 p3589 : Prop) (h : (¬ p2744) ∨ (¬ p3589) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3583) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial25555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory14811 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5)
  exact rule25555 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2744) (meaning t m 3583) (meaning t m 3589) source

theorem rule25557 (p2027 p2860 p3125 p4026 p4512 p4875 : Prop) (h : (¬ p4512) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4875) ∨ (¬ p2860) ∨ p2027) : (p2027) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial25557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory14813 t (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9)
  exact rule25557 (meaning t m 2027) (meaning t m 2860) (meaning t m 3125) (meaning t m 4026) (meaning t m 4512) (meaning t m 4875) source

theorem rule25558 (p2027 p2284 p3136 p3572 p3699 p4555 : Prop) (h : (¬ p2284) ∨ (¬ p3699) ∨ (¬ p4555) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p3136)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3699) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial25558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory14814 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule25558 (meaning t m 2027) (meaning t m 2284) (meaning t m 3136) (meaning t m 3572) (meaning t m 3699) (meaning t m 4555) source

theorem rule25564 (p2027 p2247 p2341 p2744 p3545 p3548 p4400 : Prop) (h : (¬ p3545) ∨ (¬ p2341) ∨ (¬ p4400) ∨ (¬ p3548) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2744)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2341) ∨ (¬ p2744) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial25564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory14820 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 7 8)
  exact rule25564 (meaning t m 2027) (meaning t m 2247) (meaning t m 2341) (meaning t m 2744) (meaning t m 3545) (meaning t m 3548) (meaning t m 4400) source

theorem rule25566 (p2027 p2383 p2779 p3550 p3553 p3822 p4333 p4556 : Prop) (h : (¬ p3553) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p4333) ∨ (¬ p3550) ∨ (¬ p3822) ∨ (¬ p2383) ∨ (¬ p2779)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2779) ∨ (¬ p3550) ∨ (¬ p3553) ∨ (¬ p3822) ∨ (¬ p4333) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial25566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory14822 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule25566 (meaning t m 2027) (meaning t m 2383) (meaning t m 2779) (meaning t m 3550) (meaning t m 3553) (meaning t m 3822) (meaning t m 4333) (meaning t m 4556) source

theorem rule25567 (p2027 p2313 p2383 p3550 p3553 p4333 p4556 : Prop) (h : (¬ p3553) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p4333) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3553) ∨ (¬ p4333) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial25567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory14823 t (m.theta 0 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule25567 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3550) (meaning t m 3553) (meaning t m 4333) (meaning t m 4556) source

theorem rule25568 (p2027 p2230 p2247 p2744 p3238 p4079 p4257 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3238) ∨ (¬ p2247) ∨ (¬ p4079) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial25568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory14824 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5)
  exact rule25568 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2744) (meaning t m 3238) (meaning t m 4079) (meaning t m 4257) source

theorem rule25569 (p4118 p4340 p4967 : Prop) (h : (¬ p4340) ∨ (¬ p4967) ∨ p4118) : (p4118) ∨ (¬ p4340) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial25569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4118) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory14825 (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule25569 (meaning t m 4118) (meaning t m 4340) (meaning t m 4967) source

theorem rule25580 (p2027 p2341 p3545 p3548 p3555 p4377 p4400 : Prop) (h : (¬ p4400) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3545) ∨ (¬ p4377)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p3555) ∨ (¬ p4377) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial25580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory14836 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 7 8)
  exact rule25580 (meaning t m 2027) (meaning t m 2341) (meaning t m 3545) (meaning t m 3548) (meaning t m 3555) (meaning t m 4377) (meaning t m 4400) source

theorem rule25582 (p3545 p4590 p5242 : Prop) (h : (¬ p4590) ∨ (¬ p3545) ∨ p5242) : (¬ p3545) ∨ (¬ p4590) ∨ (p5242) := by
  classical
  tauto

theorem initial25582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 4590)) ∨ (meaning t m 5242) := by
  have source := ElevenTheory.theory14838 (m.theta 0 1) (m.theta 0 7) (m.theta 0 8)
  exact rule25582 (meaning t m 3545) (meaning t m 4590) (meaning t m 5242) source

theorem rule25586 (p1982 p2027 p2696 p2699 p2743 p3256 p3537 p3589 p4967 : Prop) (h : (¬ p1982) ∨ p2699 ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3256) ∨ (¬ p3589) ∨ (¬ p2696) ∨ (¬ p4967) ∨ (¬ p3537)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p3256) ∨ (¬ p3537) ∨ (¬ p3589) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial25586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory14842 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule25586 (meaning t m 1982) (meaning t m 2027) (meaning t m 2696) (meaning t m 2699) (meaning t m 2743) (meaning t m 3256) (meaning t m 3537) (meaning t m 3589) (meaning t m 4967) source

theorem rule25589 (p2656 p3683 p3759 : Prop) (h : p3759 ∨ (¬ p2656) ∨ (¬ p3683)) : (¬ p2656) ∨ (¬ p3683) ∨ (p3759) := by
  classical
  tauto

theorem initial25589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3683)) ∨ (meaning t m 3759) := by
  have source := ElevenTheory.theory14845 (m.theta 0 4) (m.theta 2 4) (m.theta 3 4)
  exact rule25589 (meaning t m 2656) (meaning t m 3683) (meaning t m 3759) source

theorem rule25590 (p2027 p2156 p2274 p3549 p4512 p4525 : Prop) (h : p2027 ∨ (¬ p4525) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p2156) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4525) := by
  classical
  tauto

theorem initial25590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4525)) := by
  have source := ElevenTheory.theory14846 t (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule25590 (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 3549) (meaning t m 4512) (meaning t m 4525) source

theorem rule25595 (p1975 p2027 p2295 p2459 p2633 p3324 p4347 : Prop) (h : (¬ p1975) ∨ (¬ p4347) ∨ p2633 ∨ (¬ p2459) ∨ (¬ p2295) ∨ (¬ p3324) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3324) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial25595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory14851 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25595 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2459) (meaning t m 2633) (meaning t m 3324) (meaning t m 4347) source

theorem rule25597 (p3125 p3322 p3324 p3986 : Prop) (h : (¬ p3324) ∨ (¬ p3986) ∨ (¬ p3125) ∨ (¬ p3322)) : (¬ p3125) ∨ (¬ p3322) ∨ (¬ p3324) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial25597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory14853 (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule25597 (meaning t m 3125) (meaning t m 3322) (meaning t m 3324) (meaning t m 3986) source

theorem rule25601 (p3692 p3969 p5116 : Prop) (h : (¬ p3969) ∨ (¬ p5116) ∨ (¬ p3692)) : (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5116) := by
  classical
  tauto

theorem initial25601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5116)) := by
  have source := ElevenTheory.theory14857 (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25601 (meaning t m 3692) (meaning t m 3969) (meaning t m 5116) source

theorem rule25604 (p1975 p2027 p2233 p2295 p2352 p2573 p3324 : Prop) (h : (¬ p3324) ∨ (¬ p2295) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p1975) ∨ p2233 ∨ (¬ p2352)) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2295) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial25604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory14860 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25604 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2295) (meaning t m 2352) (meaning t m 2573) (meaning t m 3324) source

theorem rule25605 (p2651 p2963 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2963) ∨ (¬ p2651)) : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial25605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory14861 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule25605 (meaning t m 2651) (meaning t m 2963) (meaning t m 3019) source

theorem rule25607 (p2027 p2696 p2741 p3005 p4360 p4737 : Prop) (h : p2027 ∨ (¬ p2696) ∨ (¬ p4737) ∨ (¬ p4360) ∨ (¬ p2741) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p3005) ∨ (¬ p4360) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory14863 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 8)
  exact rule25607 (meaning t m 2027) (meaning t m 2696) (meaning t m 2741) (meaning t m 3005) (meaning t m 4360) (meaning t m 4737) source

theorem rule25610 (p3063 p3527 p3550 p4105 : Prop) (h : (¬ p3550) ∨ (¬ p4105) ∨ (¬ p3063) ∨ p3527) : (¬ p3063) ∨ (p3527) ∨ (¬ p3550) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial25610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3063)) ∨ (meaning t m 3527) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory14866 (m.theta 1 6) (m.theta 1 7) (m.theta 6 8) (m.theta 7 8)
  exact rule25610 (meaning t m 3063) (meaning t m 3527) (meaning t m 3550) (meaning t m 4105) source

theorem rule25612 (p2027 p2191 p2220 p2247 p4172 p4959 : Prop) (h : (¬ p2247) ∨ (¬ p2191) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p4172) ∨ (¬ p4959)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2247) ∨ (¬ p4172) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial25612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory14868 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8)
  exact rule25612 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2247) (meaning t m 4172) (meaning t m 4959) source

theorem rule25613 (p1976 p2027 p2765 p3115 p3365 p3952 p4385 p4392 : Prop) (h : (¬ p3365) ∨ (¬ p4392) ∨ (¬ p4385) ∨ (¬ p1976) ∨ (¬ p3115) ∨ p2027 ∨ p2765 ∨ (¬ p3952)) : (¬ p1976) ∨ (p2027) ∨ (p2765) ∨ (¬ p3115) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4385) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial25613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory14869 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule25613 (meaning t m 1976) (meaning t m 2027) (meaning t m 2765) (meaning t m 3115) (meaning t m 3365) (meaning t m 3952) (meaning t m 4385) (meaning t m 4392) source

theorem rule25614 (p2027 p2247 p2307 p2744 p3549 p4512 p4874 p5020 : Prop) (h : (¬ p4874) ∨ (¬ p2744) ∨ (¬ p5020) ∨ (¬ p4512) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2744) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4874) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial25614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory14870 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 6 7)
  exact rule25614 (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2744) (meaning t m 3549) (meaning t m 4512) (meaning t m 4874) (meaning t m 5020) source

theorem rule25616 (p2573 p3759 p3876 p3920 : Prop) (h : (¬ p2573) ∨ (¬ p3759) ∨ (¬ p3920) ∨ (¬ p3876)) : (¬ p2573) ∨ (¬ p3759) ∨ (¬ p3876) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial25616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory14872 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule25616 (meaning t m 2573) (meaning t m 3759) (meaning t m 3876) (meaning t m 3920) source

theorem rule25617 (p2027 p2386 p2499 p2901 p2962 p3413 p3556 p4811 : Prop) (h : (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3413) ∨ (¬ p4811) ∨ p2027 ∨ (¬ p2962)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p2962) ∨ (¬ p3413) ∨ (¬ p3556) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial25617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory14873 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7)
  exact rule25617 (meaning t m 2027) (meaning t m 2386) (meaning t m 2499) (meaning t m 2901) (meaning t m 2962) (meaning t m 3413) (meaning t m 3556) (meaning t m 4811) source

theorem rule25619 (p2027 p3365 p3399 p3527 p3568 p3570 p4195 p4556 p4736 : Prop) (h : (¬ p4556) ∨ (¬ p4736) ∨ (¬ p3399) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p4195) ∨ (¬ p3568) ∨ (¬ p3365)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4195) ∨ (¬ p4556) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory14875 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25619 (meaning t m 2027) (meaning t m 3365) (meaning t m 3399) (meaning t m 3527) (meaning t m 3568) (meaning t m 3570) (meaning t m 4195) (meaning t m 4556) (meaning t m 4736) source

theorem rule25627 (p1975 p2027 p2192 p2210 p2299 p2699 p2881 p3872 : Prop) (h : (¬ p2881) ∨ (¬ p1975) ∨ p2699 ∨ (¬ p2192) ∨ (¬ p3872) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2210)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2299) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial25627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory14883 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25627 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2299) (meaning t m 2699) (meaning t m 2881) (meaning t m 3872) source

theorem rule25628 (p2027 p2245 p2608 p2744 p2952 p2992 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2245) ∨ (¬ p2992) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2952) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial25628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory14884 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5)
  exact rule25628 (meaning t m 2027) (meaning t m 2245) (meaning t m 2608) (meaning t m 2744) (meaning t m 2952) (meaning t m 2992) source

theorem rule25629 (p1984 p2027 p2406 p2509 p2534 p2589 p2766 p4108 : Prop) (h : (¬ p4108) ∨ (¬ p1984) ∨ (¬ p2406) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2509) ∨ p2766) : (¬ p1984) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial25629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory14885 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule25629 (meaning t m 1984) (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2534) (meaning t m 2589) (meaning t m 2766) (meaning t m 4108) source

theorem rule25630 (p2027 p2307 p2962 p3097 p4173 p4525 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4525) ∨ (¬ p4173) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4173) ∨ (¬ p4525) := by
  classical
  tauto

theorem initial25630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4525)) := by
  have source := ElevenTheory.theory14886 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule25630 (meaning t m 2027) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 4173) (meaning t m 4525) source

theorem rule25634 (p2027 p2177 p3055 p3093 p3309 p3684 p3880 p4736 p4905 : Prop) (h : (¬ p3309) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3880) ∨ (¬ p3093) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial25634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory14890 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule25634 (meaning t m 2027) (meaning t m 2177) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3684) (meaning t m 3880) (meaning t m 4736) (meaning t m 4905) source

theorem rule25635 (p1975 p2027 p2210 p2274 p2699 p3063 p3989 p4338 : Prop) (h : p2699 ∨ (¬ p1975) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3063) ∨ (¬ p3989) ∨ (¬ p4338)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3989) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial25635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory14891 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25635 (meaning t m 1975) (meaning t m 2027) (meaning t m 2210) (meaning t m 2274) (meaning t m 2699) (meaning t m 3063) (meaning t m 3989) (meaning t m 4338) source

theorem rule25636 (p1977 p2027 p2417 p2633 p2996 p3644 p3947 : Prop) (h : p2633 ∨ (¬ p3947) ∨ (¬ p2417) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3644) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial25636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory14892 t (m.theta 1 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25636 (meaning t m 1977) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 2996) (meaning t m 3644) (meaning t m 3947) source

theorem rule25639 (p1995 p2027 p2764 p2928 p3346 p3389 p4425 : Prop) (h : (¬ p2928) ∨ p2027 ∨ p2764 ∨ (¬ p4425) ∨ (¬ p1995) ∨ (¬ p3389) ∨ (¬ p3346)) : (¬ p1995) ∨ (p2027) ∨ (p2764) ∨ (¬ p2928) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial25639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory14895 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 9 10)
  exact rule25639 (meaning t m 1995) (meaning t m 2027) (meaning t m 2764) (meaning t m 2928) (meaning t m 3346) (meaning t m 3389) (meaning t m 4425) source

theorem rule25640 (p2449 p3032 p3246 p3571 : Prop) (h : (¬ p3571) ∨ (¬ p3032) ∨ (¬ p3246) ∨ p2449) : (p2449) ∨ (¬ p3032) ∨ (¬ p3246) ∨ (¬ p3571) := by
  classical
  tauto

theorem initial25640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2449) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3571)) := by
  have source := ElevenTheory.theory14896 (m.theta 1 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule25640 (meaning t m 2449) (meaning t m 3032) (meaning t m 3246) (meaning t m 3571) source

theorem rule25641 (p1982 p2027 p2166 p2210 p2533 p2699 p3680 p4444 : Prop) (h : p2699 ∨ (¬ p2210) ∨ (¬ p3680) ∨ (¬ p1982) ∨ (¬ p2533) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p2166)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2533) ∨ (p2699) ∨ (¬ p3680) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial25641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory14897 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25641 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2533) (meaning t m 2699) (meaning t m 3680) (meaning t m 4444) source

theorem rule25643 (p1997 p2027 p2406 p2881 p2928 p2938 p3644 : Prop) (h : p2938 ∨ (¬ p1997) ∨ (¬ p2928) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3644)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2881) ∨ (¬ p2928) ∨ (p2938) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial25643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory14899 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule25643 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2881) (meaning t m 2928) (meaning t m 2938) (meaning t m 3644) source

theorem rule25644 (p2027 p2881 p3212 p3551 p3872 p4984 p5046 : Prop) (h : (¬ p3872) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p4984) ∨ (¬ p3551) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3212) ∨ (¬ p3551) ∨ (¬ p3872) ∨ (¬ p4984) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial25644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4984)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory14900 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule25644 (meaning t m 2027) (meaning t m 2881) (meaning t m 3212) (meaning t m 3551) (meaning t m 3872) (meaning t m 4984) (meaning t m 5046) source

theorem rule25645 (p2027 p2911 p2922 p3553 p4112 p4814 : Prop) (h : (¬ p2922) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p4814) ∨ (¬ p2911) ∨ (¬ p4112)) : (p2027) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial25645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory14901 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule25645 (meaning t m 2027) (meaning t m 2911) (meaning t m 2922) (meaning t m 3553) (meaning t m 4112) (meaning t m 4814) source

theorem rule25649 (p2274 p2307 p2667 p3986 : Prop) (h : (¬ p2274) ∨ (¬ p3986) ∨ (¬ p2667) ∨ p2307) : (¬ p2274) ∨ (p2307) ∨ (¬ p2667) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial25649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (meaning t m 2307) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory14905 (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule25649 (meaning t m 2274) (meaning t m 2307) (meaning t m 2667) (meaning t m 3986) source

theorem rule25654 (p2027 p2138 p2651 p3016 p3564 p3692 p3694 p4330 p4786 : Prop) (h : (¬ p2138) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p4330) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial25654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory14910 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule25654 (meaning t m 2027) (meaning t m 2138) (meaning t m 2651) (meaning t m 3016) (meaning t m 3564) (meaning t m 3692) (meaning t m 3694) (meaning t m 4330) (meaning t m 4786) source

theorem rule25657 (p2027 p2255 p2553 p2651 p2881 p2996 p3016 p3551 p4155 p4559 : Prop) (h : (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2255) ∨ (¬ p2881) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p3016) ∨ (¬ p4155) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3016) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial25657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory14913 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25657 (meaning t m 2027) (meaning t m 2255) (meaning t m 2553) (meaning t m 2651) (meaning t m 2881) (meaning t m 2996) (meaning t m 3016) (meaning t m 3551) (meaning t m 4155) (meaning t m 4559) source

theorem rule25665 (p1982 p2027 p2255 p2518 p2528 p2651 p2667 p2997 p3097 p3125 p3946 p4116 p4154 : Prop) (h : (¬ p3125) ∨ p2997 ∨ (¬ p2667) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p4154) ∨ (¬ p2518) ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p3097) ∨ (¬ p4116) ∨ (¬ p3946)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2255) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4116) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial25665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory14921 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule25665 (meaning t m 1982) (meaning t m 2027) (meaning t m 2255) (meaning t m 2518) (meaning t m 2528) (meaning t m 2651) (meaning t m 2667) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3946) (meaning t m 4116) (meaning t m 4154) source

theorem rule25666 (p2027 p2253 p2299 p2534 p2651 p3097 p3256 p3646 p4121 p4420 p4524 : Prop) (h : (¬ p4121) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4524) ∨ (¬ p3256) ∨ (¬ p2534) ∨ (¬ p4420) ∨ (¬ p3646) ∨ (¬ p2299) ∨ (¬ p3097) ∨ p2027) : (p2027) ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p3256) ∨ (¬ p3646) ∨ (¬ p4121) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial25666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14922 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25666 (meaning t m 2027) (meaning t m 2253) (meaning t m 2299) (meaning t m 2534) (meaning t m 2651) (meaning t m 3097) (meaning t m 3256) (meaning t m 3646) (meaning t m 4121) (meaning t m 4420) (meaning t m 4524) source

theorem rule25670 (p2027 p2299 p2579 p2588 p2608 p2619 p2839 p4902 p5193 : Prop) (h : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2299) ∨ (¬ p4902) ∨ (¬ p5193) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial25670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory14926 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule25670 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 4902) (meaning t m 5193) source

theorem rule25673 (p1991 p2027 p2633 p2641 p2963 p2996 p3553 : Prop) (h : (¬ p2996) ∨ (¬ p1991) ∨ (¬ p3553) ∨ p2027 ∨ p2633 ∨ (¬ p2641) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p2996) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial25673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory14929 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule25673 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 2641) (meaning t m 2963) (meaning t m 2996) (meaning t m 3553) source

theorem rule25678 (p2352 p4358 p4390 : Prop) (h : (¬ p4390) ∨ (¬ p2352) ∨ (¬ p4358)) : (¬ p2352) ∨ (¬ p4358) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial25678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory14934 (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule25678 (meaning t m 2352) (meaning t m 4358) (meaning t m 4390) source

theorem rule25679 (p2027 p2247 p2264 p2744 p3037 p3055 p3366 p3399 p3684 p3880 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p2744) ∨ (¬ p2264) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p2247) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2264) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial25679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory14935 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule25679 (meaning t m 2027) (meaning t m 2247) (meaning t m 2264) (meaning t m 2744) (meaning t m 3037) (meaning t m 3055) (meaning t m 3366) (meaning t m 3399) (meaning t m 3684) (meaning t m 3880) (meaning t m 4905) source

theorem rule25680 (p2027 p2373 p3324 p4110 p4441 p4564 : Prop) (h : (¬ p4110) ∨ (¬ p4564) ∨ (¬ p4441) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3324) ∨ (¬ p4110) ∨ (¬ p4441) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14936 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule25680 (meaning t m 2027) (meaning t m 2373) (meaning t m 3324) (meaning t m 4110) (meaning t m 4441) (meaning t m 4564) source

theorem rule25681 (p2027 p2247 p2534 p2744 p3055 p3366 p3399 p3631 p3874 p3950 : Prop) (h : (¬ p2247) ∨ (¬ p3631) ∨ (¬ p3874) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3950) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3874) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial25681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory14937 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25681 (meaning t m 2027) (meaning t m 2247) (meaning t m 2534) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3874) (meaning t m 3950) source

theorem rule25683 (p1986 p2027 p2774 p3367 p3425 p3437 p3688 : Prop) (h : p2027 ∨ p3437 ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p1986) ∨ (¬ p3367)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2774) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (p3437) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial25683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory14939 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7)
  exact rule25683 (meaning t m 1986) (meaning t m 2027) (meaning t m 2774) (meaning t m 3367) (meaning t m 3425) (meaning t m 3437) (meaning t m 3688) source

theorem rule25684 (p1994 p2027 p2510 p2528 p2651 p3008 p3172 p4118 : Prop) (h : p3008 ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2528) ∨ (¬ p3172) ∨ (¬ p2510) ∨ (¬ p2651) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (p3008) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial25684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory14940 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule25684 (meaning t m 1994) (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 2651) (meaning t m 3008) (meaning t m 3172) (meaning t m 4118) source

theorem rule25685 (p1988 p2027 p2114 p3073 p3266 p3449 p3954 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p3954) ∨ (¬ p1988) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial25685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory14941 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 8 9) (m.theta 9 10)
  exact rule25685 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 3954) source

theorem rule25686 (p2027 p2299 p2313 p2881 p3872 p4486 : Prop) (h : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p3872) ∨ (¬ p4486) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial25686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory14942 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25686 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2881) (meaning t m 3872) (meaning t m 4486) source

theorem rule25688 (p1979 p2027 p2137 p2622 p2743 p2839 p3051 p4320 : Prop) (h : p2622 ∨ (¬ p4320) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2137) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial25688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory14944 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule25688 (meaning t m 1979) (meaning t m 2027) (meaning t m 2137) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3051) (meaning t m 4320) source

theorem rule25690 (p2027 p2246 p2440 p2807 p3579 p4111 p4646 : Prop) (h : (¬ p4646) ∨ (¬ p3579) ∨ (¬ p2807) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial25690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory14946 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule25690 (meaning t m 2027) (meaning t m 2246) (meaning t m 2440) (meaning t m 2807) (meaning t m 3579) (meaning t m 4111) (meaning t m 4646) source

theorem rule25693 (p1976 p2027 p2138 p2765 p2891 p4173 p4244 : Prop) (h : (¬ p4244) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2138) ∨ p2765 ∨ (¬ p4173) ∨ (¬ p2891)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p4173) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial25693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory14949 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule25693 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2765) (meaning t m 2891) (meaning t m 4173) (meaning t m 4244) source

theorem rule25695 (p1994 p2027 p2352 p2651 p2963 p3008 p3324 : Prop) (h : p3008 ∨ (¬ p2651) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p3324) ∨ (¬ p2963)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (p3008) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial25695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory14951 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule25695 (meaning t m 1994) (meaning t m 2027) (meaning t m 2352) (meaning t m 2651) (meaning t m 2963) (meaning t m 3008) (meaning t m 3324) source

theorem rule25696 (p1986 p2027 p2598 p2641 p2688 p3365 p4195 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p2598) ∨ (¬ p4195) ∨ (¬ p2641) ∨ (¬ p3365) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3365) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial25696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory14952 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule25696 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2641) (meaning t m 2688) (meaning t m 3365) (meaning t m 4195) source

theorem rule25702 (p1988 p2027 p2313 p2553 p2761 p3008 p3654 p4623 : Prop) (h : (¬ p2761) ∨ p2027 ∨ (¬ p4623) ∨ (¬ p2553) ∨ (¬ p2313) ∨ (¬ p1988) ∨ p3008 ∨ (¬ p3654)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2761) ∨ (p3008) ∨ (¬ p3654) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial25702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory14958 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule25702 (meaning t m 1988) (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2761) (meaning t m 3008) (meaning t m 3654) (meaning t m 4623) source

theorem rule25706 (p1994 p2027 p2355 p2651 p2952 p2992 p2996 : Prop) (h : p2027 ∨ p2355 ∨ (¬ p2651) ∨ (¬ p1994) ∨ (¬ p2996) ∨ (¬ p2992) ∨ (¬ p2952)) : (¬ p1994) ∨ (p2027) ∨ (p2355) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial25706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory14962 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule25706 (meaning t m 1994) (meaning t m 2027) (meaning t m 2355) (meaning t m 2651) (meaning t m 2952) (meaning t m 2992) (meaning t m 2996) source

theorem rule25709 (p2027 p2406 p3055 p3541 p3684 p4734 : Prop) (h : p2027 ∨ (¬ p3684) ∨ (¬ p4734) ∨ (¬ p2406) ∨ (¬ p3055) ∨ (¬ p3541)) : (p2027) ∨ (¬ p2406) ∨ (¬ p3055) ∨ (¬ p3541) ∨ (¬ p3684) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory14965 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule25709 (meaning t m 2027) (meaning t m 2406) (meaning t m 3055) (meaning t m 3541) (meaning t m 3684) (meaning t m 4734) source

theorem rule25713 (p2027 p2498 p2588 p3319 p3690 p4556 p5299 p5379 : Prop) (h : (¬ p3690) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p5379) ∨ (¬ p3319) ∨ (¬ p5299) ∨ (¬ p2498) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3319) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p5299) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial25713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5299)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory14969 t (m.theta 0 9) (m.theta 1 6) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule25713 (meaning t m 2027) (meaning t m 2498) (meaning t m 2588) (meaning t m 3319) (meaning t m 3690) (meaning t m 4556) (meaning t m 5299) (meaning t m 5379) source

theorem rule25715 (p1982 p2027 p2169 p2761 p3319 p3923 p4444 p4623 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p4444) ∨ (¬ p2761) ∨ (¬ p1982) ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4623)) : (¬ p1982) ∨ (p2027) ∨ (p2169) ∨ (¬ p2761) ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4444) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial25715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory14971 t (m.theta 1 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25715 (meaning t m 1982) (meaning t m 2027) (meaning t m 2169) (meaning t m 2761) (meaning t m 3319) (meaning t m 3923) (meaning t m 4444) (meaning t m 4623) source

theorem rule25719 (p2027 p2088 p2751 p3171 p3189 p4340 p4364 : Prop) (h : (¬ p3189) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p4364) ∨ (¬ p2088) ∨ (¬ p4340) ∨ (¬ p3171)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2751) ∨ (¬ p3171) ∨ (¬ p3189) ∨ (¬ p4340) ∨ (¬ p4364) := by
  classical
  tauto

theorem initial25719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) := by
  have source := ElevenTheory.theory14975 t (m.theta 0 8) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule25719 (meaning t m 2027) (meaning t m 2088) (meaning t m 2751) (meaning t m 3171) (meaning t m 3189) (meaning t m 4340) (meaning t m 4364) source

theorem rule25723 (p2005 p2027 p2114 p2598 p2737 p3016 p3365 p3683 : Prop) (h : (¬ p3365) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p3016) ∨ (¬ p2005) ∨ (¬ p3683)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3016) ∨ (¬ p3365) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial25723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory14979 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule25723 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2598) (meaning t m 2737) (meaning t m 3016) (meaning t m 3365) (meaning t m 3683) source

theorem rule25735 (p2027 p3365 p3367 p3471 p3588 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p3367) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p3365)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial25735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14991 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule25735 (meaning t m 2027) (meaning t m 3365) (meaning t m 3367) (meaning t m 3471) (meaning t m 3588) (meaning t m 4752) source

theorem rule25736 (p2098 p2774 p4078 : Prop) (h : (¬ p4078) ∨ (¬ p2098) ∨ p2774) : (¬ p2098) ∨ (p2774) ∨ (¬ p4078) := by
  classical
  tauto

theorem initial25736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (meaning t m 2774) ∨ (¬ (meaning t m 4078)) := by
  have source := ElevenTheory.theory14992 (m.theta 0 2) (m.theta 2 6) (m.theta 2 8)
  exact rule25736 (meaning t m 2098) (meaning t m 2774) (meaning t m 4078) source

theorem rule25740 (p2589 p3363 p3641 p4607 : Prop) (h : (¬ p3363) ∨ (¬ p2589) ∨ (¬ p4607) ∨ (¬ p3641)) : (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3641) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial25740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory14996 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule25740 (meaning t m 2589) (meaning t m 3363) (meaning t m 3641) (meaning t m 4607) source

theorem rule25742 (p2027 p3016 p3564 p3742 p3921 p4624 : Prop) (h : (¬ p3921) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4624) ∨ (¬ p3564)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial25742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory14998 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule25742 (meaning t m 2027) (meaning t m 3016) (meaning t m 3564) (meaning t m 3742) (meaning t m 3921) (meaning t m 4624) source

theorem rule25743 (p2298 p3740 p3921 : Prop) (h : (¬ p3921) ∨ (¬ p3740) ∨ p2298) : (p2298) ∨ (¬ p3740) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial25743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2298) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory14999 (m.theta 3 7) (m.theta 4 7) (m.theta 6 7)
  exact rule25743 (meaning t m 2298) (meaning t m 3740) (meaning t m 3921) source

theorem rule25746 (p2307 p2553 p2578 : Prop) (h : (¬ p2307) ∨ (¬ p2578) ∨ p2553) : (¬ p2307) ∨ (p2553) ∨ (¬ p2578) := by
  classical
  tauto

theorem initial25746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (meaning t m 2553) ∨ (¬ (meaning t m 2578)) := by
  have source := ElevenTheory.theory15002 (m.theta 0 6) (m.theta 4 6) (m.theta 6 7)
  exact rule25746 (meaning t m 2307) (meaning t m 2553) (meaning t m 2578) source

theorem rule25748 (p2578 p3096 p3743 : Prop) (h : (¬ p3096) ∨ (¬ p2578) ∨ p3743) : (¬ p2578) ∨ (¬ p3096) ∨ (p3743) := by
  classical
  tauto

theorem initial25748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3096)) ∨ (meaning t m 3743) := by
  have source := ElevenTheory.theory15004 (m.theta 0 6) (m.theta 4 6) (m.theta 5 6)
  exact rule25748 (meaning t m 2578) (meaning t m 3096) (meaning t m 3743) source

theorem rule25754 (p2027 p2298 p2331 p2553 p3414 p4973 : Prop) (h : (¬ p2298) ∨ (¬ p2553) ∨ (¬ p4973) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p3414) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial25754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory15010 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule25754 (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 2553) (meaning t m 3414) (meaning t m 4973) source

theorem rule25756 (p2027 p2341 p2499 p2761 p3452 p3945 p4137 p4444 p4604 p5207 : Prop) (h : (¬ p4604) ∨ (¬ p3452) ∨ (¬ p4444) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p2499) ∨ (¬ p5207) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3452) ∨ (¬ p3945) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial25756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory15012 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25756 (meaning t m 2027) (meaning t m 2341) (meaning t m 2499) (meaning t m 2761) (meaning t m 3452) (meaning t m 3945) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) (meaning t m 5207) source

theorem rule25757 (p2027 p2247 p2744 p3051 p3486 p4172 p4202 p4257 : Prop) (h : (¬ p3051) ∨ (¬ p4257) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4202) ∨ (¬ p3486) ∨ (¬ p2744) ∨ (¬ p4172)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4172) ∨ (¬ p4202) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial25757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory15013 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7)
  exact rule25757 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3051) (meaning t m 3486) (meaning t m 4172) (meaning t m 4202) (meaning t m 4257) source

theorem rule25758 (p2528 p3256 p4437 : Prop) (h : (¬ p3256) ∨ (¬ p4437) ∨ p2528) : (p2528) ∨ (¬ p3256) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial25758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2528) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory15014 (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule25758 (meaning t m 2528) (meaning t m 3256) (meaning t m 4437) source

theorem rule25764 (p2027 p3038 p3527 p3553 p4111 p4652 : Prop) (h : (¬ p3527) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4652) ∨ (¬ p3038)) : (p2027) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4111) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial25764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory15020 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule25764 (meaning t m 2027) (meaning t m 3038) (meaning t m 3527) (meaning t m 3553) (meaning t m 4111) (meaning t m 4652) source

theorem rule25770 (p2027 p2518 p3193 p4149 p4440 p5122 : Prop) (h : (¬ p4440) ∨ (¬ p3193) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2518) ∨ (¬ p3193) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15026 t (m.theta 1 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 10) (m.theta 8 9)
  exact rule25770 (meaning t m 2027) (meaning t m 2518) (meaning t m 3193) (meaning t m 4149) (meaning t m 4440) (meaning t m 5122) source

theorem rule25774 (p2027 p2132 p2743 p2891 p2963 p3246 p3361 p4037 p4418 p4625 p4737 : Prop) (h : (¬ p4625) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p4037) ∨ (¬ p2963) ∨ (¬ p4418) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2891) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4418) ∨ (¬ p4625) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial25774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory15030 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule25774 (meaning t m 2027) (meaning t m 2132) (meaning t m 2743) (meaning t m 2891) (meaning t m 2963) (meaning t m 3246) (meaning t m 3361) (meaning t m 4037) (meaning t m 4418) (meaning t m 4625) (meaning t m 4737) source

theorem rule25777 (p2819 p3063 p4024 : Prop) (h : (¬ p2819) ∨ (¬ p4024) ∨ p3063) : (¬ p2819) ∨ (p3063) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial25777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (meaning t m 3063) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory15033 (m.theta 1 6) (m.theta 2 6) (m.theta 6 8)
  exact rule25777 (meaning t m 2819) (meaning t m 3063) (meaning t m 4024) source

theorem rule25778 (p1983 p2027 p2997 p3276 p3343 p3742 p3921 p4381 : Prop) (h : p2997 ∨ (¬ p3921) ∨ (¬ p3742) ∨ (¬ p3343) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p1983) ∨ (¬ p3276)) : (¬ p1983) ∨ (p2027) ∨ (p2997) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial25778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory15034 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule25778 (meaning t m 1983) (meaning t m 2027) (meaning t m 2997) (meaning t m 3276) (meaning t m 3343) (meaning t m 3742) (meaning t m 3921) (meaning t m 4381) source

theorem rule25783 (p1997 p2027 p2177 p2230 p2579 p2997 p3581 p3644 : Prop) (h : (¬ p2177) ∨ (¬ p3644) ∨ (¬ p3581) ∨ (¬ p2230) ∨ p2997 ∨ (¬ p2579) ∨ (¬ p1997) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial25783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory15039 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25783 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 2579) (meaning t m 2997) (meaning t m 3581) (meaning t m 3644) source

theorem rule25788 (p1981 p2027 p2668 p3043 p3680 p4037 p4191 : Prop) (h : (¬ p4037) ∨ p3043 ∨ (¬ p2668) ∨ (¬ p3680) ∨ (¬ p1981) ∨ (¬ p4191) ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2668) ∨ (p3043) ∨ (¬ p3680) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial25788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory15044 t (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule25788 (meaning t m 1981) (meaning t m 2027) (meaning t m 2668) (meaning t m 3043) (meaning t m 3680) (meaning t m 4037) (meaning t m 4191) source

theorem rule25795 (p1982 p2027 p2341 p2459 p2707 p3474 p3577 p3583 : Prop) (h : p2027 ∨ (¬ p3577) ∨ (¬ p2707) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p3583) ∨ p3474) : (¬ p1982) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (p3474) ∨ (¬ p3577) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial25795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory15051 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule25795 (meaning t m 1982) (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2707) (meaning t m 3474) (meaning t m 3577) (meaning t m 3583) source

theorem rule25801 (p2027 p2249 p2951 p2963 p2992 p3051 p3246 p3266 p3922 p3950 p4321 p4430 : Prop) (h : p2027 ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p4321) ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2249) ∨ (¬ p3922) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4430)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3922) ∨ (¬ p3950) ∨ (¬ p4321) ∨ (¬ p4430) := by
  classical
  tauto

theorem initial25801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4430)) := by
  have source := ElevenTheory.theory15057 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 1 9) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25801 (meaning t m 2027) (meaning t m 2249) (meaning t m 2951) (meaning t m 2963) (meaning t m 2992) (meaning t m 3051) (meaning t m 3246) (meaning t m 3266) (meaning t m 3922) (meaning t m 3950) (meaning t m 4321) (meaning t m 4430) source

theorem rule25802 (p2027 p2245 p2952 p2992 p3379 p4813 : Prop) (h : (¬ p4813) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2992) ∨ (¬ p3379) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3379) ∨ (¬ p4813) := by
  classical
  tauto

theorem initial25802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4813)) := by
  have source := ElevenTheory.theory15058 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5)
  exact rule25802 (meaning t m 2027) (meaning t m 2245) (meaning t m 2952) (meaning t m 2992) (meaning t m 3379) (meaning t m 4813) source

theorem rule25803 (p2027 p2192 p2312 p2553 p3486 p4283 p4718 : Prop) (h : (¬ p4283) ∨ (¬ p2192) ∨ (¬ p4718) ∨ (¬ p3486) ∨ (¬ p2312) ∨ (¬ p2553) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p2312) ∨ (¬ p2553) ∨ (¬ p3486) ∨ (¬ p4283) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial25803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory15059 t (m.theta 0 7) (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule25803 (meaning t m 2027) (meaning t m 2192) (meaning t m 2312) (meaning t m 2553) (meaning t m 3486) (meaning t m 4283) (meaning t m 4718) source

theorem rule25806 (p1991 p2027 p2657 p2881 p2938 p3644 p3742 : Prop) (h : (¬ p3742) ∨ (¬ p1991) ∨ (¬ p3644) ∨ p2027 ∨ p2938 ∨ (¬ p2657) ∨ (¬ p2881)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial25806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory15062 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule25806 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2881) (meaning t m 2938) (meaning t m 3644) (meaning t m 3742) source

theorem rule25814 (p1982 p2027 p2169 p3323 p3461 p3956 p4389 p4444 : Prop) (h : (¬ p3956) ∨ (¬ p3323) ∨ (¬ p4389) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p1982) ∨ p2169 ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2169) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3956) ∨ (¬ p4389) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial25814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory15070 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25814 (meaning t m 1982) (meaning t m 2027) (meaning t m 2169) (meaning t m 3323) (meaning t m 3461) (meaning t m 3956) (meaning t m 4389) (meaning t m 4444) source

theorem rule25815 (p4037 p4137 p4389 : Prop) (h : (¬ p4389) ∨ (¬ p4137) ∨ p4037) : (p4037) ∨ (¬ p4137) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial25815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4037) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory15071 (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule25815 (meaning t m 4037) (meaning t m 4137) (meaning t m 4389) source

theorem rule25818 (p2449 p3037 p3548 p3657 : Prop) (h : (¬ p3037) ∨ (¬ p3657) ∨ (¬ p3548) ∨ (¬ p2449)) : (¬ p2449) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial25818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory15074 (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25818 (meaning t m 2449) (meaning t m 3037) (meaning t m 3548) (meaning t m 3657) source

theorem rule25824 (p2027 p2210 p2245 p2657 p2727 p4959 : Prop) (h : (¬ p2245) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2657) ∨ (¬ p4959) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial25824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory15080 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4)
  exact rule25824 (meaning t m 2027) (meaning t m 2210) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 4959) source

theorem rule25825 (p1979 p2027 p2323 p2542 p2563 p2651 p3952 : Prop) (h : p2323 ∨ (¬ p2563) ∨ (¬ p1979) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2542)) : (¬ p1979) ∨ (p2027) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial25825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory15081 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule25825 (meaning t m 1979) (meaning t m 2027) (meaning t m 2323) (meaning t m 2542) (meaning t m 2563) (meaning t m 2651) (meaning t m 3952) source

theorem rule25827 (p2027 p2246 p2744 p2780 p2946 p3156 p3366 p3917 p3969 p4191 p5119 : Prop) (h : (¬ p2946) ∨ (¬ p5119) ∨ (¬ p3366) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p2744) ∨ (¬ p3156) ∨ (¬ p4191) ∨ (¬ p2246) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory15083 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25827 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2780) (meaning t m 2946) (meaning t m 3156) (meaning t m 3366) (meaning t m 3917) (meaning t m 3969) (meaning t m 4191) (meaning t m 5119) source

theorem rule25829 (p2027 p2839 p3585 p3695 p3874 p4608 : Prop) (h : (¬ p2839) ∨ p2027 ∨ (¬ p4608) ∨ (¬ p3695) ∨ (¬ p3585) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p3874) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial25829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory15085 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 8)
  exact rule25829 (meaning t m 2027) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 3874) (meaning t m 4608) source

theorem rule25834 (p2027 p2245 p2608 p2657 p2727 p2744 : Prop) (h : (¬ p2245) ∨ (¬ p2727) ∨ (¬ p2657) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p2608)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2744) := by
  classical
  tauto

theorem initial25834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2744)) := by
  have source := ElevenTheory.theory15090 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4)
  exact rule25834 (meaning t m 2027) (meaning t m 2245) (meaning t m 2608) (meaning t m 2657) (meaning t m 2727) (meaning t m 2744) source

theorem rule25835 (p2027 p2249 p2656 p2727 p3051 p3414 p3699 p4399 : Prop) (h : (¬ p2727) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p3051) ∨ (¬ p3699) ∨ (¬ p2656) ∨ (¬ p4399)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3051) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial25835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory15091 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7)
  exact rule25835 (meaning t m 2027) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 3051) (meaning t m 3414) (meaning t m 3699) (meaning t m 4399) source

theorem rule25838 (p2027 p2476 p3516 p4278 p4922 p5201 : Prop) (h : (¬ p3516) ∨ (¬ p4278) ∨ (¬ p5201) ∨ (¬ p4922) ∨ p2027 ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4922) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial25838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4922)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory15094 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 9)
  exact rule25838 (meaning t m 2027) (meaning t m 2476) (meaning t m 3516) (meaning t m 4278) (meaning t m 4922) (meaning t m 5201) source

theorem rule25839 (p2027 p2187 p2363 p2534 p3573 p3958 : Prop) (h : (¬ p2534) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p3573) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial25839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory15095 t (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25839 (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 2534) (meaning t m 3573) (meaning t m 3958) source

theorem rule25842 (p2027 p2138 p3051 p3873 p4244 p4521 : Prop) (h : (¬ p4244) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2138) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3051) ∨ (¬ p3873) ∨ (¬ p4244) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial25842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory15098 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule25842 (meaning t m 2027) (meaning t m 2138) (meaning t m 3051) (meaning t m 3873) (meaning t m 4244) (meaning t m 4521) source

theorem rule25845 (p2027 p2210 p2245 p2657 p2727 p2749 p4877 : Prop) (h : (¬ p2727) ∨ (¬ p2749) ∨ (¬ p4877) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2245)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial25845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory15101 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4)
  exact rule25845 (meaning t m 2027) (meaning t m 2210) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) (meaning t m 4877) source

theorem rule25849 (p2027 p2264 p2608 p2744 p3027 p3549 p3591 p3644 p4276 : Prop) (h : (¬ p2744) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p2608) ∨ (¬ p2264) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3027) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial25849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory15105 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25849 (meaning t m 2027) (meaning t m 2264) (meaning t m 2608) (meaning t m 2744) (meaning t m 3027) (meaning t m 3549) (meaning t m 3591) (meaning t m 3644) (meaning t m 4276) source

theorem rule25853 (p2027 p2247 p2744 p3051 p3486 p4172 p4874 : Prop) (h : (¬ p2247) ∨ (¬ p4172) ∨ p2027 ∨ (¬ p4874) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4172) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory15109 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 7)
  exact rule25853 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3051) (meaning t m 3486) (meaning t m 4172) (meaning t m 4874) source

theorem rule25858 (p2006 p2027 p2132 p2387 p2778 p2997 p3063 p3097 p3957 : Prop) (h : (¬ p3097) ∨ (¬ p2006) ∨ p2997 ∨ p2027 ∨ (¬ p3063) ∨ (¬ p2387) ∨ (¬ p3957) ∨ (¬ p2778) ∨ (¬ p2132)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2387) ∨ (¬ p2778) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3097) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial25858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2778)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory15114 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25858 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2387) (meaning t m 2778) (meaning t m 2997) (meaning t m 3063) (meaning t m 3097) (meaning t m 3957) source

theorem rule25859 (p1976 p2027 p2138 p2839 p2997 p3097 p3688 p4428 : Prop) (h : p2997 ∨ (¬ p1976) ∨ (¬ p2138) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2839)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3688) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial25859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory15115 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule25859 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2839) (meaning t m 2997) (meaning t m 3097) (meaning t m 3688) (meaning t m 4428) source

theorem rule25862 (p2027 p2136 p2247 p2744 p3366 p3449 p3646 p3989 p4181 p4347 p5122 : Prop) (h : (¬ p5122) ∨ (¬ p2136) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3646) ∨ (¬ p3449) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3989)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15118 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25862 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3449) (meaning t m 3646) (meaning t m 3989) (meaning t m 4181) (meaning t m 4347) (meaning t m 5122) source

theorem rule25864 (p2027 p2247 p3449 p3645 p3646 p3989 p4181 p4347 p4959 p5122 : Prop) (h : (¬ p4959) ∨ (¬ p5122) ∨ (¬ p4181) ∨ (¬ p3645) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3449) ∨ (¬ p2247) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3449) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p4959) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4959)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15120 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25864 (meaning t m 2027) (meaning t m 2247) (meaning t m 3449) (meaning t m 3645) (meaning t m 3646) (meaning t m 3989) (meaning t m 4181) (meaning t m 4347) (meaning t m 4959) (meaning t m 5122) source

theorem rule25866 (p2396 p4260 p4829 : Prop) (h : (¬ p4829) ∨ (¬ p2396) ∨ (¬ p4260)) : (¬ p2396) ∨ (¬ p4260) ∨ (¬ p4829) := by
  classical
  tauto

theorem initial25866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4829)) := by
  have source := ElevenTheory.theory15122 (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule25866 (meaning t m 2396) (meaning t m 4260) (meaning t m 4829) source

theorem rule25867 (p1994 p2027 p2230 p2440 p2688 p2922 p3540 p4281 : Prop) (h : (¬ p2230) ∨ (¬ p4281) ∨ p2688 ∨ (¬ p1994) ∨ (¬ p2922) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2688) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial25867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory15123 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule25867 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2688) (meaning t m 2922) (meaning t m 3540) (meaning t m 4281) source

theorem rule25868 (p2027 p2311 p2707 p2778 p3434 p3821 p4734 : Prop) (h : (¬ p2778) ∨ (¬ p2311) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2707) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2707) ∨ (¬ p2778) ∨ (¬ p3434) ∨ (¬ p3821) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial25868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory15124 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 7 9)
  exact rule25868 (meaning t m 2027) (meaning t m 2311) (meaning t m 2707) (meaning t m 2778) (meaning t m 3434) (meaning t m 3821) (meaning t m 4734) source

theorem rule25869 (p2005 p2027 p2622 p2743 p2829 p3483 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p3483) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2743) ∨ p2622 ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial25869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory15125 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule25869 (meaning t m 2005) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 2829) (meaning t m 3483) (meaning t m 4137) source

theorem rule25870 (p2027 p2247 p2744 p3073 p3449 p3688 p4358 p5118 p5580 : Prop) (h : (¬ p3688) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p5118) ∨ (¬ p2247) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p5580)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p4358) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory15126 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25870 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3073) (meaning t m 3449) (meaning t m 3688) (meaning t m 4358) (meaning t m 5118) (meaning t m 5580) source

theorem rule25871 (p2027 p2247 p2744 p3998 p4436 p5242 p5693 : Prop) (h : (¬ p2744) ∨ (¬ p4436) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3998) ∨ (¬ p4436) ∨ (¬ p5242) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial25871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory15127 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 8 10)
  exact rule25871 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3998) (meaning t m 4436) (meaning t m 5242) (meaning t m 5693) source

theorem rule25872 (p2027 p2247 p2744 p3449 p3688 p3917 p4181 p4191 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3917) ∨ (¬ p2247) ∨ (¬ p4181)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory15128 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25872 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3449) (meaning t m 3688) (meaning t m 3917) (meaning t m 4181) (meaning t m 4191) (meaning t m 5119) source

theorem rule25873 (p2027 p2608 p2744 p3038 p3631 p3821 p5206 : Prop) (h : (¬ p2608) ∨ (¬ p5206) ∨ (¬ p3038) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3038) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial25873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory15129 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 7 9)
  exact rule25873 (meaning t m 2027) (meaning t m 2608) (meaning t m 2744) (meaning t m 3038) (meaning t m 3631) (meaning t m 3821) (meaning t m 5206) source

end SunPrize.SMT
