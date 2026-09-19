import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory020
import SunPrize.Certificate.Theory021
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule16875 (p2459 p4045 p4404 p4440 : Prop) (h : (¬ p4404) ∨ (¬ p4440) ∨ (¬ p2459) ∨ (¬ p4045)) : (¬ p2459) ∨ (¬ p4045) ∨ (¬ p4404) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial16875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory6147 (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule16875 (meaning t m 2459) (meaning t m 4045) (meaning t m 4404) (meaning t m 4440) source

theorem rule16876 (p1975 p2027 p2299 p2699 p2911 p2922 p3379 : Prop) (h : (¬ p3379) ∨ p2699 ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2911)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial16876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory6148 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16876 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2699) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) source

theorem rule16877 (p1977 p2608 p2699 p2750 : Prop) (h : (¬ p1977) ∨ p2699 ∨ p2750 ∨ (¬ p2608)) : (¬ p1977) ∨ (¬ p2608) ∨ (p2699) ∨ (p2750) := by
  classical
  tauto

theorem initial16877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (meaning t m 2750) := by
  have source := ElevenTheory.theory6149 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule16877 (meaning t m 1977) (meaning t m 2608) (meaning t m 2699) (meaning t m 2750) source

theorem rule16878 (p1987 p2027 p2274 p2737 p2765 p3568 p3688 p4337 : Prop) (h : (¬ p2737) ∨ (¬ p1987) ∨ (¬ p3688) ∨ p2765 ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4337) ∨ (¬ p3568)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2737) ∨ (p2765) ∨ (¬ p3568) ∨ (¬ p3688) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial16878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory6150 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16878 (meaning t m 1987) (meaning t m 2027) (meaning t m 2274) (meaning t m 2737) (meaning t m 2765) (meaning t m 3568) (meaning t m 3688) (meaning t m 4337) source

theorem rule16879 (p1994 p2027 p2274 p2651 p2765 p2963 p3568 : Prop) (h : (¬ p3568) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2651) ∨ p2765 ∨ (¬ p2274)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2651) ∨ (p2765) ∨ (¬ p2963) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial16879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory6151 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16879 (meaning t m 1994) (meaning t m 2027) (meaning t m 2274) (meaning t m 2651) (meaning t m 2765) (meaning t m 2963) (meaning t m 3568) source

theorem rule16880 (p1986 p2027 p2230 p2579 p2588 p2997 p3684 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p3684) ∨ (¬ p2230) ∨ (¬ p2588) ∨ (¬ p1986) ∨ (¬ p2579)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial16880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory6152 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule16880 (meaning t m 1986) (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) (meaning t m 3684) source

theorem rule16882 (p2000 p2027 p2476 p2588 p2997 p3083 p3574 : Prop) (h : (¬ p2476) ∨ (¬ p3083) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p3574) ∨ p2997 ∨ (¬ p2588)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3083) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial16882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory6154 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule16882 (meaning t m 2000) (meaning t m 2027) (meaning t m 2476) (meaning t m 2588) (meaning t m 2997) (meaning t m 3083) (meaning t m 3574) source

theorem rule16883 (p1991 p2027 p2462 p2761 p2963 p4037 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p2963) ∨ p2462 ∨ (¬ p2761)) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6155 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16883 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 2963) (meaning t m 4037) (meaning t m 4191) source

theorem rule16884 (p1991 p2027 p2764 p2963 p3568 p4107 p4381 : Prop) (h : (¬ p1991) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4381) ∨ p2764) : (¬ p1991) ∨ (p2027) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6156 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16884 (meaning t m 1991) (meaning t m 2027) (meaning t m 2764) (meaning t m 2963) (meaning t m 3568) (meaning t m 4107) (meaning t m 4381) source

theorem rule16886 (p1991 p2027 p2657 p2938 p3246 p3742 p4278 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p3246) ∨ (¬ p3742) ∨ p2938 ∨ (¬ p4278)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6158 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16886 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2938) (meaning t m 3246) (meaning t m 3742) (meaning t m 4278) source

theorem rule16887 (p3880 p4109 p4115 p4238 : Prop) (h : (¬ p4238) ∨ (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4115)) : (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4115) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial16887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory6159 (m.theta 0 5) (m.theta 0 8) (m.theta 4 5) (m.theta 5 8)
  exact rule16887 (meaning t m 3880) (meaning t m 4109) (meaning t m 4115) (meaning t m 4238) source

theorem rule16888 (p1986 p2027 p2143 p2202 p2427 p3367 p3556 p3583 : Prop) (h : (¬ p1986) ∨ (¬ p2143) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3556) ∨ p2202) : (¬ p1986) ∨ (p2027) ∨ (¬ p2143) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3367) ∨ (¬ p3556) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial16888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory6160 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule16888 (meaning t m 1986) (meaning t m 2027) (meaning t m 2143) (meaning t m 2202) (meaning t m 2427) (meaning t m 3367) (meaning t m 3556) (meaning t m 3583) source

theorem rule16889 (p1982 p2027 p2241 p2363 p2641 p2668 p2699 : Prop) (h : (¬ p2668) ∨ (¬ p1982) ∨ p2699 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (p2699) := by
  classical
  tauto

theorem initial16889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory6161 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16889 (meaning t m 1982) (meaning t m 2027) (meaning t m 2241) (meaning t m 2363) (meaning t m 2641) (meaning t m 2668) (meaning t m 2699) source

theorem rule16890 (p1986 p2027 p2313 p2462 p2785 p3367 p3688 p4107 : Prop) (h : p2027 ∨ p2462 ∨ (¬ p2313) ∨ (¬ p3688) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p1986) ∨ (¬ p4107)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2313) ∨ (p2462) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial16890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6162 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16890 (meaning t m 1986) (meaning t m 2027) (meaning t m 2313) (meaning t m 2462) (meaning t m 2785) (meaning t m 3367) (meaning t m 3688) (meaning t m 4107) source

theorem rule16891 (p1998 p2027 p2363 p2699 p3063 p3093 p4348 : Prop) (h : (¬ p3093) ∨ (¬ p2363) ∨ (¬ p3063) ∨ p2699 ∨ (¬ p1998) ∨ (¬ p4348) ∨ p2027) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6163 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16891 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 4348) source

theorem rule16893 (p1986 p2027 p2598 p2765 p2780 p3125 p3917 : Prop) (h : p2027 ∨ (¬ p1986) ∨ p2765 ∨ (¬ p3125) ∨ (¬ p3917) ∨ (¬ p2598) ∨ (¬ p2780)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (p2765) ∨ (¬ p2780) ∨ (¬ p3125) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial16893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory6165 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule16893 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2765) (meaning t m 2780) (meaning t m 3125) (meaning t m 3917) source

theorem rule16894 (p1986 p2027 p2633 p3367 p3570 p3583 p4244 : Prop) (h : (¬ p3570) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3583) ∨ p2633 ∨ (¬ p1986) ∨ (¬ p4244)) : (¬ p1986) ∨ (p2027) ∨ (p2633) ∨ (¬ p3367) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6166 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule16894 (meaning t m 1986) (meaning t m 2027) (meaning t m 2633) (meaning t m 3367) (meaning t m 3570) (meaning t m 3583) (meaning t m 4244) source

theorem rule16896 (p1999 p2027 p2765 p3105 p3680 p3758 p4191 : Prop) (h : (¬ p3680) ∨ (¬ p1999) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p3105) ∨ p2765 ∨ (¬ p3758)) : (¬ p1999) ∨ (p2027) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6168 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16896 (meaning t m 1999) (meaning t m 2027) (meaning t m 2765) (meaning t m 3105) (meaning t m 3680) (meaning t m 3758) (meaning t m 4191) source

theorem rule16897 (p1986 p2027 p2598 p2766 p3425 p3659 p4348 : Prop) (h : (¬ p1986) ∨ (¬ p4348) ∨ p2766 ∨ p2027 ∨ (¬ p3659) ∨ (¬ p2598) ∨ (¬ p3425)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6169 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16897 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2766) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) source

theorem rule16899 (p2001 p2027 p2220 p2427 p2765 p3556 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p2001) ∨ p2027 ∨ p2765 ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p2220)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3556) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6171 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule16899 (meaning t m 2001) (meaning t m 2027) (meaning t m 2220) (meaning t m 2427) (meaning t m 2765) (meaning t m 3556) (meaning t m 4110) source

theorem rule16900 (p1986 p2027 p2764 p3366 p3367 p3425 p4106 p4278 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p3425) ∨ p2764 ∨ (¬ p4106) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3366) ∨ (¬ p1986) ∨ (¬ p3367)) : (¬ p1986) ∨ (p2027) ∨ (p2764) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6172 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16900 (meaning t m 1986) (meaning t m 2027) (meaning t m 2764) (meaning t m 3366) (meaning t m 3367) (meaning t m 3425) (meaning t m 4106) (meaning t m 4278) (meaning t m 4381) source

theorem rule16902 (p1975 p2027 p2295 p2699 p3093 p3319 p4037 : Prop) (h : (¬ p3093) ∨ p2027 ∨ (¬ p2295) ∨ p2699 ∨ (¬ p1975) ∨ (¬ p4037) ∨ (¬ p3319)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial16902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory6174 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16902 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 4037) source

theorem rule16903 (p1986 p2027 p2187 p2598 p2765 p2780 p4358 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p1986) ∨ (¬ p2187) ∨ (¬ p4358) ∨ (¬ p2780) ∨ p2765) : (¬ p1986) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2598) ∨ (p2765) ∨ (¬ p2780) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial16903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory6175 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule16903 (meaning t m 1986) (meaning t m 2027) (meaning t m 2187) (meaning t m 2598) (meaning t m 2765) (meaning t m 2780) (meaning t m 4358) source

theorem rule16904 (p1988 p2027 p2323 p2331 p2363 p2668 p3266 : Prop) (h : (¬ p1988) ∨ p2323 ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p2363) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial16904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory6176 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16904 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3266) source

theorem rule16905 (p1981 p2027 p2241 p2699 p3189 p3256 p4347 : Prop) (h : (¬ p1981) ∨ p2699 ∨ (¬ p4347) ∨ (¬ p3189) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3256)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6177 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16905 (meaning t m 1981) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3189) (meaning t m 3256) (meaning t m 4347) source

theorem rule16906 (p1999 p2088 p4080 p4330 : Prop) (h : p4080 ∨ p4330 ∨ (¬ p2088) ∨ (¬ p1999)) : (¬ p1999) ∨ (¬ p2088) ∨ (p4080) ∨ (p4330) := by
  classical
  tauto

theorem initial16906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 4080) ∨ (meaning t m 4330) := by
  have source := ElevenTheory.theory6178 t (m.theta 0 8) (m.theta 6 9) (m.theta 8 9)
  exact rule16906 (meaning t m 1999) (meaning t m 2088) (meaning t m 4080) (meaning t m 4330) source

theorem rule16907 (p2011 p2027 p2192 p2241 p2699 p3115 p3952 p4365 : Prop) (h : (¬ p4365) ∨ (¬ p2192) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p2241) ∨ p2699 ∨ p2027 ∨ (¬ p2011)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial16907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory6179 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule16907 (meaning t m 2011) (meaning t m 2027) (meaning t m 2192) (meaning t m 2241) (meaning t m 2699) (meaning t m 3115) (meaning t m 3952) (meaning t m 4365) source

theorem rule16908 (p2001 p2027 p2220 p2765 p2870 p3556 p3758 : Prop) (h : p2765 ∨ (¬ p2001) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p2220)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial16908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory6180 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule16908 (meaning t m 2001) (meaning t m 2027) (meaning t m 2220) (meaning t m 2765) (meaning t m 2870) (meaning t m 3556) (meaning t m 3758) source

theorem rule16909 (p1986 p2027 p2132 p2622 p3365 p3367 p3583 : Prop) (h : (¬ p3583) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p2132) ∨ (¬ p3367) ∨ p2622) : (¬ p1986) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial16909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory6181 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule16909 (meaning t m 1986) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 3365) (meaning t m 3367) (meaning t m 3583) source

theorem rule16911 (p1986 p2027 p2462 p2598 p2780 p3822 p4107 : Prop) (h : p2462 ∨ (¬ p1986) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p2598)) : (¬ p1986) ∨ (p2027) ∨ (p2462) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial16911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6183 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16911 (meaning t m 1986) (meaning t m 2027) (meaning t m 2462) (meaning t m 2598) (meaning t m 2780) (meaning t m 3822) (meaning t m 4107) source

theorem rule16913 (p1986 p2027 p2462 p2761 p3367 p3588 p3773 p3959 p5294 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2761) ∨ (¬ p3773) ∨ (¬ p5294) ∨ (¬ p3959) ∨ (¬ p1986) ∨ (¬ p3588)) : (¬ p1986) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3773) ∨ (¬ p3959) ∨ (¬ p5294) := by
  classical
  tauto

theorem initial16913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 5294)) := by
  have source := ElevenTheory.theory6185 t (m.theta 0 7) (m.theta 0 9) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16913 (meaning t m 1986) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3367) (meaning t m 3588) (meaning t m 3773) (meaning t m 3959) (meaning t m 5294) source

theorem rule16914 (p2001 p2027 p2192 p2210 p2699 p3156 p3952 : Prop) (h : (¬ p2210) ∨ (¬ p2192) ∨ (¬ p3156) ∨ p2699 ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2001)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3156) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6186 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule16914 (meaning t m 2001) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2699) (meaning t m 3156) (meaning t m 3952) source

theorem rule16915 (p1998 p2027 p2177 p2192 p2210 p2274 p2699 : Prop) (h : p2699 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p2177) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (p2699) := by
  classical
  tauto

theorem initial16915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory6187 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16915 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2699) source

theorem rule16916 (p1992 p2027 p2579 p2766 p3363 p3585 p3956 p4347 : Prop) (h : (¬ p1992) ∨ p2766 ∨ (¬ p4347) ∨ (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3956) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6188 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16916 (meaning t m 1992) (meaning t m 2027) (meaning t m 2579) (meaning t m 2766) (meaning t m 3363) (meaning t m 3585) (meaning t m 3956) (meaning t m 4347) source

theorem rule16917 (p1986 p2027 p2177 p2598 p2780 p2997 p3659 p3689 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p2177) ∨ (¬ p1986) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3689) ∨ (¬ p3659)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3659) ∨ (¬ p3689) := by
  classical
  tauto

theorem initial16917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) := by
  have source := ElevenTheory.theory6189 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16917 (meaning t m 1986) (meaning t m 2027) (meaning t m 2177) (meaning t m 2598) (meaning t m 2780) (meaning t m 2997) (meaning t m 3659) (meaning t m 3689) source

theorem rule16919 (p1987 p2027 p2589 p2662 p2810 p2997 p3097 p4110 : Prop) (h : (¬ p2589) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p2662) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6191 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule16919 (meaning t m 1987) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2810) (meaning t m 2997) (meaning t m 3097) (meaning t m 4110) source

theorem rule16920 (p1994 p2027 p2406 p2440 p2499 p2588 p2997 : Prop) (h : (¬ p2440) ∨ (¬ p1994) ∨ p2027 ∨ p2997 ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2406)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2997) := by
  classical
  tauto

theorem initial16920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) := by
  have source := ElevenTheory.theory6192 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule16920 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2499) (meaning t m 2588) (meaning t m 2997) source

theorem rule16921 (p1994 p2027 p2230 p2440 p2579 p2588 p2997 : Prop) (h : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2440) ∨ (¬ p1994) ∨ p2997 ∨ p2027 ∨ (¬ p2230)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) := by
  classical
  tauto

theorem initial16921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) := by
  have source := ElevenTheory.theory6193 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule16921 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) source

theorem rule16922 (p3246 p3571 p5357 p5358 : Prop) (h : (¬ p3246) ∨ (¬ p5358) ∨ (¬ p5357) ∨ (¬ p3571)) : (¬ p3246) ∨ (¬ p3571) ∨ (¬ p5357) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial16922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 5357)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory6194 (m.theta 1 7) (m.theta 1 9) (m.theta 5 7) (m.theta 7 9)
  exact rule16922 (meaning t m 3246) (meaning t m 3571) (meaning t m 5357) (meaning t m 5358) source

theorem rule16923 (p1998 p2027 p2132 p2611 p2881 p3434 p3587 p3690 : Prop) (h : (¬ p2132) ∨ p2611 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3587) ∨ (¬ p3690) ∨ (¬ p3434) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial16923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory6195 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16923 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2881) (meaning t m 3434) (meaning t m 3587) (meaning t m 3690) source

theorem rule16924 (p1986 p2027 p2578 p2766 p2785 p3367 p3688 p3956 p4347 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p2578) ∨ (¬ p3688) ∨ (¬ p1986) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3956) ∨ (¬ p4347)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2578) ∨ (p2766) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2578)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6196 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16924 (meaning t m 1986) (meaning t m 2027) (meaning t m 2578) (meaning t m 2766) (meaning t m 2785) (meaning t m 3367) (meaning t m 3688) (meaning t m 3956) (meaning t m 4347) source

theorem rule16926 (p1986 p2027 p2299 p2313 p2633 p2785 p3367 p3688 : Prop) (h : p2633 ∨ (¬ p3367) ∨ (¬ p2785) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3688) ∨ (¬ p2313)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial16926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory6198 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16926 (meaning t m 1986) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 2785) (meaning t m 3367) (meaning t m 3688) source

theorem rule16929 (p1979 p2027 p2098 p2588 p2780 p2997 p3497 p4188 p4342 : Prop) (h : (¬ p1979) ∨ (¬ p2588) ∨ (¬ p3497) ∨ p2997 ∨ (¬ p4342) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p4188) ∨ (¬ p2098)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3497) ∨ (¬ p4188) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial16929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory6201 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7)
  exact rule16929 (meaning t m 1979) (meaning t m 2027) (meaning t m 2098) (meaning t m 2588) (meaning t m 2780) (meaning t m 2997) (meaning t m 3497) (meaning t m 4188) (meaning t m 4342) source

theorem rule16931 (p1990 p2027 p2202 p2383 p2427 p2962 p3556 p3989 : Prop) (h : p2202 ∨ (¬ p1990) ∨ (¬ p2962) ∨ (¬ p3989) ∨ (¬ p2383) ∨ (¬ p3556) ∨ (¬ p2427) ∨ p2027) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2383) ∨ (¬ p2427) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial16931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6203 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule16931 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2383) (meaning t m 2427) (meaning t m 2962) (meaning t m 3556) (meaning t m 3989) source

theorem rule16932 (p1981 p2027 p2156 p2187 p2202 p2427 p3556 : Prop) (h : (¬ p1981) ∨ p2027 ∨ p2202 ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p2156) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial16932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory6204 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule16932 (meaning t m 1981) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2202) (meaning t m 2427) (meaning t m 3556) source

theorem rule16933 (p1987 p2027 p2241 p2352 p2387 p2449 p2577 p2699 p2810 p3027 p3347 p3487 p4137 p4625 : Prop) (h : (¬ p2241) ∨ (¬ p2449) ∨ p2699 ∨ (¬ p3027) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p2810) ∨ (¬ p3487) ∨ (¬ p4625) ∨ (¬ p1987) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p2577) ∨ (p2699) ∨ (¬ p2810) ∨ (¬ p3027) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial16933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory6205 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule16933 (meaning t m 1987) (meaning t m 2027) (meaning t m 2241) (meaning t m 2352) (meaning t m 2387) (meaning t m 2449) (meaning t m 2577) (meaning t m 2699) (meaning t m 2810) (meaning t m 3027) (meaning t m 3347) (meaning t m 3487) (meaning t m 4137) (meaning t m 4625) source

theorem rule16935 (p1994 p2027 p2475 p2534 p2630 p2764 p3177 p3877 p4444 : Prop) (h : (¬ p2534) ∨ p2027 ∨ p2764 ∨ (¬ p1994) ∨ (¬ p4444) ∨ (¬ p3177) ∨ (¬ p2475) ∨ (¬ p3877) ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2475) ∨ (¬ p2534) ∨ (¬ p2630) ∨ (p2764) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6207 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16935 (meaning t m 1994) (meaning t m 2027) (meaning t m 2475) (meaning t m 2534) (meaning t m 2630) (meaning t m 2764) (meaning t m 3177) (meaning t m 3877) (meaning t m 4444) source

theorem rule16938 (p1990 p2027 p2284 p2588 p2997 p3564 p4033 p4208 : Prop) (h : (¬ p2588) ∨ (¬ p1990) ∨ p2997 ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p4208)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p4033) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial16938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory6210 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule16938 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2588) (meaning t m 2997) (meaning t m 3564) (meaning t m 4033) (meaning t m 4208) source

theorem rule16940 (p1987 p2027 p2577 p2588 p2662 p2810 p2997 p3564 p3946 : Prop) (h : p2997 ∨ (¬ p2577) ∨ (¬ p2588) ∨ (¬ p3946) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p2662) ∨ (¬ p1987) ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2577) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial16940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory6212 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16940 (meaning t m 1987) (meaning t m 2027) (meaning t m 2577) (meaning t m 2588) (meaning t m 2662) (meaning t m 2810) (meaning t m 2997) (meaning t m 3564) (meaning t m 3946) source

theorem rule16941 (p2024 p2027 p2588 p2997 p3461 p3564 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p3461) ∨ p2027 ∨ p2997 ∨ (¬ p2024) ∨ (¬ p2588) ∨ (¬ p3564)) : (¬ p2024) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial16941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory6213 t (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule16941 (meaning t m 2024) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3461) (meaning t m 3564) (meaning t m 5284) source

theorem rule16942 (p1990 p2202 p2427 p4555 : Prop) (h : (¬ p2427) ∨ (¬ p1990) ∨ p2202 ∨ p4555) : (¬ p1990) ∨ (p2202) ∨ (¬ p2427) ∨ (p4555) := by
  classical
  tauto

theorem initial16942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 4555) := by
  have source := ElevenTheory.theory6214 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16942 (meaning t m 1990) (meaning t m 2202) (meaning t m 2427) (meaning t m 4555) source

theorem rule16944 (p4032 p4120 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p4120) ∨ p4032) : (p4032) ∨ (¬ p4120) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial16944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4032) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory6216 (m.theta 0 5) (m.theta 5 8) (m.theta 5 9)
  exact rule16944 (meaning t m 4032) (meaning t m 4120) (meaning t m 4335) source

theorem rule16945 (p1983 p2027 p2148 p2156 p2427 p3246 p4110 : Prop) (h : p2148 ∨ (¬ p1983) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4110) ∨ (¬ p2427)) : (¬ p1983) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6217 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule16945 (meaning t m 1983) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2427) (meaning t m 3246) (meaning t m 4110) source

theorem rule16946 (p2957 p3497 p4120 : Prop) (h : (¬ p4120) ∨ (¬ p2957) ∨ p3497) : (¬ p2957) ∨ (p3497) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial16946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (meaning t m 3497) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory6218 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule16946 (meaning t m 2957) (meaning t m 3497) (meaning t m 4120) source

theorem rule16949 (p2210 p2241 p4365 : Prop) (h : (¬ p2241) ∨ (¬ p4365) ∨ p2210) : (p2210) ∨ (¬ p2241) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial16949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory6221 (m.theta 0 1) (m.theta 1 3) (m.theta 1 5)
  exact rule16949 (meaning t m 2210) (meaning t m 2241) (meaning t m 4365) source

theorem rule16952 (p1994 p2027 p2202 p2427 p2727 p2957 p3556 p3662 : Prop) (h : p2027 ∨ (¬ p2957) ∨ p2202 ∨ (¬ p2727) ∨ (¬ p1994) ∨ (¬ p2427) ∨ (¬ p3662) ∨ (¬ p3556)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial16952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory6224 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule16952 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2727) (meaning t m 2957) (meaning t m 3556) (meaning t m 3662) source

theorem rule16953 (p1986 p2027 p2143 p2202 p2563 p3367 p3583 p3646 : Prop) (h : (¬ p3367) ∨ (¬ p1986) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p2563) ∨ p2027 ∨ p2202 ∨ (¬ p2143)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2143) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial16953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory6225 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16953 (meaning t m 1986) (meaning t m 2027) (meaning t m 2143) (meaning t m 2202) (meaning t m 2563) (meaning t m 3367) (meaning t m 3583) (meaning t m 3646) source

theorem rule16954 (p1992 p2027 p2136 p2202 p2427 p2598 p3556 p3585 : Prop) (h : (¬ p2136) ∨ (¬ p3556) ∨ (¬ p2598) ∨ (¬ p1992) ∨ (¬ p3585) ∨ p2202 ∨ p2027 ∨ (¬ p2427)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2136) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p3556) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial16954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6226 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule16954 (meaning t m 1992) (meaning t m 2027) (meaning t m 2136) (meaning t m 2202) (meaning t m 2427) (meaning t m 2598) (meaning t m 3556) (meaning t m 3585) source

theorem rule16957 (p1979 p2027 p2462 p2563 p3690 p3952 p4235 : Prop) (h : (¬ p3952) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p2563) ∨ p2462 ∨ (¬ p4235) ∨ (¬ p3690)) : (¬ p1979) ∨ (p2027) ∨ (p2462) ∨ (¬ p2563) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial16957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6229 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule16957 (meaning t m 1979) (meaning t m 2027) (meaning t m 2462) (meaning t m 2563) (meaning t m 3690) (meaning t m 3952) (meaning t m 4235) source

theorem rule16958 (p1986 p2027 p2766 p2780 p3366 p3367 p3956 p4342 p4347 : Prop) (h : (¬ p4342) ∨ (¬ p2780) ∨ (¬ p3956) ∨ p2766 ∨ (¬ p1986) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4347)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3956) ∨ (¬ p4342) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6230 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16958 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 2780) (meaning t m 3366) (meaning t m 3367) (meaning t m 3956) (meaning t m 4342) (meaning t m 4347) source

theorem rule16959 (p1998 p2027 p2373 p2938 p3146 p4235 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2938 ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p4235)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2373) ∨ (p2938) ∨ (¬ p3146) ∨ (¬ p4235) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6231 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16959 (meaning t m 1998) (meaning t m 2027) (meaning t m 2373) (meaning t m 2938) (meaning t m 3146) (meaning t m 4235) (meaning t m 4348) source

theorem rule16961 (p1992 p2027 p2589 p2764 p3363 p3585 p4322 p4948 : Prop) (h : (¬ p1992) ∨ p2764 ∨ (¬ p4322) ∨ (¬ p4948) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3363)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory6233 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule16961 (meaning t m 1992) (meaning t m 2027) (meaning t m 2589) (meaning t m 2764) (meaning t m 3363) (meaning t m 3585) (meaning t m 4322) (meaning t m 4948) source

theorem rule16962 (p1992 p2027 p2138 p2598 p2938 p3585 p3698 p4235 : Prop) (h : (¬ p2598) ∨ p2938 ∨ (¬ p3585) ∨ (¬ p4235) ∨ (¬ p1992) ∨ (¬ p2138) ∨ (¬ p3698) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (p2938) ∨ (¬ p3585) ∨ (¬ p3698) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial16962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6234 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule16962 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2938) (meaning t m 3585) (meaning t m 3698) (meaning t m 4235) source

theorem rule16963 (p1992 p2765 p3688 p4889 : Prop) (h : p2765 ∨ (¬ p1992) ∨ p4889 ∨ (¬ p3688)) : (¬ p1992) ∨ (p2765) ∨ (¬ p3688) ∨ (p4889) := by
  classical
  tauto

theorem initial16963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3688)) ∨ (meaning t m 4889) := by
  have source := ElevenTheory.theory6235 t (m.theta 1 2) (m.theta 2 6) (m.theta 5 6)
  exact rule16963 (meaning t m 1992) (meaning t m 2765) (meaning t m 3688) (meaning t m 4889) source

theorem rule16966 (p1992 p2027 p2766 p3583 p3758 p3989 p4347 : Prop) (h : p2027 ∨ (¬ p4347) ∨ (¬ p1992) ∨ (¬ p3989) ∨ (¬ p3583) ∨ p2766 ∨ (¬ p3758)) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6238 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16966 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3583) (meaning t m 3758) (meaning t m 3989) (meaning t m 4347) source

theorem rule16967 (p2927 p3548 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p2927) ∨ p3548) : (¬ p2927) ∨ (p3548) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial16967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (meaning t m 3548) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory6239 (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule16967 (meaning t m 2927) (meaning t m 3548) (meaning t m 3644) source

theorem rule16968 (p1997 p2027 p2542 p3043 p3359 p3680 p4425 : Prop) (h : p3043 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3359) ∨ (¬ p1997) ∨ (¬ p4425) ∨ (¬ p3680)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p3043) ∨ (¬ p3359) ∨ (¬ p3680) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial16968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory6240 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule16968 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 3043) (meaning t m 3359) (meaning t m 3680) (meaning t m 4425) source

theorem rule16969 (p1997 p2027 p2323 p2331 p2542 p2727 p4154 : Prop) (h : p2027 ∨ (¬ p2542) ∨ p2323 ∨ (¬ p2727) ∨ (¬ p2331) ∨ (¬ p4154) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory6241 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule16969 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2542) (meaning t m 2727) (meaning t m 4154) source

theorem rule16971 (p1994 p2622 p2797 p4972 : Prop) (h : p2622 ∨ (¬ p1994) ∨ (¬ p2797) ∨ p4972) : (¬ p1994) ∨ (p2622) ∨ (¬ p2797) ∨ (p4972) := by
  classical
  tauto

theorem initial16971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (meaning t m 4972) := by
  have source := ElevenTheory.theory6243 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule16971 (meaning t m 1994) (meaning t m 2622) (meaning t m 2797) (meaning t m 4972) source

theorem rule16972 (p1992 p2027 p2938 p3246 p3363 p3540 p3585 p4278 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p3246) ∨ p2938 ∨ (¬ p3363) ∨ (¬ p3585)) : (¬ p1992) ∨ (p2027) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6244 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16972 (meaning t m 1992) (meaning t m 2027) (meaning t m 2938) (meaning t m 3246) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 4278) source

theorem rule16973 (p1983 p2027 p2449 p2622 p2797 p2807 p2963 : Prop) (h : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p1983) ∨ (¬ p2963) ∨ p2027 ∨ p2622 ∨ (¬ p2797)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial16973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory6245 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9)
  exact rule16973 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2622) (meaning t m 2797) (meaning t m 2807) (meaning t m 2963) source

theorem rule16974 (p2881 p3246 p3657 : Prop) (h : (¬ p3246) ∨ (¬ p3657) ∨ p2881) : (p2881) ∨ (¬ p3246) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial16974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2881) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory6246 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16974 (meaning t m 2881) (meaning t m 3246) (meaning t m 3657) source

theorem rule16975 (p1996 p2027 p2911 p2938 p3246 p3553 p4278 : Prop) (h : p2027 ∨ p2938 ∨ (¬ p3553) ∨ (¬ p2911) ∨ (¬ p4278) ∨ (¬ p1996) ∨ (¬ p3246)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2911) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6247 t (m.theta 3 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16975 (meaning t m 1996) (meaning t m 2027) (meaning t m 2911) (meaning t m 2938) (meaning t m 3246) (meaning t m 3553) (meaning t m 4278) source

theorem rule16976 (p1998 p2027 p2373 p2938 p3256 p4235 p4312 p4348 : Prop) (h : p2938 ∨ (¬ p1998) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3256) ∨ (¬ p4235) ∨ (¬ p4312)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2373) ∨ (p2938) ∨ (¬ p3256) ∨ (¬ p4235) ∨ (¬ p4312) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6248 t (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16976 (meaning t m 1998) (meaning t m 2027) (meaning t m 2373) (meaning t m 2938) (meaning t m 3256) (meaning t m 4235) (meaning t m 4312) (meaning t m 4348) source

theorem rule16978 (p1976 p2027 p2138 p2765 p2901 p3952 p4244 : Prop) (h : p2765 ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p3952) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2901)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6250 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16978 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2765) (meaning t m 2901) (meaning t m 3952) (meaning t m 4244) source

theorem rule16979 (p1981 p2027 p2352 p2588 p2699 p3093 p3309 : Prop) (h : (¬ p2352) ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2027 ∨ p2699 ∨ (¬ p2588) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial16979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory6251 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16979 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) source

theorem rule16980 (p1998 p2027 p2911 p2922 p3379 p3591 p3818 : Prop) (h : p2027 ∨ p3818 ∨ (¬ p3379) ∨ (¬ p2911) ∨ (¬ p1998) ∨ (¬ p2922) ∨ (¬ p3591)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (p3818) := by
  classical
  tauto

theorem initial16980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (meaning t m 3818) := by
  have source := ElevenTheory.theory6252 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 7 8)
  exact rule16980 (meaning t m 1998) (meaning t m 2027) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3591) (meaning t m 3818) source

theorem rule16982 (p1998 p2027 p2499 p2842 p2911 p2922 p3422 : Prop) (h : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p1998) ∨ p2027 ∨ p2842 ∨ (¬ p3422)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2499) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial16982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory6254 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule16982 (meaning t m 1998) (meaning t m 2027) (meaning t m 2499) (meaning t m 2842) (meaning t m 2911) (meaning t m 2922) (meaning t m 3422) source

theorem rule16983 (p1991 p2027 p2810 p3005 p3008 p3172 p3574 : Prop) (h : (¬ p1991) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3005) ∨ p3008 ∨ (¬ p3574) ∨ (¬ p3172)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (p3008) ∨ (¬ p3172) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial16983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory6255 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6)
  exact rule16983 (meaning t m 1991) (meaning t m 2027) (meaning t m 2810) (meaning t m 3005) (meaning t m 3008) (meaning t m 3172) (meaning t m 3574) source

theorem rule16984 (p1998 p2027 p2499 p2545 p2911 p2922 p3016 : Prop) (h : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p1998) ∨ p2545 ∨ p2027 ∨ (¬ p3016)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2499) ∨ (p2545) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial16984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory6256 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule16984 (meaning t m 1998) (meaning t m 2027) (meaning t m 2499) (meaning t m 2545) (meaning t m 2911) (meaning t m 2922) (meaning t m 3016) source

theorem rule16985 (p1991 p2027 p2545 p2952 p3016 p3136 p3364 p3584 : Prop) (h : (¬ p1991) ∨ p2027 ∨ p2545 ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3016)) : (¬ p1991) ∨ (p2027) ∨ (p2545) ∨ (¬ p2952) ∨ (¬ p3016) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial16985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory6257 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule16985 (meaning t m 1991) (meaning t m 2027) (meaning t m 2545) (meaning t m 2952) (meaning t m 3016) (meaning t m 3136) (meaning t m 3364) (meaning t m 3584) source

theorem rule16987 (p1977 p2027 p2946 p2963 p2997 p3568 p3662 : Prop) (h : (¬ p2963) ∨ (¬ p1977) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3662)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial16987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory6259 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule16987 (meaning t m 1977) (meaning t m 2027) (meaning t m 2946) (meaning t m 2963) (meaning t m 2997) (meaning t m 3568) (meaning t m 3662) source

theorem rule16988 (p1989 p2027 p2210 p2881 p2938 p3548 p4366 : Prop) (h : (¬ p2210) ∨ (¬ p3548) ∨ (¬ p1989) ∨ (¬ p4366) ∨ p2027 ∨ p2938 ∨ (¬ p2881)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory6260 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule16988 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2881) (meaning t m 2938) (meaning t m 3548) (meaning t m 4366) source

theorem rule16990 (p1988 p2027 p2579 p2842 p3276 p3355 p3422 : Prop) (h : (¬ p3276) ∨ (¬ p1988) ∨ (¬ p2579) ∨ p2842 ∨ (¬ p3355) ∨ (¬ p3422) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2579) ∨ (p2842) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial16990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory6262 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule16990 (meaning t m 1988) (meaning t m 2027) (meaning t m 2579) (meaning t m 2842) (meaning t m 3276) (meaning t m 3355) (meaning t m 3422) source

theorem rule16991 (p1975 p2027 p2287 p2299 p2341 p2685 p4066 p4195 : Prop) (h : (¬ p4195) ∨ p2287 ∨ (¬ p4066) ∨ (¬ p2341) ∨ (¬ p2685) ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (p2287) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2685) ∨ (¬ p4066) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial16991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory6263 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16991 (meaning t m 1975) (meaning t m 2027) (meaning t m 2287) (meaning t m 2299) (meaning t m 2341) (meaning t m 2685) (meaning t m 4066) (meaning t m 4195) source

theorem rule16992 (p1997 p2027 p2619 p2633 p3570 p3880 p4244 : Prop) (h : p2027 ∨ (¬ p4244) ∨ (¬ p3880) ∨ (¬ p1997) ∨ (¬ p3570) ∨ p2633 ∨ (¬ p2619)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2619) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p3880) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6264 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule16992 (meaning t m 1997) (meaning t m 2027) (meaning t m 2619) (meaning t m 2633) (meaning t m 3570) (meaning t m 3880) (meaning t m 4244) source

theorem rule16994 (p2020 p2027 p2373 p2406 p2699 p3379 p3969 : Prop) (h : (¬ p3379) ∨ (¬ p2373) ∨ p2027 ∨ p2699 ∨ (¬ p2406) ∨ (¬ p2020) ∨ (¬ p3969)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial16994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory6266 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule16994 (meaning t m 2020) (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2699) (meaning t m 3379) (meaning t m 3969) source

theorem rule16995 (p1976 p2027 p2104 p2766 p3941 p4348 p5612 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p2104) ∨ (¬ p5612) ∨ (¬ p3941) ∨ p2766 ∨ (¬ p4348)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2104) ∨ (p2766) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial16995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory6267 t (m.theta 0 2) (m.theta 2 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule16995 (meaning t m 1976) (meaning t m 2027) (meaning t m 2104) (meaning t m 2766) (meaning t m 3941) (meaning t m 4348) (meaning t m 5612) source

theorem rule16999 (p1985 p2027 p2233 p2396 p2553 p2573 p3690 : Prop) (h : (¬ p2553) ∨ (¬ p3690) ∨ p2233 ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2573) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2233) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial16999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory6271 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16999 (meaning t m 1985) (meaning t m 2027) (meaning t m 2233) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3690) source

theorem rule17002 (p1976 p2027 p3146 p3365 p3578 p3877 p4118 : Prop) (h : (¬ p3877) ∨ p2027 ∨ p3578 ∨ (¬ p1976) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p3146)) : (¬ p1976) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (p3578) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory6274 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17002 (meaning t m 1976) (meaning t m 2027) (meaning t m 3146) (meaning t m 3365) (meaning t m 3578) (meaning t m 3877) (meaning t m 4118) source

theorem rule17003 (p1976 p2027 p2138 p2764 p3690 p4244 p4381 : Prop) (h : (¬ p1976) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3690) ∨ p2764 ∨ (¬ p4381)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2764) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6275 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17003 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2764) (meaning t m 3690) (meaning t m 4244) (meaning t m 4381) source

theorem rule17004 (p1979 p2027 p2633 p2946 p3246 p3570 p3821 p4849 : Prop) (h : (¬ p1979) ∨ (¬ p3570) ∨ p2027 ∨ p2633 ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p4849) ∨ (¬ p3821)) : (¬ p1979) ∨ (p2027) ∨ (p2633) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial17004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory6276 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17004 (meaning t m 1979) (meaning t m 2027) (meaning t m 2633) (meaning t m 2946) (meaning t m 3246) (meaning t m 3570) (meaning t m 3821) (meaning t m 4849) source

theorem rule17005 (p1991 p2027 p2588 p2630 p2657 p2997 p4195 p4389 : Prop) (h : (¬ p1991) ∨ p2027 ∨ p2997 ∨ (¬ p2657) ∨ (¬ p2588) ∨ (¬ p4195) ∨ (¬ p2630) ∨ (¬ p4389)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2997) ∨ (¬ p4195) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial17005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory6277 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule17005 (meaning t m 1991) (meaning t m 2027) (meaning t m 2588) (meaning t m 2630) (meaning t m 2657) (meaning t m 2997) (meaning t m 4195) (meaning t m 4389) source

theorem rule17009 (p2005 p2545 p2573 p2659 : Prop) (h : (¬ p2005) ∨ p2545 ∨ (¬ p2573) ∨ p2659) : (¬ p2005) ∨ (p2545) ∨ (¬ p2573) ∨ (p2659) := by
  classical
  tauto

theorem initial17009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2659) := by
  have source := ElevenTheory.theory6281 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6)
  exact rule17009 (meaning t m 2005) (meaning t m 2545) (meaning t m 2573) (meaning t m 2659) source

theorem rule17010 (p1997 p2938 p4244 p4885 : Prop) (h : (¬ p4244) ∨ p2938 ∨ (¬ p1997) ∨ p4885) : (¬ p1997) ∨ (p2938) ∨ (¬ p4244) ∨ (p4885) := by
  classical
  tauto

theorem initial17010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4244)) ∨ (meaning t m 4885) := by
  have source := ElevenTheory.theory6282 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule17010 (meaning t m 1997) (meaning t m 2938) (meaning t m 4244) (meaning t m 4885) source

theorem rule17012 (p2000 p2027 p2440 p2476 p2765 p3083 p4110 : Prop) (h : (¬ p2000) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2476) ∨ (¬ p4110) ∨ p2765) : (¬ p2000) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (p2765) ∨ (¬ p3083) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6284 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule17012 (meaning t m 2000) (meaning t m 2027) (meaning t m 2440) (meaning t m 2476) (meaning t m 2765) (meaning t m 3083) (meaning t m 4110) source

theorem rule17014 (p1994 p2027 p2608 p2630 p2699 p3309 p3822 p4841 p4869 : Prop) (h : (¬ p3822) ∨ p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4869) ∨ (¬ p2630) ∨ (¬ p3309) ∨ (¬ p4841) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial17014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory6286 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 6 7)
  exact rule17014 (meaning t m 1994) (meaning t m 2027) (meaning t m 2608) (meaning t m 2630) (meaning t m 2699) (meaning t m 3309) (meaning t m 3822) (meaning t m 4841) (meaning t m 4869) source

theorem rule17015 (p1998 p2027 p2177 p2247 p2688 p3093 p3309 : Prop) (h : (¬ p2247) ∨ (¬ p1998) ∨ (¬ p3309) ∨ (¬ p2177) ∨ p2688 ∨ p2027 ∨ (¬ p3093)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3093) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial17015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory6287 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17015 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2688) (meaning t m 3093) (meaning t m 3309) source

theorem rule17016 (p2027 p2727 p2946 p2963 p3368 p3412 p4972 : Prop) (h : (¬ p4972) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3368)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3368) ∨ (¬ p3412) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial17016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory6288 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule17016 (meaning t m 2027) (meaning t m 2727) (meaning t m 2946) (meaning t m 2963) (meaning t m 3368) (meaning t m 3412) (meaning t m 4972) source

theorem rule17017 (p1998 p2027 p2437 p2528 p3008 p3574 p3875 p4348 : Prop) (h : (¬ p2528) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3875) ∨ (¬ p2437) ∨ (¬ p1998) ∨ p3008 ∨ (¬ p3574)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2528) ∨ (p3008) ∨ (¬ p3574) ∨ (¬ p3875) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6289 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17017 (meaning t m 1998) (meaning t m 2027) (meaning t m 2437) (meaning t m 2528) (meaning t m 3008) (meaning t m 3574) (meaning t m 3875) (meaning t m 4348) source

theorem rule17019 (p1998 p2027 p2177 p2766 p3266 p4107 p4381 : Prop) (h : (¬ p3266) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p4107) ∨ p2766 ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6291 t (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17019 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2766) (meaning t m 3266) (meaning t m 4107) (meaning t m 4381) source

theorem rule17020 (p1976 p2027 p2441 p2938 p3055 p3246 p3684 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p1976) ∨ p2938 ∨ (¬ p2441) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p3684)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2441) ∨ (p2938) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3684) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial17020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6292 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule17020 (meaning t m 1976) (meaning t m 2027) (meaning t m 2441) (meaning t m 2938) (meaning t m 3055) (meaning t m 3246) (meaning t m 3684) (meaning t m 4278) source

theorem rule17023 (p1991 p2027 p2589 p2655 p2765 p3156 p3880 p3952 : Prop) (h : (¬ p3156) ∨ (¬ p1991) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p2589) ∨ p2765 ∨ (¬ p3880)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (p2765) ∨ (¬ p3156) ∨ (¬ p3880) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial17023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6295 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17023 (meaning t m 1991) (meaning t m 2027) (meaning t m 2589) (meaning t m 2655) (meaning t m 2765) (meaning t m 3156) (meaning t m 3880) (meaning t m 3952) source

theorem rule17024 (p1995 p2027 p2860 p2938 p3238 p4110 p4244 : Prop) (h : (¬ p4110) ∨ (¬ p1995) ∨ (¬ p3238) ∨ p2027 ∨ p2938 ∨ (¬ p4244) ∨ (¬ p2860)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2860) ∨ (p2938) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial17024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6296 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17024 (meaning t m 1995) (meaning t m 2027) (meaning t m 2860) (meaning t m 2938) (meaning t m 3238) (meaning t m 4110) (meaning t m 4244) source

theorem rule17026 (p1991 p2027 p2589 p2655 p2765 p2901 p3952 p4235 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2655) ∨ (¬ p1991) ∨ (¬ p4235) ∨ (¬ p2901) ∨ (¬ p2589)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6298 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17026 (meaning t m 1991) (meaning t m 2027) (meaning t m 2589) (meaning t m 2655) (meaning t m 2765) (meaning t m 2901) (meaning t m 3952) (meaning t m 4235) source

theorem rule17027 (p1997 p2027 p2764 p3570 p4235 p4348 p4444 : Prop) (h : (¬ p3570) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4444) ∨ p2764 ∨ (¬ p4235) ∨ (¬ p4348)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6299 t (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17027 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 3570) (meaning t m 4235) (meaning t m 4348) (meaning t m 4444) source

theorem rule17028 (p1991 p2027 p2534 p2657 p2764 p4256 p4444 : Prop) (h : (¬ p2534) ∨ (¬ p4256) ∨ p2764 ∨ p2027 ∨ (¬ p1991) ∨ (¬ p4444) ∨ (¬ p2657)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p4256) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6300 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17028 (meaning t m 1991) (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 2764) (meaning t m 4256) (meaning t m 4444) source

theorem rule17031 (p1997 p2027 p2220 p2409 p2493 p2579 p3880 p4399 : Prop) (h : (¬ p2579) ∨ (¬ p2493) ∨ (¬ p1997) ∨ p2409 ∨ p2027 ∨ (¬ p2220) ∨ (¬ p4399) ∨ (¬ p3880)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2220) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial17031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory6303 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule17031 (meaning t m 1997) (meaning t m 2027) (meaning t m 2220) (meaning t m 2409) (meaning t m 2493) (meaning t m 2579) (meaning t m 3880) (meaning t m 4399) source

theorem rule17032 (p1998 p2027 p2287 p3005 p3256 p4195 p4348 : Prop) (h : (¬ p4195) ∨ (¬ p3005) ∨ (¬ p1998) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3256) ∨ p2287) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4195) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6304 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17032 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 3005) (meaning t m 3256) (meaning t m 4195) (meaning t m 4348) source

theorem rule17033 (p1976 p2027 p2764 p3365 p4208 p4315 p4322 : Prop) (h : (¬ p3365) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p4208) ∨ (¬ p4322) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3365) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial17033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory6305 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule17033 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3365) (meaning t m 4208) (meaning t m 4315) (meaning t m 4322) source

theorem rule17037 (p1997 p2027 p2274 p2406 p2579 p2588 p2765 p3347 : Prop) (h : (¬ p2406) ∨ (¬ p1997) ∨ (¬ p3347) ∨ p2027 ∨ p2765 ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p2274)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2406) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial17037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory6309 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17037 (meaning t m 1997) (meaning t m 2027) (meaning t m 2274) (meaning t m 2406) (meaning t m 2579) (meaning t m 2588) (meaning t m 2765) (meaning t m 3347) source

theorem rule17042 (p1984 p2027 p2191 p2764 p3555 p3692 p4444 : Prop) (h : (¬ p1984) ∨ (¬ p2191) ∨ (¬ p3692) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4444) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (p2764) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6314 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17042 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2764) (meaning t m 3555) (meaning t m 3692) (meaning t m 4444) source

theorem rule17043 (p1983 p2027 p2396 p2611 p3471 p4253 p4260 : Prop) (h : (¬ p4253) ∨ (¬ p1983) ∨ p2611 ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p3471)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2396) ∨ (p2611) ∨ (¬ p3471) ∨ (¬ p4253) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial17043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory6315 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule17043 (meaning t m 1983) (meaning t m 2027) (meaning t m 2396) (meaning t m 2611) (meaning t m 3471) (meaning t m 4253) (meaning t m 4260) source

theorem rule17044 (p1984 p2027 p2274 p2499 p2588 p2765 p3452 : Prop) (h : (¬ p1984) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p2274) ∨ p2765) : (¬ p1984) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial17044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory6316 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17044 (meaning t m 1984) (meaning t m 2027) (meaning t m 2274) (meaning t m 2499) (meaning t m 2588) (meaning t m 2765) (meaning t m 3452) source

theorem rule17045 (p1977 p2027 p2241 p2499 p2545 p3016 p3452 : Prop) (h : p2545 ∨ (¬ p2499) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p1977) ∨ (¬ p2241) ∨ (¬ p3452)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2499) ∨ (p2545) ∨ (¬ p3016) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial17045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory6317 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule17045 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2499) (meaning t m 2545) (meaning t m 3016) (meaning t m 3452) source

theorem rule17046 (p1984 p2027 p2352 p2588 p2997 p3591 p3923 : Prop) (h : (¬ p2352) ∨ p2027 ∨ p2997 ∨ (¬ p2588) ∨ (¬ p1984) ∨ (¬ p3591) ∨ (¬ p3923)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial17046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory6318 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17046 (meaning t m 1984) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2997) (meaning t m 3591) (meaning t m 3923) source

theorem rule17049 (p1976 p2027 p2764 p3365 p3877 p4118 p4444 : Prop) (h : p2764 ∨ (¬ p4444) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6321 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17049 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) (meaning t m 4444) source

theorem rule17051 (p1987 p2027 p2545 p2737 p3016 p3584 p3585 : Prop) (h : (¬ p1987) ∨ (¬ p2737) ∨ p2545 ∨ (¬ p3584) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3585)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2737) ∨ (¬ p3016) ∨ (¬ p3584) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6323 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule17051 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2737) (meaning t m 3016) (meaning t m 3584) (meaning t m 3585) source

theorem rule17052 (p1992 p2027 p2743 p2765 p2950 p3115 p3361 p3952 p4032 : Prop) (h : (¬ p4032) ∨ (¬ p2743) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3115) ∨ p2765 ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2765) ∨ (¬ p2950) ∨ (¬ p3115) ∨ (¬ p3361) ∨ (¬ p3952) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial17052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory6324 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule17052 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2765) (meaning t m 2950) (meaning t m 3115) (meaning t m 3361) (meaning t m 3952) (meaning t m 4032) source

theorem rule17053 (p1992 p2027 p2499 p2545 p2608 p3016 p3452 : Prop) (h : (¬ p2608) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3016) ∨ p2545) : (¬ p1992) ∨ (p2027) ∨ (¬ p2499) ∨ (p2545) ∨ (¬ p2608) ∨ (¬ p3016) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial17053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory6325 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule17053 (meaning t m 1992) (meaning t m 2027) (meaning t m 2499) (meaning t m 2545) (meaning t m 2608) (meaning t m 3016) (meaning t m 3452) source

theorem rule17054 (p1975 p2027 p2299 p2579 p2911 p3008 p3389 : Prop) (h : (¬ p1975) ∨ (¬ p2579) ∨ (¬ p2299) ∨ p2027 ∨ p3008 ∨ (¬ p2911) ∨ (¬ p3389)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2911) ∨ (p3008) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial17054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory6326 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17054 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2911) (meaning t m 3008) (meaning t m 3389) source

theorem rule17056 (p1977 p2027 p2241 p2764 p3412 p3555 p4208 p4322 : Prop) (h : (¬ p3412) ∨ (¬ p1977) ∨ (¬ p4208) ∨ (¬ p4322) ∨ p2027 ∨ p2764 ∨ (¬ p2241) ∨ (¬ p3555)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2764) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial17056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory6328 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule17056 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2764) (meaning t m 3412) (meaning t m 3555) (meaning t m 4208) (meaning t m 4322) source

theorem rule17060 (p1983 p2027 p2114 p2295 p2331 p2396 p2737 p2811 : Prop) (h : (¬ p2811) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p2331) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2737) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial17060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory6332 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17060 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2737) (meaning t m 2811) source

theorem rule17061 (p1998 p2027 p2264 p2307 p2344 p2396 p3947 : Prop) (h : p2027 ∨ p2344 ∨ (¬ p3947) ∨ (¬ p2264) ∨ (¬ p1998) ∨ (¬ p2307) ∨ (¬ p2396)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p2396) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial17061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory6333 t (m.theta 0 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17061 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2307) (meaning t m 2344) (meaning t m 2396) (meaning t m 3947) source

theorem rule17062 (p1998 p2027 p2323 p2331 p2363 p2668 p4348 : Prop) (h : p2323 ∨ (¬ p2363) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p1998) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6334 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17062 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 4348) source

theorem rule17063 (p1976 p2027 p2138 p2839 p3008 p3584 p3585 : Prop) (h : p3008 ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3584)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (p3008) ∨ (¬ p3584) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6335 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule17063 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2839) (meaning t m 3008) (meaning t m 3584) (meaning t m 3585) source

theorem rule17064 (p1992 p2027 p2499 p2608 p2842 p3422 p3452 : Prop) (h : (¬ p1992) ∨ p2842 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3422) ∨ (¬ p2499)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2608) ∨ (p2842) ∨ (¬ p3422) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial17064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory6336 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule17064 (meaning t m 1992) (meaning t m 2027) (meaning t m 2499) (meaning t m 2608) (meaning t m 2842) (meaning t m 3422) (meaning t m 3452) source

theorem rule17067 (p1997 p2027 p2462 p2542 p2579 p2588 p2662 p4107 : Prop) (h : (¬ p2542) ∨ (¬ p2662) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2588) ∨ p2462 ∨ (¬ p4107)) : (¬ p1997) ∨ (p2027) ∨ (p2462) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial17067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6339 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17067 (meaning t m 1997) (meaning t m 2027) (meaning t m 2462) (meaning t m 2542) (meaning t m 2579) (meaning t m 2588) (meaning t m 2662) (meaning t m 4107) source

theorem rule17069 (p1997 p2027 p2274 p2542 p2579 p2588 p2662 p2765 : Prop) (h : (¬ p2662) ∨ (¬ p2588) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2579) ∨ (¬ p2274) ∨ p2765) : (¬ p1997) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (p2765) := by
  classical
  tauto

theorem initial17069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2765) := by
  have source := ElevenTheory.theory6341 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17069 (meaning t m 1997) (meaning t m 2027) (meaning t m 2274) (meaning t m 2542) (meaning t m 2579) (meaning t m 2588) (meaning t m 2662) (meaning t m 2765) source

theorem rule17070 (p1997 p2027 p2542 p2622 p2662 p2743 p2922 p3540 p3541 : Prop) (h : p2027 ∨ (¬ p2542) ∨ (¬ p3540) ∨ (¬ p2662) ∨ (¬ p3541) ∨ (¬ p1997) ∨ (¬ p2922) ∨ (¬ p2743) ∨ p2622) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2622) ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial17070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory6342 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule17070 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2622) (meaning t m 2662) (meaning t m 2743) (meaning t m 2922) (meaning t m 3540) (meaning t m 3541) source

theorem rule17072 (p1997 p2027 p2166 p2476 p2542 p2662 p2765 p3693 p4173 : Prop) (h : (¬ p3693) ∨ p2765 ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2476) ∨ (¬ p2542) ∨ (¬ p1997) ∨ (¬ p2662)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2476) ∨ (¬ p2542) ∨ (¬ p2662) ∨ (p2765) ∨ (¬ p3693) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory6344 t (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule17072 (meaning t m 1997) (meaning t m 2027) (meaning t m 2166) (meaning t m 2476) (meaning t m 2542) (meaning t m 2662) (meaning t m 2765) (meaning t m 3693) (meaning t m 4173) source

theorem rule17073 (p1988 p3461 p4206 p5249 : Prop) (h : (¬ p3461) ∨ p5249 ∨ (¬ p1988) ∨ p4206) : (¬ p1988) ∨ (¬ p3461) ∨ (p4206) ∨ (p5249) := by
  classical
  tauto

theorem initial17073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (¬ (meaning t m 3461)) ∨ (meaning t m 4206) ∨ (meaning t m 5249) := by
  have source := ElevenTheory.theory6345 t (m.theta 6 10) (m.theta 6 9) (m.theta 9 10)
  exact rule17073 (meaning t m 1988) (meaning t m 3461) (meaning t m 4206) (meaning t m 5249) source

theorem rule17076 (p1988 p2027 p2449 p2622 p2707 p2743 p2761 p4325 : Prop) (h : (¬ p2761) ∨ (¬ p2449) ∨ (¬ p2743) ∨ p2027 ∨ p2622 ∨ (¬ p4325) ∨ (¬ p1988) ∨ (¬ p2707)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2449) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2761) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial17076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory6348 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17076 (meaning t m 1988) (meaning t m 2027) (meaning t m 2449) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 2761) (meaning t m 4325) source

theorem rule17078 (p1997 p2027 p2230 p2493 p2579 p2914 p2928 : Prop) (h : (¬ p1997) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2493) ∨ p2914) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (p2914) ∨ (¬ p2928) := by
  classical
  tauto

theorem initial17078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2928)) := by
  have source := ElevenTheory.theory6350 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule17078 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2493) (meaning t m 2579) (meaning t m 2914) (meaning t m 2928) source

theorem rule17080 (p1997 p2027 p2542 p2766 p3266 p3359 p4425 : Prop) (h : (¬ p4425) ∨ (¬ p3266) ∨ p2027 ∨ p2766 ∨ (¬ p2542) ∨ (¬ p3359) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial17080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory6352 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17080 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2766) (meaning t m 3266) (meaning t m 3359) (meaning t m 4425) source

theorem rule17084 (p1977 p2027 p2579 p2662 p2764 p4111 p4137 p4191 : Prop) (h : p2764 ∨ (¬ p4191) ∨ (¬ p1977) ∨ (¬ p4137) ∨ (¬ p2579) ∨ (¬ p4111) ∨ (¬ p2662) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p4111) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial17084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6356 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule17084 (meaning t m 1977) (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2764) (meaning t m 4111) (meaning t m 4137) (meaning t m 4191) source

theorem rule17085 (p1982 p2027 p2459 p2765 p2881 p3051 p3646 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p3051) ∨ (¬ p1982) ∨ (¬ p2881) ∨ (¬ p2459) ∨ (¬ p3646)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial17085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory6357 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17085 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2765) (meaning t m 2881) (meaning t m 3051) (meaning t m 3646) source

theorem rule17086 (p1982 p2027 p2323 p2459 p2807 p4009 p4044 p5558 : Prop) (h : p2323 ∨ (¬ p4044) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p5558) ∨ (¬ p4009)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial17086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory6358 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17086 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2459) (meaning t m 2807) (meaning t m 4009) (meaning t m 4044) (meaning t m 5558) source

theorem rule17088 (p2957 p3156 p3696 p3697 : Prop) (h : (¬ p2957) ∨ (¬ p3697) ∨ (¬ p3696) ∨ (¬ p3156)) : (¬ p2957) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p3697) := by
  classical
  tauto

theorem initial17088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3697)) := by
  have source := ElevenTheory.theory6360 (m.theta 0 5) (m.theta 0 8) (m.theta 3 5) (m.theta 5 8)
  exact rule17088 (meaning t m 2957) (meaning t m 3156) (meaning t m 3696) (meaning t m 3697) source

theorem rule17091 (p1982 p2027 p2247 p2363 p2668 p2688 p3093 p3922 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p1982) ∨ (¬ p2247) ∨ (¬ p2668) ∨ (¬ p3093) ∨ (¬ p2363) ∨ (¬ p3922)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (p2688) ∨ (¬ p3093) ∨ (¬ p3922) := by
  classical
  tauto

theorem initial17091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3922)) := by
  have source := ElevenTheory.theory6363 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17091 (meaning t m 1982) (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2668) (meaning t m 2688) (meaning t m 3093) (meaning t m 3922) source

theorem rule17092 (p2246 p2807 p2996 : Prop) (h : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2996)) : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial17092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory6364 (m.theta 0 3) (m.theta 1 3) (m.theta 3 7)
  exact rule17092 (meaning t m 2246) (meaning t m 2807) (meaning t m 2996) source

theorem rule17097 (p1994 p2027 p2499 p2518 p2588 p2997 p4256 : Prop) (h : (¬ p2588) ∨ (¬ p1994) ∨ p2997 ∨ (¬ p4256) ∨ (¬ p2518) ∨ (¬ p2499) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial17097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory6369 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule17097 (meaning t m 1994) (meaning t m 2027) (meaning t m 2499) (meaning t m 2518) (meaning t m 2588) (meaning t m 2997) (meaning t m 4256) source

theorem rule17098 (p1984 p2027 p3008 p3193 p3333 p3452 p3584 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p3452) ∨ (¬ p3193) ∨ p3008 ∨ (¬ p3333)) : (¬ p1984) ∨ (p2027) ∨ (p3008) ∨ (¬ p3193) ∨ (¬ p3333) ∨ (¬ p3452) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial17098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory6370 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9)
  exact rule17098 (meaning t m 1984) (meaning t m 2027) (meaning t m 3008) (meaning t m 3193) (meaning t m 3333) (meaning t m 3452) (meaning t m 3584) source

theorem rule17099 (p1982 p2027 p2363 p2622 p2668 p2743 p2829 p4328 : Prop) (h : p2622 ∨ (¬ p2668) ∨ (¬ p4328) ∨ (¬ p1982) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2829)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2622) ∨ (¬ p2668) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial17099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory6371 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17099 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2622) (meaning t m 2668) (meaning t m 2743) (meaning t m 2829) (meaning t m 4328) source

theorem rule17100 (p1982 p2027 p2114 p2331 p2363 p2668 p2737 p2811 : Prop) (h : (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p2811)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial17100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory6372 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17100 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2737) (meaning t m 2811) source

theorem rule17101 (p1992 p2027 p2608 p2764 p3193 p3452 p4425 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p3452) ∨ (¬ p1992) ∨ (¬ p3193) ∨ (¬ p4425) ∨ p2764) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial17101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory6373 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 9) (m.theta 9 10)
  exact rule17101 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2764) (meaning t m 3193) (meaning t m 3452) (meaning t m 4425) source

theorem rule17104 (p2000 p2027 p2476 p2499 p2518 p2588 p2997 : Prop) (h : (¬ p2499) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p2588) ∨ p2997 ∨ (¬ p2476) ∨ (¬ p2518)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588) ∨ (p2997) := by
  classical
  tauto

theorem initial17104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) := by
  have source := ElevenTheory.theory6376 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule17104 (meaning t m 2000) (meaning t m 2027) (meaning t m 2476) (meaning t m 2499) (meaning t m 2518) (meaning t m 2588) (meaning t m 2997) source

theorem rule17106 (p1983 p2027 p2409 p2417 p2493 p2579 p3389 : Prop) (h : (¬ p1983) ∨ (¬ p2493) ∨ p2409 ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p2579)) : (¬ p1983) ∨ (p2027) ∨ (p2409) ∨ (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial17106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory6378 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule17106 (meaning t m 1983) (meaning t m 2027) (meaning t m 2409) (meaning t m 2417) (meaning t m 2493) (meaning t m 2579) (meaning t m 3389) source

theorem rule17109 (p1982 p2027 p2264 p2459 p2611 p2685 p2696 : Prop) (h : (¬ p1982) ∨ p2611 ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2459) ∨ (¬ p2685)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (p2611) ∨ (¬ p2685) ∨ (¬ p2696) := by
  classical
  tauto

theorem initial17109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) := by
  have source := ElevenTheory.theory6381 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17109 (meaning t m 1982) (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2611) (meaning t m 2685) (meaning t m 2696) source

theorem rule17112 (p1997 p2027 p2323 p2474 p2542 p2662 p3166 p3256 p3857 : Prop) (h : p2323 ∨ (¬ p2662) ∨ (¬ p3256) ∨ (¬ p2542) ∨ (¬ p3166) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2474)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2474) ∨ (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial17112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory6384 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 8) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 8 9)
  exact rule17112 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2474) (meaning t m 2542) (meaning t m 2662) (meaning t m 3166) (meaning t m 3256) (meaning t m 3857) source

theorem rule17113 (p1982 p2027 p2363 p2611 p2668 p2696 p2797 : Prop) (h : (¬ p2363) ∨ (¬ p1982) ∨ p2611 ∨ p2027 ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) := by
  classical
  tauto

theorem initial17113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) := by
  have source := ElevenTheory.theory6385 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17113 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2611) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) source

theorem rule17116 (p1998 p2027 p2323 p2427 p2542 p2651 p2881 : Prop) (h : (¬ p2651) ∨ (¬ p2881) ∨ (¬ p2542) ∨ (¬ p2427) ∨ p2323 ∨ p2027 ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial17116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory6388 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17116 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2427) (meaning t m 2542) (meaning t m 2651) (meaning t m 2881) source

theorem rule17119 (p1984 p2027 p2633 p3585 p3644 p3876 p3954 : Prop) (h : (¬ p1984) ∨ p2633 ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3644) ∨ (¬ p3876)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6391 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule17119 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3585) (meaning t m 3644) (meaning t m 3876) (meaning t m 3954) source

theorem rule17121 (p1992 p2027 p2608 p2717 p2842 p3548 p4366 p5085 : Prop) (h : (¬ p5085) ∨ p2842 ∨ (¬ p2717) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3548) ∨ (¬ p1992) ∨ (¬ p4366)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2717) ∨ (p2842) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial17121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory6393 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule17121 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2717) (meaning t m 2842) (meaning t m 3548) (meaning t m 4366) (meaning t m 5085) source

theorem rule17123 (p1984 p2027 p2928 p2938 p3246 p3452 p4278 : Prop) (h : (¬ p2928) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p1984) ∨ p2938 ∨ (¬ p3246)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2928) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial17123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6395 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule17123 (meaning t m 1984) (meaning t m 2027) (meaning t m 2928) (meaning t m 2938) (meaning t m 3246) (meaning t m 3452) (meaning t m 4278) source

theorem rule17125 (p1992 p2027 p2143 p2764 p3583 p3692 p4120 p4444 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p1992) ∨ (¬ p3583) ∨ p2764 ∨ (¬ p2143) ∨ (¬ p4444)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6397 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17125 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2764) (meaning t m 3583) (meaning t m 3692) (meaning t m 4120) (meaning t m 4444) source

theorem rule17127 (p2009 p2409 p2478 p2518 : Prop) (h : p2409 ∨ p2478 ∨ (¬ p2009) ∨ (¬ p2518)) : (¬ p2009) ∨ (p2409) ∨ (p2478) ∨ (¬ p2518) := by
  classical
  tauto

theorem initial17127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2409) ∨ (meaning t m 2478) ∨ (¬ (meaning t m 2518)) := by
  have source := ElevenTheory.theory6399 t (m.theta 0 8) (m.theta 1 4) (m.theta 4 8)
  exact rule17127 (meaning t m 2009) (meaning t m 2409) (meaning t m 2478) (meaning t m 2518) source

theorem rule17134 (p2027 p3172 p3516 p3947 p4104 p4386 p5062 : Prop) (h : (¬ p3516) ∨ (¬ p4104) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p5062) ∨ p2027 ∨ (¬ p3172)) : (p2027) ∨ (¬ p3172) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4104) ∨ (¬ p4386) ∨ (¬ p5062) := by
  classical
  tauto

theorem initial17134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 5062)) := by
  have source := ElevenTheory.theory6406 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 3 8) (m.theta 7 9)
  exact rule17134 (meaning t m 2027) (meaning t m 3172) (meaning t m 3516) (meaning t m 3947) (meaning t m 4104) (meaning t m 4386) (meaning t m 5062) source

theorem rule17138 (p2004 p3791 p4206 p4442 p5472 : Prop) (h : p4206 ∨ (¬ p2004) ∨ p5472 ∨ (¬ p3791) ∨ (¬ p4442)) : (¬ p2004) ∨ (¬ p3791) ∨ (p4206) ∨ (¬ p4442) ∨ (p5472) := by
  classical
  tauto

theorem initial17138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (¬ (meaning t m 3791)) ∨ (meaning t m 4206) ∨ (¬ (meaning t m 4442)) ∨ (meaning t m 5472) := by
  have source := ElevenTheory.theory6410 t (m.theta 1 7) (m.theta 6 10) (m.theta 6 7) (m.theta 7 10)
  exact rule17138 (meaning t m 2004) (meaning t m 3791) (meaning t m 4206) (meaning t m 4442) (meaning t m 5472) source

theorem rule17139 (p1984 p2027 p2138 p2462 p2839 p3588 p3690 p3873 p4169 : Prop) (h : (¬ p1984) ∨ (¬ p3588) ∨ p2462 ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p4169) ∨ (¬ p3873)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (p2462) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p3690) ∨ (¬ p3873) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial17139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory6411 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule17139 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2462) (meaning t m 2839) (meaning t m 3588) (meaning t m 3690) (meaning t m 3873) (meaning t m 4169) source

theorem rule17141 (p2010 p2027 p2437 p3574 p3818 p4053 p5514 : Prop) (h : p2027 ∨ p3818 ∨ (¬ p4053) ∨ (¬ p2010) ∨ (¬ p3574) ∨ (¬ p2437) ∨ (¬ p5514)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p3574) ∨ (p3818) ∨ (¬ p4053) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial17141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory6413 t (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule17141 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 3574) (meaning t m 3818) (meaning t m 4053) (meaning t m 5514) source

theorem rule17142 (p1994 p2027 p2764 p3551 p3692 p3742 p4042 p4279 p4444 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p3551) ∨ (¬ p4042) ∨ (¬ p1994) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p3692) ∨ (¬ p4444)) : (¬ p1994) ∨ (p2027) ∨ (p2764) ∨ (¬ p3551) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p4042) ∨ (¬ p4279) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6414 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17142 (meaning t m 1994) (meaning t m 2027) (meaning t m 2764) (meaning t m 3551) (meaning t m 3692) (meaning t m 3742) (meaning t m 4042) (meaning t m 4279) (meaning t m 4444) source

theorem rule17143 (p1988 p2027 p2598 p2622 p3276 p3333 p3365 : Prop) (h : p2027 ∨ (¬ p1988) ∨ (¬ p3365) ∨ (¬ p2598) ∨ p2622 ∨ (¬ p3276) ∨ (¬ p3333)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial17143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory6415 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 9) (m.theta 9 10)
  exact rule17143 (meaning t m 1988) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 3276) (meaning t m 3333) (meaning t m 3365) source

theorem rule17144 (p1984 p2027 p2766 p3266 p3555 p4322 p4363 : Prop) (h : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4363) ∨ (¬ p3555)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3555) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial17144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory6416 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17144 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3555) (meaning t m 4322) (meaning t m 4363) source

theorem rule17145 (p2022 p2027 p2299 p2766 p3791 p4348 p4372 : Prop) (h : (¬ p3791) ∨ (¬ p4348) ∨ (¬ p2299) ∨ p2766 ∨ (¬ p2022) ∨ (¬ p4372) ∨ p2027) : (¬ p2022) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p3791) ∨ (¬ p4348) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial17145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory6417 t (m.theta 0 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule17145 (meaning t m 2022) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 3791) (meaning t m 4348) (meaning t m 4372) source

theorem rule17146 (p2143 p3645 p4243 : Prop) (h : (¬ p3645) ∨ p2143 ∨ (¬ p4243)) : (p2143) ∨ (¬ p3645) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial17146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2143) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory6418 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule17146 (meaning t m 2143) (meaning t m 3645) (meaning t m 4243) source

theorem rule17147 (p4024 p4435 p5539 p5540 : Prop) (h : (¬ p4435) ∨ (¬ p4024) ∨ (¬ p5539) ∨ (¬ p5540)) : (¬ p4024) ∨ (¬ p4435) ∨ (¬ p5539) ∨ (¬ p5540) := by
  classical
  tauto

theorem initial17147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5539)) ∨ (¬ (meaning t m 5540)) := by
  have source := ElevenTheory.theory6419 (m.theta 1 6) (m.theta 2 10) (m.theta 2 6) (m.theta 6 10)
  exact rule17147 (meaning t m 4024) (meaning t m 4435) (meaning t m 5539) (meaning t m 5540) source

theorem rule17148 (p1988 p2027 p2622 p2743 p2779 p2829 p3461 p3654 : Prop) (h : p2027 ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p1988) ∨ (¬ p2779) ∨ p2622 ∨ (¬ p3654) ∨ (¬ p2743)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3654) := by
  classical
  tauto

theorem initial17148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) := by
  have source := ElevenTheory.theory6420 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 9) (m.theta 9 10)
  exact rule17148 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 2779) (meaning t m 2829) (meaning t m 3461) (meaning t m 3654) source

theorem rule17149 (p1992 p2027 p2608 p2764 p3555 p4322 p4363 : Prop) (h : (¬ p2608) ∨ (¬ p1992) ∨ (¬ p3555) ∨ (¬ p4322) ∨ p2764 ∨ p2027 ∨ (¬ p4363)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3555) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial17149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory6421 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 9) (m.theta 9 10)
  exact rule17149 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2764) (meaning t m 3555) (meaning t m 4322) (meaning t m 4363) source

theorem rule17152 (p1996 p2027 p2765 p2891 p3246 p3947 p4173 : Prop) (h : (¬ p3947) ∨ (¬ p3246) ∨ p2027 ∨ p2765 ∨ (¬ p1996) ∨ (¬ p4173) ∨ (¬ p2891)) : (¬ p1996) ∨ (p2027) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory6424 t (m.theta 1 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule17152 (meaning t m 1996) (meaning t m 2027) (meaning t m 2765) (meaning t m 2891) (meaning t m 3246) (meaning t m 3947) (meaning t m 4173) source

theorem rule17154 (p1982 p2027 p2470 p2528 p2579 p2842 p3422 : Prop) (h : (¬ p3422) ∨ p2842 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2579)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (p2842) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial17154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory6426 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule17154 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2579) (meaning t m 2842) (meaning t m 3422) source

theorem rule17155 (p1983 p2027 p2323 p2396 p2807 p3032 p4075 p4260 : Prop) (h : (¬ p4260) ∨ p2323 ∨ (¬ p1983) ∨ (¬ p2396) ∨ (¬ p3032) ∨ p2027 ∨ (¬ p4075) ∨ (¬ p2807)) : (¬ p1983) ∨ (p2027) ∨ (p2323) ∨ (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p4075) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial17155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory6427 t (m.theta 0 3) (m.theta 1 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule17155 (meaning t m 1983) (meaning t m 2027) (meaning t m 2323) (meaning t m 2396) (meaning t m 2807) (meaning t m 3032) (meaning t m 4075) (meaning t m 4260) source

theorem rule17158 (p1998 p2027 p2177 p2409 p2922 p3868 p4260 : Prop) (h : p2409 ∨ (¬ p3868) ∨ (¬ p1998) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2409) ∨ (¬ p2922) ∨ (¬ p3868) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial17158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory6430 t (m.theta 1 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule17158 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2409) (meaning t m 2922) (meaning t m 3868) (meaning t m 4260) source

theorem rule17163 (p2005 p2027 p2148 p2264 p2995 p3212 p3581 p3644 p4208 : Prop) (h : (¬ p3212) ∨ p2027 ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p2005) ∨ (¬ p2264) ∨ (¬ p2995) ∨ p2148 ∨ (¬ p4208)) : (¬ p2005) ∨ (p2027) ∨ (p2148) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3212) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial17163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory6435 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8)
  exact rule17163 (meaning t m 2005) (meaning t m 2027) (meaning t m 2148) (meaning t m 2264) (meaning t m 2995) (meaning t m 3212) (meaning t m 3581) (meaning t m 3644) (meaning t m 4208) source

theorem rule17167 (p1979 p2027 p2233 p2482 p3136 p3877 p3998 p5600 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p5600) ∨ (¬ p3998) ∨ (¬ p2482) ∨ (¬ p3136) ∨ (¬ p1979) ∨ (¬ p3877)) : (¬ p1979) ∨ (p2027) ∨ (p2233) ∨ (¬ p2482) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p3998) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial17167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory6439 t (m.theta 0 4) (m.theta 0 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 10)
  exact rule17167 (meaning t m 1979) (meaning t m 2027) (meaning t m 2233) (meaning t m 2482) (meaning t m 3136) (meaning t m 3877) (meaning t m 3998) (meaning t m 5600) source

theorem rule17170 (p1989 p2027 p2210 p2299 p2633 p3097 p3591 p3957 : Prop) (h : (¬ p1989) ∨ (¬ p2299) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p2210) ∨ p2633) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3591) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial17170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory6442 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17170 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2299) (meaning t m 2633) (meaning t m 3097) (meaning t m 3591) (meaning t m 3957) source

theorem rule17172 (p1997 p2027 p2191 p2192 p3982 p4110 p4506 p5580 : Prop) (h : (¬ p1997) ∨ (¬ p4506) ∨ (¬ p2192) ∨ (¬ p2191) ∨ p3982 ∨ p2027 ∨ (¬ p5580) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (p3982) ∨ (¬ p4110) ∨ (¬ p4506) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial17172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory6444 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10)
  exact rule17172 (meaning t m 1997) (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 3982) (meaning t m 4110) (meaning t m 4506) (meaning t m 5580) source

theorem rule17173 (p2010 p2027 p2210 p2246 p2264 p2651 p2766 p3580 p3591 p3644 p3957 p3989 p4347 p4959 : Prop) (h : p2766 ∨ (¬ p3989) ∨ (¬ p3580) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3644) ∨ (¬ p2264) ∨ (¬ p2010) ∨ (¬ p4347) ∨ (¬ p3957) ∨ (¬ p4959) ∨ (¬ p3591) ∨ (¬ p2210)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p3580) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p3957) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial17173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory6445 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17173 (meaning t m 2010) (meaning t m 2027) (meaning t m 2210) (meaning t m 2246) (meaning t m 2264) (meaning t m 2651) (meaning t m 2766) (meaning t m 3580) (meaning t m 3591) (meaning t m 3644) (meaning t m 3957) (meaning t m 3989) (meaning t m 4347) (meaning t m 4959) source

theorem rule17176 (p2003 p2027 p2299 p2633 p3319 p3549 p3946 : Prop) (h : (¬ p3319) ∨ (¬ p2003) ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3549) ∨ p2027 ∨ (¬ p3946)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial17176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory6448 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule17176 (meaning t m 2003) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3319) (meaning t m 3549) (meaning t m 3946) source

theorem rule17177 (p1997 p2027 p2230 p2938 p3540 p4129 p5503 : Prop) (h : p2938 ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4129) ∨ (¬ p5503) ∨ (¬ p2230) ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (p2938) ∨ (¬ p3540) ∨ (¬ p4129) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial17177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory6449 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10)
  exact rule17177 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2938) (meaning t m 3540) (meaning t m 4129) (meaning t m 5503) source

theorem rule17178 (p1984 p2027 p2138 p2839 p3588 p3873 p3944 p4169 p5660 : Prop) (h : (¬ p4169) ∨ (¬ p1984) ∨ (¬ p3588) ∨ p3944 ∨ (¬ p5660) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3873)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (p3944) ∨ (¬ p4169) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial17178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (meaning t m 3944) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory6450 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 10)
  exact rule17178 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2839) (meaning t m 3588) (meaning t m 3873) (meaning t m 3944) (meaning t m 4169) (meaning t m 5660) source

theorem rule17181 (p1984 p2027 p2191 p2619 p2938 p3555 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p1984) ∨ (¬ p3555) ∨ p2938 ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2191)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (p2938) ∨ (¬ p3555) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial17181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6453 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule17181 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2619) (meaning t m 2938) (meaning t m 3555) (meaning t m 4244) source

theorem rule17185 (p1992 p2027 p2191 p2608 p2619 p3474 p3555 : Prop) (h : (¬ p2619) ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p2191) ∨ p3474) : (¬ p1992) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (p3474) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial17185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory6457 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule17185 (meaning t m 1992) (meaning t m 2027) (meaning t m 2191) (meaning t m 2608) (meaning t m 2619) (meaning t m 3474) (meaning t m 3555) source

theorem rule17188 (p1977 p2027 p2766 p3661 p3662 p3692 p3969 p5600 : Prop) (h : (¬ p1977) ∨ (¬ p3969) ∨ p2766 ∨ (¬ p3692) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p3661) ∨ (¬ p5600)) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p3661) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial17188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory6460 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17188 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 3661) (meaning t m 3662) (meaning t m 3692) (meaning t m 3969) (meaning t m 5600) source

theorem rule17189 (p1992 p2027 p2741 p2764 p2957 p3662 p3692 p4120 p4444 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p2741) ∨ (¬ p1992) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p2957) ∨ (¬ p4444) ∨ p2764) : (¬ p1992) ∨ (p2027) ∨ (¬ p2741) ∨ (p2764) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6461 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17189 (meaning t m 1992) (meaning t m 2027) (meaning t m 2741) (meaning t m 2764) (meaning t m 2957) (meaning t m 3662) (meaning t m 3692) (meaning t m 4120) (meaning t m 4444) source

theorem rule17191 (p1975 p2027 p2122 p2699 p3063 p3093 p4358 : Prop) (h : (¬ p3093) ∨ p2699 ∨ (¬ p2122) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p4358)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial17191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory6463 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17191 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 4358) source

theorem rule17193 (p1987 p2027 p2579 p2588 p2737 p2997 p3363 p3585 : Prop) (h : (¬ p3363) ∨ (¬ p2579) ∨ (¬ p3585) ∨ (¬ p2737) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p1987) ∨ p2997) : (¬ p1987) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2737) ∨ (p2997) ∨ (¬ p3363) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6465 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule17193 (meaning t m 1987) (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2737) (meaning t m 2997) (meaning t m 3363) (meaning t m 3585) source

theorem rule17194 (p1982 p2027 p2114 p2518 p2528 p3379 p3954 : Prop) (h : (¬ p1982) ∨ p2114 ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p2528) ∨ (¬ p2518)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6466 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule17194 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 3954) source

theorem rule17196 (p1987 p2027 p2657 p3008 p3286 p3574 p4035 : Prop) (h : (¬ p2657) ∨ p3008 ∨ (¬ p3286) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p4035)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2657) ∨ (p3008) ∨ (¬ p3286) ∨ (¬ p3574) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial17196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory6468 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6)
  exact rule17196 (meaning t m 1987) (meaning t m 2027) (meaning t m 2657) (meaning t m 3008) (meaning t m 3286) (meaning t m 3574) (meaning t m 4035) source

theorem rule17197 (p1976 p2027 p2476 p2588 p2997 p3584 p3641 p3905 : Prop) (h : (¬ p1976) ∨ (¬ p3905) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3584) ∨ (¬ p3641)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial17197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory6469 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule17197 (meaning t m 1976) (meaning t m 2027) (meaning t m 2476) (meaning t m 2588) (meaning t m 2997) (meaning t m 3584) (meaning t m 3641) (meaning t m 3905) source

theorem rule17200 (p1977 p2027 p2622 p2797 p2807 p2963 p2996 : Prop) (h : (¬ p2807) ∨ (¬ p2963) ∨ p2622 ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2996) ∨ (¬ p2797)) : (¬ p1977) ∨ (p2027) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial17200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory6472 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule17200 (meaning t m 1977) (meaning t m 2027) (meaning t m 2622) (meaning t m 2797) (meaning t m 2807) (meaning t m 2963) (meaning t m 2996) source

theorem rule17201 (p1992 p2027 p2169 p2743 p2952 p3361 p3952 p3989 : Prop) (h : (¬ p2743) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p1992) ∨ p2169 ∨ (¬ p2952) ∨ (¬ p3361)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6473 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule17201 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2743) (meaning t m 2952) (meaning t m 3361) (meaning t m 3952) (meaning t m 3989) source

theorem rule17204 (p1982 p2027 p2459 p2622 p2685 p4009 p4044 p5558 : Prop) (h : (¬ p1982) ∨ (¬ p4044) ∨ p2622 ∨ (¬ p2459) ∨ (¬ p5558) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p4009)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2685) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial17204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory6476 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17204 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2622) (meaning t m 2685) (meaning t m 4009) (meaning t m 4044) (meaning t m 5558) source

theorem rule17205 (p1987 p2027 p2964 p3276 p4208 p4315 p4322 : Prop) (h : (¬ p1987) ∨ (¬ p4315) ∨ p2964 ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4322)) : (¬ p1987) ∨ (p2027) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial17205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory6477 t (m.theta 2 3) (m.theta 3 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule17205 (meaning t m 1987) (meaning t m 2027) (meaning t m 2964) (meaning t m 3276) (meaning t m 4208) (meaning t m 4315) (meaning t m 4322) source

theorem rule17208 (p1987 p2027 p2191 p2764 p3364 p3684 p3692 p4210 p4444 : Prop) (h : (¬ p3692) ∨ (¬ p1987) ∨ (¬ p2191) ∨ p2764 ∨ (¬ p4210) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3364) ∨ (¬ p3684)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2191) ∨ (p2764) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p3692) ∨ (¬ p4210) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6480 t (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17208 (meaning t m 1987) (meaning t m 2027) (meaning t m 2191) (meaning t m 2764) (meaning t m 3364) (meaning t m 3684) (meaning t m 3692) (meaning t m 4210) (meaning t m 4444) source

theorem rule17211 (p1992 p2027 p2608 p2764 p3860 p4261 p4444 : Prop) (h : (¬ p1992) ∨ p2764 ∨ (¬ p4444) ∨ (¬ p3860) ∨ (¬ p2608) ∨ (¬ p4261) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6483 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17211 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2764) (meaning t m 3860) (meaning t m 4261) (meaning t m 4444) source

theorem rule17213 (p1998 p2027 p2177 p2409 p2493 p2579 p3389 p4710 : Prop) (h : (¬ p1998) ∨ (¬ p2177) ∨ (¬ p4710) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2579) ∨ p2409 ∨ (¬ p3389)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial17213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory6485 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17213 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2409) (meaning t m 2493) (meaning t m 2579) (meaning t m 3389) (meaning t m 4710) source

theorem rule17214 (p2007 p2027 p2088 p2409 p2482 p2493 p2534 p2579 : Prop) (h : p2027 ∨ (¬ p2534) ∨ (¬ p2007) ∨ (¬ p2493) ∨ (¬ p2482) ∨ (¬ p2088) ∨ p2409 ∨ (¬ p2579)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2088) ∨ (p2409) ∨ (¬ p2482) ∨ (¬ p2493) ∨ (¬ p2534) ∨ (¬ p2579) := by
  classical
  tauto

theorem initial17214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) := by
  have source := ElevenTheory.theory6486 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule17214 (meaning t m 2007) (meaning t m 2027) (meaning t m 2088) (meaning t m 2409) (meaning t m 2482) (meaning t m 2493) (meaning t m 2534) (meaning t m 2579) source

theorem rule17215 (p4040 p4322 p5284 : Prop) (h : (¬ p4040) ∨ (¬ p4322) ∨ p5284) : (¬ p4040) ∨ (¬ p4322) ∨ (p5284) := by
  classical
  tauto

theorem initial17215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4322)) ∨ (meaning t m 5284) := by
  have source := ElevenTheory.theory6487 (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule17215 (meaning t m 4040) (meaning t m 4322) (meaning t m 5284) source

theorem rule17216 (p1976 p2027 p2138 p2287 p2743 p2839 p4195 : Prop) (h : (¬ p2138) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p1976) ∨ (¬ p4195) ∨ p2287) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2287) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial17216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory6488 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule17216 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2287) (meaning t m 2743) (meaning t m 2839) (meaning t m 4195) source

end SunPrize.SMT
