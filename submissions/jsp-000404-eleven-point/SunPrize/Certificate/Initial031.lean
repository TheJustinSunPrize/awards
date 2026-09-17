import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory015
import SunPrize.Certificate.Theory016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule14898 (p1975 p2027 p2169 p2274 p2387 p3654 p3744 : Prop) (h : p2169 ∨ (¬ p2387) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p3744)) : (¬ p1975) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial14898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory4330 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule14898 (meaning t m 1975) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2387) (meaning t m 3654) (meaning t m 3744) source

theorem rule14906 (p1977 p2027 p2764 p2996 p3553 p4348 p4444 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p2996) ∨ (¬ p1977) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4444)) : (¬ p1977) ∨ (p2027) ∨ (p2764) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4338 t (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14906 (meaning t m 1977) (meaning t m 2027) (meaning t m 2764) (meaning t m 2996) (meaning t m 3553) (meaning t m 4348) (meaning t m 4444) source

theorem rule14908 (p1977 p2027 p2662 p2766 p3540 p3644 p4111 p4348 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p2662) ∨ (¬ p4111) ∨ (¬ p3644) ∨ (¬ p1977) ∨ (¬ p4348) ∨ (¬ p3540)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4340 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14908 (meaning t m 1977) (meaning t m 2027) (meaning t m 2662) (meaning t m 2766) (meaning t m 3540) (meaning t m 3644) (meaning t m 4111) (meaning t m 4348) source

theorem rule14910 (p1977 p2027 p2169 p2651 p2963 p3324 p4111 : Prop) (h : (¬ p3324) ∨ (¬ p2963) ∨ (¬ p1977) ∨ (¬ p2651) ∨ (¬ p4111) ∨ p2027 ∨ p2169) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4342 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule14910 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2651) (meaning t m 2963) (meaning t m 3324) (meaning t m 4111) source

theorem rule14912 (p1977 p2027 p2476 p2534 p2662 p3146 p3578 p4111 : Prop) (h : (¬ p1977) ∨ p3578 ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p4111)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4344 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule14912 (meaning t m 1977) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2662) (meaning t m 3146) (meaning t m 3578) (meaning t m 4111) source

theorem rule14913 (p1996 p2027 p2114 p2685 p2696 p3055 p3367 : Prop) (h : (¬ p3055) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3367) ∨ p2114 ∨ (¬ p1996) ∨ (¬ p2685)) : (¬ p1996) ∨ (p2027) ∨ (p2114) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial14913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory4345 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule14913 (meaning t m 1996) (meaning t m 2027) (meaning t m 2114) (meaning t m 2685) (meaning t m 2696) (meaning t m 3055) (meaning t m 3367) source

theorem rule14917 (p1988 p2027 p2363 p2699 p3063 p3093 p3266 : Prop) (h : p2699 ∨ (¬ p2363) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3266) ∨ (¬ p3063)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2363) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial14917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory4349 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14917 (meaning t m 1988) (meaning t m 2027) (meaning t m 2363) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 3266) source

theorem rule14919 (p2001 p2027 p2166 p2355 p2449 p3486 p3690 : Prop) (h : (¬ p2449) ∨ (¬ p3486) ∨ p2027 ∨ p2355 ∨ (¬ p3690) ∨ (¬ p2001) ∨ (¬ p2166)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2166) ∨ (p2355) ∨ (¬ p2449) ∨ (¬ p3486) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial14919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory4351 t (m.theta 1 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule14919 (meaning t m 2001) (meaning t m 2027) (meaning t m 2166) (meaning t m 2355) (meaning t m 2449) (meaning t m 3486) (meaning t m 3690) source

theorem rule14921 (p1989 p2027 p2156 p2388 p2901 p3556 p4173 : Prop) (h : p2027 ∨ (¬ p1989) ∨ (¬ p2156) ∨ p2388 ∨ (¬ p3556) ∨ (¬ p2901) ∨ (¬ p4173)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2156) ∨ (p2388) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial14921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory4353 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14921 (meaning t m 1989) (meaning t m 2027) (meaning t m 2156) (meaning t m 2388) (meaning t m 2901) (meaning t m 3556) (meaning t m 4173) source

theorem rule14922 (p1976 p2027 p2766 p3055 p3684 p3692 p3880 : Prop) (h : (¬ p1976) ∨ (¬ p3055) ∨ (¬ p3684) ∨ p2766 ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3880)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial14922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4354 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule14922 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3055) (meaning t m 3684) (meaning t m 3692) (meaning t m 3880) source

theorem rule14925 (p1977 p2027 p2765 p2881 p3644 p3742 p3872 p4111 : Prop) (h : p2765 ∨ (¬ p4111) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3872) ∨ (¬ p2881) ∨ (¬ p3644)) : (¬ p1977) ∨ (p2027) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3872) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4357 t (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule14925 (meaning t m 1977) (meaning t m 2027) (meaning t m 2765) (meaning t m 2881) (meaning t m 3644) (meaning t m 3742) (meaning t m 3872) (meaning t m 4111) source

theorem rule14926 (p1987 p2027 p2651 p2810 p2911 p2914 p3172 p4548 : Prop) (h : (¬ p2911) ∨ (¬ p2810) ∨ (¬ p2651) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3172) ∨ p2914 ∨ (¬ p4548)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3172) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial14926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory4358 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule14926 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2810) (meaning t m 2911) (meaning t m 2914) (meaning t m 3172) (meaning t m 4548) source

theorem rule14927 (p1977 p2027 p2651 p2963 p2997 p3568 p4111 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p2963) ∨ (¬ p3568) ∨ p2997) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4359 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule14927 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2963) (meaning t m 2997) (meaning t m 3568) (meaning t m 4111) source

theorem rule14928 (p2156 p3370 p3957 p4512 : Prop) (h : (¬ p3370) ∨ (¬ p2156) ∨ (¬ p4512) ∨ (¬ p3957)) : (¬ p2156) ∨ (¬ p3370) ∨ (¬ p3957) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial14928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory4360 (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6)
  exact rule14928 (meaning t m 2156) (meaning t m 3370) (meaning t m 3957) (meaning t m 4512) source

theorem rule14931 (p1999 p2027 p2765 p2972 p3680 p4034 p4110 p4191 : Prop) (h : (¬ p4110) ∨ (¬ p1999) ∨ (¬ p2972) ∨ p2765 ∨ (¬ p4191) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p4034)) : (¬ p1999) ∨ (p2027) ∨ (p2765) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4034) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4363 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule14931 (meaning t m 1999) (meaning t m 2027) (meaning t m 2765) (meaning t m 2972) (meaning t m 3680) (meaning t m 4034) (meaning t m 4110) (meaning t m 4191) source

theorem rule14932 (p1977 p2027 p2651 p2764 p3292 p4111 p4425 p5171 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p4425) ∨ (¬ p5171) ∨ p2764 ∨ (¬ p3292)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p3292) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial14932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory4364 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule14932 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 3292) (meaning t m 4111) (meaning t m 4425) (meaning t m 5171) source

theorem rule14934 (p1977 p2027 p2662 p3043 p3346 p3680 p4111 p4425 : Prop) (h : (¬ p3346) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p4425) ∨ (¬ p2662) ∨ (¬ p3680) ∨ p3043) : (¬ p1977) ∨ (p2027) ∨ (¬ p2662) ∨ (p3043) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4111) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial14934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4366 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule14934 (meaning t m 1977) (meaning t m 2027) (meaning t m 2662) (meaning t m 3043) (meaning t m 3346) (meaning t m 3680) (meaning t m 4111) (meaning t m 4425) source

theorem rule14935 (p1981 p2027 p2287 p2963 p3166 p3256 p4347 : Prop) (h : (¬ p3256) ∨ (¬ p1981) ∨ (¬ p3166) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2963) ∨ p2287) : (¬ p1981) ∨ (p2027) ∨ (p2287) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4367 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14935 (meaning t m 1981) (meaning t m 2027) (meaning t m 2287) (meaning t m 2963) (meaning t m 3166) (meaning t m 3256) (meaning t m 4347) source

theorem rule14936 (p2006 p2027 p2287 p2946 p3156 p3414 p3694 p4156 : Prop) (h : p2027 ∨ (¬ p3694) ∨ (¬ p3414) ∨ (¬ p2006) ∨ (¬ p4156) ∨ (¬ p3156) ∨ (¬ p2946) ∨ p2287) : (¬ p2006) ∨ (p2027) ∨ (p2287) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3414) ∨ (¬ p3694) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial14936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory4368 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7) (m.theta 5 8)
  exact rule14936 (meaning t m 2006) (meaning t m 2027) (meaning t m 2287) (meaning t m 2946) (meaning t m 3156) (meaning t m 3414) (meaning t m 3694) (meaning t m 4156) source

theorem rule14937 (p1986 p2611 p2774 p5221 : Prop) (h : p2611 ∨ (¬ p2774) ∨ p5221 ∨ (¬ p1986)) : (¬ p1986) ∨ (p2611) ∨ (¬ p2774) ∨ (p5221) := by
  classical
  tauto

theorem initial14937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 5221) := by
  have source := ElevenTheory.theory4369 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule14937 (meaning t m 1986) (meaning t m 2611) (meaning t m 2774) (meaning t m 5221) source

theorem rule14942 (p1983 p2027 p2132 p2699 p2707 p3246 p3583 p3589 p4344 : Prop) (h : (¬ p3246) ∨ p2699 ∨ (¬ p2132) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p4344) ∨ (¬ p3583) ∨ (¬ p2707)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2132) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3246) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial14942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory4374 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14942 (meaning t m 1983) (meaning t m 2027) (meaning t m 2132) (meaning t m 2699) (meaning t m 2707) (meaning t m 3246) (meaning t m 3583) (meaning t m 3589) (meaning t m 4344) source

theorem rule14944 (p1987 p2027 p2766 p2810 p3266 p3359 p4425 : Prop) (h : (¬ p1987) ∨ (¬ p3266) ∨ (¬ p2810) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p4425) ∨ p2766) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial14944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4376 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14944 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 2810) (meaning t m 3266) (meaning t m 3359) (meaning t m 4425) source

theorem rule14945 (p1977 p2027 p2476 p2534 p2662 p2764 p4111 p4444 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p1977) ∨ (¬ p2534) ∨ (¬ p2476) ∨ (¬ p4444)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p4111) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4377 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14945 (meaning t m 1977) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2662) (meaning t m 2764) (meaning t m 4111) (meaning t m 4444) source

theorem rule14946 (p1995 p2027 p2476 p2534 p2766 p2928 p3389 : Prop) (h : (¬ p2476) ∨ (¬ p2928) ∨ (¬ p1995) ∨ (¬ p2534) ∨ p2027 ∨ p2766 ∨ (¬ p3389)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p2928) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial14946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory4378 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule14946 (meaning t m 1995) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2766) (meaning t m 2928) (meaning t m 3389) source

theorem rule14947 (p1995 p2027 p2474 p2528 p2928 p3389 p3498 p3857 : Prop) (h : p3498 ∨ (¬ p1995) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2528) ∨ (¬ p3389) ∨ (¬ p2474) ∨ (¬ p2928)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (p3498) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial14947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory4379 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule14947 (meaning t m 1995) (meaning t m 2027) (meaning t m 2474) (meaning t m 2528) (meaning t m 2928) (meaning t m 3389) (meaning t m 3498) (meaning t m 3857) source

theorem rule14948 (p1988 p2027 p2148 p2156 p3105 p3680 p3758 : Prop) (h : (¬ p3680) ∨ (¬ p3758) ∨ (¬ p1988) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p3105)) : (¬ p1988) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial14948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory4380 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule14948 (meaning t m 1988) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 3105) (meaning t m 3680) (meaning t m 3758) source

theorem rule14953 (p1977 p2027 p2662 p2764 p3540 p4111 p4278 p4381 : Prop) (h : (¬ p1977) ∨ (¬ p2662) ∨ (¬ p3540) ∨ p2764 ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4111) ∨ (¬ p4381)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial14953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4385 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14953 (meaning t m 1977) (meaning t m 2027) (meaning t m 2662) (meaning t m 2764) (meaning t m 3540) (meaning t m 4111) (meaning t m 4278) (meaning t m 4381) source

theorem rule14956 (p1977 p2027 p2474 p2662 p2964 p3276 p3857 p4111 p4444 : Prop) (h : p2964 ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2662) ∨ (¬ p4444) ∨ (¬ p2474) ∨ (¬ p4111) ∨ (¬ p3276)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2474) ∨ (¬ p2662) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p3857) ∨ (¬ p4111) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4388 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14956 (meaning t m 1977) (meaning t m 2027) (meaning t m 2474) (meaning t m 2662) (meaning t m 2964) (meaning t m 3276) (meaning t m 3857) (meaning t m 4111) (meaning t m 4444) source

theorem rule14958 (p1975 p2027 p2156 p2274 p2619 p3474 p4120 : Prop) (h : p3474 ∨ (¬ p1975) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2156) ∨ (¬ p4120)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2619) ∨ (p3474) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial14958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory4390 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule14958 (meaning t m 1975) (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2619) (meaning t m 3474) (meaning t m 4120) source

theorem rule14959 (p1977 p2027 p2462 p2662 p2911 p3551 p4111 p4278 p5197 : Prop) (h : (¬ p4111) ∨ (¬ p3551) ∨ (¬ p5197) ∨ p2462 ∨ (¬ p1977) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4278)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2662) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial14959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory4391 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14959 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2662) (meaning t m 2911) (meaning t m 3551) (meaning t m 4111) (meaning t m 4278) (meaning t m 5197) source

theorem rule14960 (p1988 p2027 p2132 p2611 p2860 p3125 p3461 : Prop) (h : (¬ p2132) ∨ (¬ p1988) ∨ (¬ p3125) ∨ p2611 ∨ (¬ p2860) ∨ p2027 ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial14960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory4392 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14960 (meaning t m 1988) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2860) (meaning t m 3125) (meaning t m 3461) source

theorem rule14961 (p3093 p5153 p5486 p5487 : Prop) (h : (¬ p5153) ∨ (¬ p3093) ∨ (¬ p5486) ∨ (¬ p5487)) : (¬ p3093) ∨ (¬ p5153) ∨ (¬ p5486) ∨ (¬ p5487) := by
  classical
  tauto

theorem initial14961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 5153)) ∨ (¬ (meaning t m 5486)) ∨ (¬ (meaning t m 5487)) := by
  have source := ElevenTheory.theory4393 (m.theta 0 1) (m.theta 0 9) (m.theta 1 6) (m.theta 1 9)
  exact rule14961 (meaning t m 3093) (meaning t m 5153) (meaning t m 5486) (meaning t m 5487) source

theorem rule14962 (p1981 p2027 p2166 p2210 p2699 p3146 p4347 : Prop) (h : (¬ p1981) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p4347) ∨ p2699 ∨ (¬ p3146)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3146) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4394 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14962 (meaning t m 1981) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 3146) (meaning t m 4347) source

theorem rule14964 (p1994 p2202 p3574 p4717 : Prop) (h : (¬ p3574) ∨ p2202 ∨ p4717 ∨ (¬ p1994)) : (¬ p1994) ∨ (p2202) ∨ (¬ p3574) ∨ (p4717) := by
  classical
  tauto

theorem initial14964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 4717) := by
  have source := ElevenTheory.theory4396 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule14964 (meaning t m 1994) (meaning t m 2202) (meaning t m 3574) (meaning t m 4717) source

theorem rule14970 (p1977 p2027 p2387 p2459 p2633 p2667 p4154 p4347 : Prop) (h : (¬ p4154) ∨ (¬ p1977) ∨ (¬ p2667) ∨ p2027 ∨ p2633 ∨ (¬ p4347) ∨ (¬ p2459) ∨ (¬ p2387)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4402 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14970 (meaning t m 1977) (meaning t m 2027) (meaning t m 2387) (meaning t m 2459) (meaning t m 2633) (meaning t m 2667) (meaning t m 4154) (meaning t m 4347) source

theorem rule14971 (p1977 p2027 p2459 p2476 p2534 p2633 p2662 p4111 : Prop) (h : (¬ p1977) ∨ (¬ p4111) ∨ p2633 ∨ (¬ p2476) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2534) ∨ (¬ p2459)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4403 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14971 (meaning t m 1977) (meaning t m 2027) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2633) (meaning t m 2662) (meaning t m 4111) source

theorem rule14972 (p1977 p2027 p2462 p2667 p2761 p3946 p4154 p4191 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p3946) ∨ (¬ p1977) ∨ (¬ p2761) ∨ (¬ p4191) ∨ (¬ p4154) ∨ (¬ p2667)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2667) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4404 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule14972 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2667) (meaning t m 2761) (meaning t m 3946) (meaning t m 4154) (meaning t m 4191) source

theorem rule14974 (p1983 p2027 p2323 p2449 p2651 p3027 p4111 : Prop) (h : (¬ p1983) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4111) ∨ p2323 ∨ (¬ p2651) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4406 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule14974 (meaning t m 1983) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2651) (meaning t m 3027) (meaning t m 4111) source

theorem rule14975 (p2002 p2027 p2177 p2829 p2997 p3551 p3588 p3959 : Prop) (h : (¬ p2002) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p3959) ∨ (¬ p3588) ∨ (¬ p2177) ∨ p2997 ∨ (¬ p3551)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2829) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial14975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory4407 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule14975 (meaning t m 2002) (meaning t m 2027) (meaning t m 2177) (meaning t m 2829) (meaning t m 2997) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) source

theorem rule14978 (p1990 p2027 p2331 p2388 p2952 p3097 p3309 p4319 : Prop) (h : (¬ p3097) ∨ (¬ p1990) ∨ p2388 ∨ p2027 ∨ (¬ p4319) ∨ (¬ p3309) ∨ (¬ p2952) ∨ (¬ p2331)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial14978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory4410 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule14978 (meaning t m 1990) (meaning t m 2027) (meaning t m 2331) (meaning t m 2388) (meaning t m 2952) (meaning t m 3097) (meaning t m 3309) (meaning t m 4319) source

theorem rule14981 (p1975 p2027 p2274 p2383 p2388 p2952 p3987 p3989 : Prop) (h : (¬ p2952) ∨ (¬ p3987) ∨ (¬ p2383) ∨ (¬ p3989) ∨ (¬ p2274) ∨ p2388 ∨ (¬ p1975) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial14981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory4413 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14981 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2383) (meaning t m 2388) (meaning t m 2952) (meaning t m 3987) (meaning t m 3989) source

theorem rule14982 (p1996 p2027 p2331 p2388 p2952 p3027 p4154 : Prop) (h : p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p1996) ∨ (¬ p4154) ∨ p2388 ∨ (¬ p3027)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial14982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4414 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7)
  exact rule14982 (meaning t m 1996) (meaning t m 2027) (meaning t m 2331) (meaning t m 2388) (meaning t m 2952) (meaning t m 3027) (meaning t m 4154) source

theorem rule14983 (p1977 p2027 p2633 p2996 p3246 p3570 p3821 p4155 : Prop) (h : (¬ p1977) ∨ p2633 ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4155) ∨ (¬ p3570) ∨ (¬ p2996) ∨ (¬ p3821)) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial14983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory4415 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14983 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2996) (meaning t m 3246) (meaning t m 3570) (meaning t m 3821) (meaning t m 4155) source

theorem rule14984 (p1977 p2027 p2299 p2633 p2957 p3097 p3646 p3662 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p2957) ∨ (¬ p1977) ∨ (¬ p2299) ∨ (¬ p3662)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial14984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory4416 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule14984 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2957) (meaning t m 3097) (meaning t m 3646) (meaning t m 3662) source

theorem rule14987 (p1977 p2027 p2957 p3556 p3570 p3662 p3982 p5558 : Prop) (h : (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3570) ∨ (¬ p1977) ∨ (¬ p2957) ∨ p3982 ∨ p2027 ∨ (¬ p5558)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial14987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory4419 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule14987 (meaning t m 1977) (meaning t m 2027) (meaning t m 2957) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) (meaning t m 3982) (meaning t m 5558) source

theorem rule14988 (p1982 p2027 p2253 p2363 p2699 p3166 p4009 p5580 : Prop) (h : (¬ p5580) ∨ p2027 ∨ (¬ p1982) ∨ p2699 ∨ (¬ p3166) ∨ (¬ p2363) ∨ (¬ p2253) ∨ (¬ p4009)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2363) ∨ (p2699) ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial14988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory4420 t (m.theta 0 1) (m.theta 0 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule14988 (meaning t m 1982) (meaning t m 2027) (meaning t m 2253) (meaning t m 2363) (meaning t m 2699) (meaning t m 3166) (meaning t m 4009) (meaning t m 5580) source

theorem rule14989 (p1977 p2027 p2766 p2957 p3556 p3570 p3662 p4348 : Prop) (h : (¬ p3556) ∨ (¬ p1977) ∨ (¬ p3662) ∨ (¬ p2957) ∨ (¬ p3570) ∨ p2766 ∨ p2027 ∨ (¬ p4348)) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4421 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14989 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) (meaning t m 4348) source

theorem rule14991 (p1999 p2027 p2633 p2761 p3246 p3570 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p1999) ∨ (¬ p3246) ∨ p2633 ∨ (¬ p2761)) : (¬ p1999) ∨ (p2027) ∨ (p2633) ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4423 t (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule14991 (meaning t m 1999) (meaning t m 2027) (meaning t m 2633) (meaning t m 2761) (meaning t m 3246) (meaning t m 3570) (meaning t m 4191) source

theorem rule14993 (p1975 p2027 p2323 p2331 p2553 p2668 p3956 : Prop) (h : (¬ p2331) ∨ p2323 ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (¬ p3956)) : (¬ p1975) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial14993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4425 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14993 (meaning t m 1975) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2553) (meaning t m 2668) (meaning t m 3956) source

theorem rule14996 (p1977 p2027 p2459 p2633 p2957 p3662 p3692 p4120 : Prop) (h : (¬ p2957) ∨ p2633 ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p1977) ∨ (¬ p4120) ∨ (¬ p2459)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial14996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory4428 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14996 (meaning t m 1977) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2957) (meaning t m 3662) (meaning t m 3692) (meaning t m 4120) source

theorem rule14997 (p1982 p2027 p2190 p2202 p2363 p2563 p3969 p5580 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p5580) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p2363) ∨ (¬ p3969) ∨ (¬ p2190)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2190) ∨ (p2202) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3969) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial14997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory4429 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule14997 (meaning t m 1982) (meaning t m 2027) (meaning t m 2190) (meaning t m 2202) (meaning t m 2363) (meaning t m 2563) (meaning t m 3969) (meaning t m 5580) source

theorem rule14998 (p1988 p2027 p2323 p2651 p3016 p3461 p3564 : Prop) (h : (¬ p3564) ∨ (¬ p3461) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2651) ∨ p2323 ∨ (¬ p3016)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3461) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial14998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory4430 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14998 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2651) (meaning t m 3016) (meaning t m 3461) (meaning t m 3564) source

theorem rule14999 (p1977 p2027 p2633 p2957 p3570 p3662 p4129 p4372 p4984 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p4129) ∨ (¬ p4984) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4372) ∨ p2633 ∨ (¬ p3570)) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2957) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4129) ∨ (¬ p4372) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial14999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4372)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory4431 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule14999 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2957) (meaning t m 3570) (meaning t m 3662) (meaning t m 4129) (meaning t m 4372) (meaning t m 4984) source

theorem rule15000 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p4139) ∨ (((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4139) ∨ (meaning t m 6172) := by
  exact rule15000 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15001 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p5660) ∨ (((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5660) ∨ (meaning t m 6172) := by
  exact rule15001 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15002 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p4141) ∨ (((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4141) ∨ (meaning t m 6172) := by
  exact rule15002 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15003 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p5661) ∨ (((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5661) ∨ (meaning t m 6172) := by
  exact rule15003 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15004 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p5662) ∨ (((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5662) ∨ (meaning t m 6172) := by
  exact rule15004 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15005 (p4139 p4141 p5660 p5661 p5662 : Prop) : (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5660) ∨ (¬ p5661) ∨ (¬ p5662) ∨ (¬ ((¬ p4139) ∨ (¬ p5660) ∨ (¬ p4141) ∨ (¬ p5661) ∨ (¬ p5662))) := by
  classical
  tauto

theorem initial15005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4139)) ∨ (¬ (meaning t m 4141)) ∨ (¬ (meaning t m 5660)) ∨ (¬ (meaning t m 5661)) ∨ (¬ (meaning t m 5662)) ∨ (¬ (meaning t m 6172)) := by
  exact rule15005 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule15008 (p4129 p5664 p5665 p5666 p5667 : Prop) : (p4129) ∨ (((¬ p5664) ∨ (¬ p5665) ∨ (¬ p4129) ∨ (¬ p5666) ∨ (¬ p5667))) := by
  classical
  tauto

theorem initial15008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4129) ∨ (meaning t m 6173) := by
  exact rule15008 (meaning t m 4129) (meaning t m 5664) (meaning t m 5665) (meaning t m 5666) (meaning t m 5667)

theorem rule15014 (p6172 p6173 : Prop) : (¬ ((¬ p6172) ∨ (¬ p6173))) ∨ (¬ p6172) ∨ (¬ p6173) := by
  classical
  tauto

theorem initial15014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6171)) ∨ (¬ (meaning t m 6172)) ∨ (¬ (meaning t m 6173)) := by
  exact rule15014 (meaning t m 6172) (meaning t m 6173)

theorem rule15015 (p5658 p6171 : Prop) (h : (p5658 ↔ p6171)) : (¬ p5658) ∨ (p6171) := by
  classical
  tauto

theorem initial15015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5658)) ∨ (meaning t m 6171) := by
  have source := ElevenTheory.theory4432 t (m.theta 5 10) (m.theta 5 7) (m.theta 7 10)
  exact rule15015 (meaning t m 5658) (meaning t m 6171) source

theorem rule15018 (p1988 p2027 p2608 p2699 p2829 p3461 p3483 : Prop) (h : (¬ p3483) ∨ (¬ p2608) ∨ p2699 ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2829) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3483) := by
  classical
  tauto

theorem initial15018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) := by
  have source := ElevenTheory.theory4434 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15018 (meaning t m 1988) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) (meaning t m 3461) (meaning t m 3483) source

theorem rule15024 (p1997 p2027 p2323 p2641 p2807 p2996 p3986 p4110 : Prop) (h : p2323 ∨ (¬ p2807) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4110) ∨ (¬ p2641) ∨ (¬ p3986)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3986) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4440 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6)
  exact rule15024 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2641) (meaning t m 2807) (meaning t m 2996) (meaning t m 3986) (meaning t m 4110) source

theorem rule15025 (p1977 p2027 p2462 p2881 p2957 p3551 p3662 p3690 p4984 : Prop) (h : (¬ p3551) ∨ (¬ p1977) ∨ (¬ p4984) ∨ (¬ p2881) ∨ p2462 ∨ (¬ p3662) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2957)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial15025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory4441 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15025 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 2957) (meaning t m 3551) (meaning t m 3662) (meaning t m 3690) (meaning t m 4984) source

theorem rule15028 (p1981 p2027 p2699 p3093 p3527 p3941 p4452 p5580 : Prop) (h : (¬ p1981) ∨ (¬ p4452) ∨ (¬ p5580) ∨ (¬ p3941) ∨ (¬ p3527) ∨ (¬ p3093) ∨ p2699 ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4452) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial15028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory4444 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule15028 (meaning t m 1981) (meaning t m 2027) (meaning t m 2699) (meaning t m 3093) (meaning t m 3527) (meaning t m 3941) (meaning t m 4452) (meaning t m 5580) source

theorem rule15029 (p1976 p2027 p2299 p2780 p2881 p2938 p3822 : Prop) (h : (¬ p1976) ∨ (¬ p2881) ∨ (¬ p2780) ∨ p2938 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3822)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial15029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory4445 t (m.theta 0 2) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15029 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2780) (meaning t m 2881) (meaning t m 2938) (meaning t m 3822) source

theorem rule15031 (p1975 p2027 p2253 p2331 p2553 p2699 p3323 p4137 : Prop) (h : p2699 ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p1975) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p4137)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3323) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4447 t (m.theta 0 1) (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15031 (meaning t m 1975) (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 2553) (meaning t m 2699) (meaning t m 3323) (meaning t m 4137) source

theorem rule15032 (p1975 p2027 p2299 p2323 p3527 p3654 p3987 p4026 p4452 : Prop) (h : p2323 ∨ (¬ p3527) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p4026) ∨ (¬ p3654) ∨ (¬ p4452) ∨ (¬ p3987)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2323) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4026) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial15032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory4448 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule15032 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2323) (meaning t m 3527) (meaning t m 3654) (meaning t m 3987) (meaning t m 4026) (meaning t m 4452) source

theorem rule15033 (p1975 p2027 p2299 p2764 p3527 p3817 p4444 p4445 : Prop) (h : p2764 ∨ (¬ p1975) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p2299) ∨ (¬ p3817) ∨ (¬ p4445)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2764) ∨ (¬ p3527) ∨ (¬ p3817) ∨ (¬ p4444) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial15033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory4449 t (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15033 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2764) (meaning t m 3527) (meaning t m 3817) (meaning t m 4444) (meaning t m 4445) source

theorem rule15034 (p2004 p2027 p2881 p2938 p3516 p3551 p3817 : Prop) (h : (¬ p3551) ∨ p2938 ∨ (¬ p2881) ∨ (¬ p2004) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p3516)) : (¬ p2004) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial15034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory4450 t (m.theta 0 7) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15034 (meaning t m 2004) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3516) (meaning t m 3551) (meaning t m 3817) source

theorem rule15037 (p1982 p2027 p2363 p2765 p2881 p3872 p3941 p5580 : Prop) (h : (¬ p3941) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p3872) ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2765 ∨ (¬ p2881)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3941) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial15037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory4453 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15037 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2765) (meaning t m 2881) (meaning t m 3872) (meaning t m 3941) (meaning t m 5580) source

theorem rule15040 (p1975 p2027 p2295 p2964 p3276 p4037 p4191 : Prop) (h : p2964 ∨ p2027 ∨ (¬ p2295) ∨ (¬ p4191) ∨ (¬ p1975) ∨ (¬ p3276) ∨ (¬ p4037)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4456 t (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule15040 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2964) (meaning t m 3276) (meaning t m 4037) (meaning t m 4191) source

theorem rule15044 (p1990 p2027 p2323 p2553 p2651 p3016 p3097 : Prop) (h : (¬ p2553) ∨ p2323 ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p1990) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (p2323) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial15044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory4460 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule15044 (meaning t m 1990) (meaning t m 2027) (meaning t m 2323) (meaning t m 2553) (meaning t m 2651) (meaning t m 3016) (meaning t m 3097) source

theorem rule15046 (p1999 p2027 p2295 p2323 p2331 p2588 p3564 : Prop) (h : p2323 ∨ (¬ p1999) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p2295)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial15046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory4462 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15046 (meaning t m 1999) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2331) (meaning t m 2588) (meaning t m 3564) source

theorem rule15050 (p1975 p2027 p2299 p2699 p2881 p2891 p3379 p3948 : Prop) (h : (¬ p1975) ∨ (¬ p3948) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3379) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3379) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial15050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory4466 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15050 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2699) (meaning t m 2881) (meaning t m 2891) (meaning t m 3379) (meaning t m 3948) source

theorem rule15055 (p2253 p2946 p3412 p3555 : Prop) (h : (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p2253)) : (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial15055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory4471 (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 5)
  exact rule15055 (meaning t m 2253) (meaning t m 2946) (meaning t m 3412) (meaning t m 3555) source

theorem rule15060 (p2246 p2651 p4111 : Prop) (h : (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2246)) : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4476 (m.theta 0 3) (m.theta 1 3) (m.theta 3 4)
  exact rule15060 (meaning t m 2246) (meaning t m 2651) (meaning t m 4111) source

theorem rule15061 (p1997 p2027 p2633 p2972 p3486 p3570 p4948 : Prop) (h : p2027 ∨ (¬ p1997) ∨ (¬ p3570) ∨ (¬ p4948) ∨ p2633 ∨ (¬ p3486) ∨ (¬ p2972)) : (¬ p1997) ∨ (p2027) ∨ (p2633) ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial15061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory4477 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule15061 (meaning t m 1997) (meaning t m 2027) (meaning t m 2633) (meaning t m 2972) (meaning t m 3486) (meaning t m 3570) (meaning t m 4948) source

theorem rule15077 (p1992 p2027 p2598 p2633 p3425 p3585 p3659 : Prop) (h : p2633 ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p1992) ∨ (¬ p2598)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial15077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory4493 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule15077 (meaning t m 1992) (meaning t m 2027) (meaning t m 2598) (meaning t m 2633) (meaning t m 3425) (meaning t m 3585) (meaning t m 3659) source

theorem rule15079 (p3297 p3773 p5288 p5289 : Prop) (h : (¬ p3773) ∨ (¬ p5289) ∨ (¬ p5288) ∨ (¬ p3297)) : (¬ p3297) ∨ (¬ p3773) ∨ (¬ p5288) ∨ (¬ p5289) := by
  classical
  tauto

theorem initial15079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 5288)) ∨ (¬ (meaning t m 5289)) := by
  have source := ElevenTheory.theory4495 (m.theta 0 9) (m.theta 3 10) (m.theta 3 9) (m.theta 9 10)
  exact rule15079 (meaning t m 3297) (meaning t m 3773) (meaning t m 5288) (meaning t m 5289) source

theorem rule15080 (p4286 p4287 p5670 p5671 p5672 : Prop) : (p5670) ∨ (((¬ p5670) ∨ (¬ p4286) ∨ (¬ p4287) ∨ (¬ p5671) ∨ (¬ p5672))) := by
  classical
  tauto

theorem initial15080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5670) ∨ (meaning t m 6175) := by
  exact rule15080 (meaning t m 4286) (meaning t m 4287) (meaning t m 5670) (meaning t m 5671) (meaning t m 5672)

theorem rule15081 (p4286 p4287 p5670 p5671 p5672 : Prop) : (p4286) ∨ (((¬ p5670) ∨ (¬ p4286) ∨ (¬ p4287) ∨ (¬ p5671) ∨ (¬ p5672))) := by
  classical
  tauto

theorem initial15081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4286) ∨ (meaning t m 6175) := by
  exact rule15081 (meaning t m 4286) (meaning t m 4287) (meaning t m 5670) (meaning t m 5671) (meaning t m 5672)

theorem rule15086 (p4149 p4239 p5674 p5675 p5676 : Prop) : (p5674) ∨ (((¬ p5674) ∨ (¬ p4239) ∨ (¬ p4149) ∨ (¬ p5675) ∨ (¬ p5676))) := by
  classical
  tauto

theorem initial15086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5674) ∨ (meaning t m 6176) := by
  exact rule15086 (meaning t m 4149) (meaning t m 4239) (meaning t m 5674) (meaning t m 5675) (meaning t m 5676)

theorem rule15088 (p4149 p4239 p5674 p5675 p5676 : Prop) : (p4149) ∨ (((¬ p5674) ∨ (¬ p4239) ∨ (¬ p4149) ∨ (¬ p5675) ∨ (¬ p5676))) := by
  classical
  tauto

theorem initial15088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4149) ∨ (meaning t m 6176) := by
  exact rule15088 (meaning t m 4149) (meaning t m 4239) (meaning t m 5674) (meaning t m 5675) (meaning t m 5676)

theorem rule15094 (p6175 p6176 : Prop) : (¬ ((¬ p6175) ∨ (¬ p6176))) ∨ (¬ p6175) ∨ (¬ p6176) := by
  classical
  tauto

theorem initial15094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6174)) ∨ (¬ (meaning t m 6175)) ∨ (¬ (meaning t m 6176)) := by
  exact rule15094 (meaning t m 6175) (meaning t m 6176)

theorem rule15095 (p5668 p6174 : Prop) (h : (p5668 ↔ p6174)) : (¬ p5668) ∨ (p6174) := by
  classical
  tauto

theorem initial15095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5668)) ∨ (meaning t m 6174) := by
  have source := ElevenTheory.theory4496 t (m.theta 4 10) (m.theta 4 8) (m.theta 8 10)
  exact rule15095 (meaning t m 5668) (meaning t m 6174) source

theorem rule15098 (p1982 p2027 p2202 p2563 p2619 p3146 p3758 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2563) ∨ (¬ p3146) ∨ p2202 ∨ (¬ p2619) ∨ (¬ p3758)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial15098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory4498 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule15098 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2619) (meaning t m 3146) (meaning t m 3758) source

theorem rule15099 (p2011 p2027 p2241 p2542 p2699 p2727 p2982 : Prop) (h : (¬ p2542) ∨ p2699 ∨ (¬ p2011) ∨ (¬ p2982) ∨ (¬ p2241) ∨ (¬ p2727) ∨ p2027) : (¬ p2011) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2982) := by
  classical
  tauto

theorem initial15099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2982)) := by
  have source := ElevenTheory.theory4499 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9)
  exact rule15099 (meaning t m 2011) (meaning t m 2027) (meaning t m 2241) (meaning t m 2542) (meaning t m 2699) (meaning t m 2727) (meaning t m 2982) source

theorem rule15103 (p1981 p2027 p2323 p2510 p2528 p2651 p3016 p4347 : Prop) (h : (¬ p1981) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4347) ∨ (¬ p2510) ∨ p2323 ∨ (¬ p3016)) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial15103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4503 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule15103 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2510) (meaning t m 2528) (meaning t m 2651) (meaning t m 3016) (meaning t m 4347) source

theorem rule15106 (p2007 p2027 p2534 p2619 p2765 p3146 p3758 : Prop) (h : p2027 ∨ (¬ p2007) ∨ (¬ p3758) ∨ (¬ p2534) ∨ (¬ p2619) ∨ (¬ p3146) ∨ p2765) : (¬ p2007) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial15106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory4506 t (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule15106 (meaning t m 2007) (meaning t m 2027) (meaning t m 2534) (meaning t m 2619) (meaning t m 2765) (meaning t m 3146) (meaning t m 3758) source

theorem rule15107 (p1985 p2202 p2891 p4629 : Prop) (h : (¬ p1985) ∨ p2202 ∨ (¬ p2891) ∨ p4629) : (¬ p1985) ∨ (p2202) ∨ (¬ p2891) ∨ (p4629) := by
  classical
  tauto

theorem initial15107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2891)) ∨ (meaning t m 4629) := by
  have source := ElevenTheory.theory4507 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule15107 (meaning t m 1985) (meaning t m 2202) (meaning t m 2891) (meaning t m 4629) source

theorem rule15109 (p3551 p3644 p4279 : Prop) (h : (¬ p3551) ∨ (¬ p4279) ∨ p3644) : (¬ p3551) ∨ (p3644) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial15109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3551)) ∨ (meaning t m 3644) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory4509 (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule15109 (meaning t m 3551) (meaning t m 3644) (meaning t m 4279) source

theorem rule15110 (p3551 p3657 p3821 : Prop) (h : (¬ p3551) ∨ (¬ p3657) ∨ p3821) : (¬ p3551) ∨ (¬ p3657) ∨ (p3821) := by
  classical
  tauto

theorem initial15110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 3821) := by
  have source := ElevenTheory.theory4510 (m.theta 0 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15110 (meaning t m 3551) (meaning t m 3657) (meaning t m 3821) source

theorem rule15111 (p1985 p2027 p2323 p2946 p3038 p3527 p3570 p3662 : Prop) (h : p2323 ∨ (¬ p1985) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3038) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial15111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory4511 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15111 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3038) (meaning t m 3527) (meaning t m 3570) (meaning t m 3662) source

theorem rule15113 (p1975 p2027 p2553 p2766 p3266 p4137 p4191 : Prop) (h : p2766 ∨ (¬ p3266) ∨ (¬ p1975) ∨ (¬ p4191) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p4137)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4513 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15113 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2766) (meaning t m 3266) (meaning t m 4137) (meaning t m 4191) source

theorem rule15114 (p1975 p2027 p2553 p2651 p3016 p3292 p3871 : Prop) (h : p3871 ∨ (¬ p1975) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3292)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3292) ∨ (p3871) := by
  classical
  tauto

theorem initial15114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3292)) ∨ (meaning t m 3871) := by
  have source := ElevenTheory.theory4514 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7)
  exact rule15114 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2651) (meaning t m 3016) (meaning t m 3292) (meaning t m 3871) source

theorem rule15117 (p1977 p2027 p2169 p2313 p2553 p2577 p2662 p3956 p4111 : Prop) (h : (¬ p3956) ∨ (¬ p2662) ∨ (¬ p4111) ∨ p2169 ∨ (¬ p1977) ∨ p2027 ∨ (¬ p2577) ∨ (¬ p2313) ∨ (¬ p2553)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3956) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4517 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15117 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2662) (meaning t m 3956) (meaning t m 4111) source

theorem rule15119 (p1979 p2027 p2169 p2992 p3574 p3956 p4111 : Prop) (h : (¬ p4111) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p2992) ∨ p2169 ∨ (¬ p3956) ∨ (¬ p3574)) : (¬ p1979) ∨ (p2027) ∨ (p2169) ∨ (¬ p2992) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4519 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 6 8)
  exact rule15119 (meaning t m 1979) (meaning t m 2027) (meaning t m 2169) (meaning t m 2992) (meaning t m 3574) (meaning t m 3956) (meaning t m 4111) source

theorem rule15122 (p1975 p2027 p2295 p2462 p2761 p4037 p4191 : Prop) (h : (¬ p1975) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p2295) ∨ p2462 ∨ p2027 ∨ (¬ p2761)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4522 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15122 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2462) (meaning t m 2761) (meaning t m 4037) (meaning t m 4191) source

theorem rule15123 (p1981 p2027 p2352 p2641 p2688 p3323 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p1981) ∨ (¬ p3323) ∨ (¬ p2352) ∨ (¬ p2641) ∨ p2688 ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3323) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4523 t (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15123 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2641) (meaning t m 2688) (meaning t m 3323) (meaning t m 4137) source

theorem rule15125 (p2246 p2331 p4245 p4319 : Prop) (h : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4319) ∨ (¬ p4245)) : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4245) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial15125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory4525 (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule15125 (meaning t m 2246) (meaning t m 2331) (meaning t m 4245) (meaning t m 4319) source

theorem rule15126 (p1998 p2027 p2177 p2323 p2553 p2651 p3016 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p2177) ∨ (¬ p1998) ∨ (¬ p2553)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2323) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial15126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory4526 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15126 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2323) (meaning t m 2553) (meaning t m 2651) (meaning t m 3016) source

theorem rule15128 (p1975 p2027 p2295 p2331 p2688 p2952 p2992 : Prop) (h : (¬ p2295) ∨ p2688 ∨ (¬ p2331) ∨ (¬ p1975) ∨ (¬ p2952) ∨ (¬ p2992) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial15128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory4528 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule15128 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) source

theorem rule15129 (p1992 p2027 p2143 p2462 p2881 p3551 p3583 p3690 p4984 : Prop) (h : (¬ p2143) ∨ p2027 ∨ (¬ p3551) ∨ p2462 ∨ (¬ p3690) ∨ (¬ p1992) ∨ (¬ p2881) ∨ (¬ p3583) ∨ (¬ p4984)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial15129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory4529 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15129 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2462) (meaning t m 2881) (meaning t m 3551) (meaning t m 3583) (meaning t m 3690) (meaning t m 4984) source

theorem rule15130 (p1981 p2027 p2114 p2352 p2651 p2737 p2811 p3016 : Prop) (h : (¬ p3016) ∨ p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2811) ∨ (¬ p2352) ∨ (¬ p2651)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial15130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory4530 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule15130 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2352) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3016) source

theorem rule15131 (p2006 p2027 p2132 p2622 p2743 p3055 p3367 : Prop) (h : (¬ p2743) ∨ (¬ p2006) ∨ p2027 ∨ p2622 ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3367)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial15131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory4531 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule15131 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2743) (meaning t m 3055) (meaning t m 3367) source

theorem rule15135 (p2006 p2027 p2462 p2839 p2881 p3548 p3690 p4400 : Prop) (h : p2462 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4400) ∨ (¬ p3548) ∨ (¬ p3690) ∨ (¬ p2006) ∨ (¬ p2839)) : (¬ p2006) ∨ (p2027) ∨ (p2462) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3690) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial15135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory4535 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15135 (meaning t m 2006) (meaning t m 2027) (meaning t m 2462) (meaning t m 2839) (meaning t m 2881) (meaning t m 3548) (meaning t m 3690) (meaning t m 4400) source

theorem rule15136 (p1975 p2027 p2553 p2598 p2622 p3016 p3365 p3683 : Prop) (h : (¬ p2553) ∨ (¬ p3016) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3683) ∨ (¬ p2598) ∨ p2622 ∨ (¬ p3365)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p3016) ∨ (¬ p3365) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial15136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory4536 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule15136 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2598) (meaning t m 2622) (meaning t m 3016) (meaning t m 3365) (meaning t m 3683) source

theorem rule15137 (p1996 p2462 p3553 p4666 : Prop) (h : (¬ p1996) ∨ (¬ p3553) ∨ p4666 ∨ p2462) : (¬ p1996) ∨ (p2462) ∨ (¬ p3553) ∨ (p4666) := by
  classical
  tauto

theorem initial15137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3553)) ∨ (meaning t m 4666) := by
  have source := ElevenTheory.theory4537 t (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15137 (meaning t m 1996) (meaning t m 2462) (meaning t m 3553) (meaning t m 4666) source

theorem rule15138 (p1975 p2027 p2299 p2323 p2651 p3189 p4111 p4378 : Prop) (h : (¬ p4378) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3189) ∨ (¬ p4111) ∨ p2323 ∨ (¬ p2651)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial15138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory4538 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule15138 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2323) (meaning t m 2651) (meaning t m 3189) (meaning t m 4111) (meaning t m 4378) source

theorem rule15139 (p1979 p2027 p2766 p2992 p2996 p3551 p4155 p4348 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p2996) ∨ p2766 ∨ (¬ p1979) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p2992)) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4539 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15139 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 2992) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) (meaning t m 4348) source

theorem rule15140 (p1979 p2027 p2992 p3146 p3177 p3578 p3857 p4360 : Prop) (h : (¬ p3146) ∨ p2027 ∨ p3578 ∨ (¬ p4360) ∨ (¬ p1979) ∨ (¬ p3857) ∨ (¬ p2992) ∨ (¬ p3177)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3177) ∨ (p3578) ∨ (¬ p3857) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial15140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3177)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory4540 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule15140 (meaning t m 1979) (meaning t m 2027) (meaning t m 2992) (meaning t m 3146) (meaning t m 3177) (meaning t m 3578) (meaning t m 3857) (meaning t m 4360) source

theorem rule15141 (p1978 p2027 p2766 p2870 p3556 p3694 p4132 p4348 : Prop) (h : (¬ p1978) ∨ p2766 ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4348) ∨ (¬ p4132) ∨ (¬ p3694)) : (¬ p1978) ∨ (p2027) ∨ (p2766) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4541 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15141 (meaning t m 1978) (meaning t m 2027) (meaning t m 2766) (meaning t m 2870) (meaning t m 3556) (meaning t m 3694) (meaning t m 4132) (meaning t m 4348) source

theorem rule15143 (p1992 p2027 p2462 p2761 p3583 p4322 p4385 : Prop) (h : p2027 ∨ p2462 ∨ (¬ p4385) ∨ (¬ p1992) ∨ (¬ p2761) ∨ (¬ p3583) ∨ (¬ p4322)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3583) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial15143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory4543 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15143 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3583) (meaning t m 4322) (meaning t m 4385) source

theorem rule15146 (p1992 p2027 p2143 p2764 p3556 p3583 p3690 p4381 : Prop) (h : (¬ p1992) ∨ p2764 ∨ (¬ p3556) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2143) ∨ (¬ p3690)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2764) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4546 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15146 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2764) (meaning t m 3556) (meaning t m 3583) (meaning t m 3690) (meaning t m 4381) source

theorem rule15147 (p1988 p2027 p2622 p2630 p3016 p3461 p3564 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3461) ∨ p2622 ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p2630)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3016) ∨ (¬ p3461) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial15147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory4547 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15147 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 3016) (meaning t m 3461) (meaning t m 3564) source

theorem rule15148 (p1979 p2027 p2187 p2387 p2667 p2765 p2992 p4154 : Prop) (h : (¬ p2992) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p2187) ∨ p2765 ∨ (¬ p4154) ∨ (¬ p2387) ∨ (¬ p2667)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (p2765) ∨ (¬ p2992) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4548 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15148 (meaning t m 1979) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2667) (meaning t m 2765) (meaning t m 2992) (meaning t m 4154) source

theorem rule15149 (p2005 p2027 p2122 p2588 p2608 p2699 p2829 : Prop) (h : (¬ p2005) ∨ p2699 ∨ (¬ p2588) ∨ (¬ p2122) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2608)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial15149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory4549 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15149 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) source

theorem rule15150 (p2005 p2027 p2699 p3379 p3422 p3801 p5681 : Prop) (h : (¬ p3379) ∨ (¬ p2005) ∨ (¬ p5681) ∨ p2699 ∨ (¬ p3422) ∨ p2027 ∨ (¬ p3801)) : (¬ p2005) ∨ (p2027) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3801) ∨ (¬ p5681) := by
  classical
  tauto

theorem initial15150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3801)) ∨ (¬ (meaning t m 5681)) := by
  have source := ElevenTheory.theory4550 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 10) (m.theta 4 6)
  exact rule15150 (meaning t m 2005) (meaning t m 2027) (meaning t m 2699) (meaning t m 3379) (meaning t m 3422) (meaning t m 3801) (meaning t m 5681) source

theorem rule15152 (p5679 p5680 p5681 p5682 p5683 : Prop) : (p5681) ∨ (((¬ p5680) ∨ (¬ p5681) ∨ (¬ p5679) ∨ (¬ p5682) ∨ (¬ p5683))) := by
  classical
  tauto

theorem initial15152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5681) ∨ (meaning t m 6178) := by
  exact rule15152 (meaning t m 5679) (meaning t m 5680) (meaning t m 5681) (meaning t m 5682) (meaning t m 5683)

theorem rule15159 (p4166 p5685 p5686 p5687 p5688 : Prop) : (p4166) ∨ (((¬ p5685) ∨ (¬ p5686) ∨ (¬ p4166) ∨ (¬ p5687) ∨ (¬ p5688))) := by
  classical
  tauto

theorem initial15159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4166) ∨ (meaning t m 6179) := by
  exact rule15159 (meaning t m 4166) (meaning t m 5685) (meaning t m 5686) (meaning t m 5687) (meaning t m 5688)

theorem rule15165 (p6178 p6179 : Prop) : (¬ ((¬ p6178) ∨ (¬ p6179))) ∨ (¬ p6178) ∨ (¬ p6179) := by
  classical
  tauto

theorem initial15165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6177)) ∨ (¬ (meaning t m 6178)) ∨ (¬ (meaning t m 6179)) := by
  exact rule15165 (meaning t m 6178) (meaning t m 6179)

theorem rule15166 (p5677 p6177 : Prop) (h : (p5677 ↔ p6177)) : (¬ p5677) ∨ (p6177) := by
  classical
  tauto

theorem initial15166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5677)) ∨ (meaning t m 6177) := by
  have source := ElevenTheory.theory4551 t (m.theta 2 10) (m.theta 2 4) (m.theta 4 10)
  exact rule15166 (meaning t m 5677) (meaning t m 6177) source

theorem rule15168 (p1988 p2027 p2608 p2699 p3276 p3333 p3367 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p1988) ∨ (¬ p3276) ∨ (¬ p3333)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial15168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory4552 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 9 10)
  exact rule15168 (meaning t m 1988) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3276) (meaning t m 3333) (meaning t m 3367) source

theorem rule15169 (p1975 p2027 p2323 p2470 p2553 p2663 p3016 p4256 : Prop) (h : p2323 ∨ (¬ p2553) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3016) ∨ (¬ p2663) ∨ (¬ p2470) ∨ (¬ p4256)) : (¬ p1975) ∨ (p2027) ∨ (p2323) ∨ (¬ p2470) ∨ (¬ p2553) ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial15169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory4553 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule15169 (meaning t m 1975) (meaning t m 2027) (meaning t m 2323) (meaning t m 2470) (meaning t m 2553) (meaning t m 2663) (meaning t m 3016) (meaning t m 4256) source

theorem rule15171 (p1979 p2027 p2132 p2622 p2870 p3365 p4320 : Prop) (h : (¬ p2870) ∨ (¬ p4320) ∨ p2622 ∨ (¬ p1979) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3365)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2870) ∨ (¬ p3365) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory4555 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule15171 (meaning t m 1979) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2870) (meaning t m 3365) (meaning t m 4320) source

theorem rule15173 (p1982 p2027 p2202 p2220 p2427 p2459 p3556 p4042 : Prop) (h : p2027 ∨ (¬ p4042) ∨ p2202 ∨ (¬ p2427) ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p3556) ∨ (¬ p2220)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p3556) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial15173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory4557 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15173 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2220) (meaning t m 2427) (meaning t m 2459) (meaning t m 3556) (meaning t m 4042) source

theorem rule15175 (p1983 p2027 p2312 p2341 p2553 p3008 p3246 p3570 : Prop) (h : p3008 ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2553) ∨ (¬ p2312) ∨ (¬ p1983) ∨ (¬ p3246) ∨ (¬ p3570)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3246) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial15175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory4559 t (m.theta 0 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15175 (meaning t m 1983) (meaning t m 2027) (meaning t m 2312) (meaning t m 2341) (meaning t m 2553) (meaning t m 3008) (meaning t m 3246) (meaning t m 3570) source

theorem rule15176 (p1990 p2027 p2417 p2633 p3097 p3644 p4107 : Prop) (h : (¬ p3644) ∨ p2633 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2417) ∨ (¬ p1990) ∨ (¬ p4107)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3644) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial15176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4560 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15176 (meaning t m 1990) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 3097) (meaning t m 3644) (meaning t m 4107) source

theorem rule15177 (p1990 p2027 p2295 p2611 p2696 p2797 p3097 : Prop) (h : (¬ p2797) ∨ p2027 ∨ p2611 ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p2295) ∨ (¬ p2696)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial15177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory4561 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule15177 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2696) (meaning t m 2797) (meaning t m 3097) source

theorem rule15178 (p1979 p2027 p2765 p2992 p3125 p4037 p4154 : Prop) (h : (¬ p3125) ∨ p2765 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p1979) ∨ (¬ p4037)) : (¬ p1979) ∨ (p2027) ∨ (p2765) ∨ (¬ p2992) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4562 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule15178 (meaning t m 1979) (meaning t m 2027) (meaning t m 2765) (meaning t m 2992) (meaning t m 3125) (meaning t m 4037) (meaning t m 4154) source

theorem rule15179 (p1992 p2027 p2177 p2553 p3008 p3588 p3659 : Prop) (h : (¬ p2553) ∨ p3008 ∨ (¬ p3659) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2177) ∨ (¬ p3588)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3588) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial15179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory4563 t (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15179 (meaning t m 1992) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 3008) (meaning t m 3588) (meaning t m 3659) source

theorem rule15180 (p2177 p2318 p3551 : Prop) (h : (¬ p3551) ∨ (¬ p2177) ∨ (¬ p2318)) : (¬ p2177) ∨ (¬ p2318) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial15180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory4564 (m.theta 0 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15180 (meaning t m 2177) (meaning t m 2318) (meaning t m 3551) source

theorem rule15181 (p1997 p2027 p2764 p3989 p4110 p4347 p4444 : Prop) (h : (¬ p1997) ∨ p2027 ∨ p2764 ∨ (¬ p4347) ∨ (¬ p4110) ∨ (¬ p3989) ∨ (¬ p4444)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4565 t (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15181 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 3989) (meaning t m 4110) (meaning t m 4347) (meaning t m 4444) source

theorem rule15186 (p1992 p2027 p2143 p2766 p3583 p3646 p3989 p4347 : Prop) (h : (¬ p2143) ∨ (¬ p3989) ∨ (¬ p1992) ∨ (¬ p3646) ∨ p2766 ∨ p2027 ∨ (¬ p3583) ∨ (¬ p4347)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial15186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4570 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule15186 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2766) (meaning t m 3583) (meaning t m 3646) (meaning t m 3989) (meaning t m 4347) source

theorem rule15187 (p1977 p2027 p2462 p2957 p3097 p3646 p3662 p4107 : Prop) (h : (¬ p3097) ∨ (¬ p1977) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2957) ∨ p2462 ∨ (¬ p4107) ∨ (¬ p3662)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial15187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4571 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule15187 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2957) (meaning t m 3097) (meaning t m 3646) (meaning t m 3662) (meaning t m 4107) source

theorem rule15188 (p1978 p2027 p2177 p2462 p3556 p3570 p4107 : Prop) (h : (¬ p2177) ∨ p2462 ∨ (¬ p1978) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p4107)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial15188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4572 t (m.theta 0 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15188 (meaning t m 1978) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3556) (meaning t m 3570) (meaning t m 4107) source

theorem rule15190 (p1987 p2027 p2462 p2957 p3097 p3646 p4107 p4315 : Prop) (h : (¬ p3646) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p4107) ∨ (¬ p1987) ∨ (¬ p3097) ∨ p2462 ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial15190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory4574 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule15190 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2957) (meaning t m 3097) (meaning t m 3646) (meaning t m 4107) (meaning t m 4315) source

theorem rule15191 (p1985 p2027 p2323 p2427 p2651 p2810 p3136 p4241 : Prop) (h : (¬ p2651) ∨ (¬ p2810) ∨ p2027 ∨ p2323 ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p2427) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial15191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory4575 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule15191 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2427) (meaning t m 2651) (meaning t m 2810) (meaning t m 3136) (meaning t m 4241) source

theorem rule15192 (p1979 p2323 p2651 p4704 : Prop) (h : p2323 ∨ (¬ p1979) ∨ (¬ p2651) ∨ p4704) : (¬ p1979) ∨ (p2323) ∨ (¬ p2651) ∨ (p4704) := by
  classical
  tauto

theorem initial15192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 4704) := by
  have source := ElevenTheory.theory4576 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule15192 (meaning t m 1979) (meaning t m 2323) (meaning t m 2651) (meaning t m 4704) source

theorem rule15193 (p1996 p2027 p2881 p2938 p3516 p3551 p3947 : Prop) (h : (¬ p1996) ∨ p2938 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p3551)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial15193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory4577 t (m.theta 0 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15193 (meaning t m 1996) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3516) (meaning t m 3551) (meaning t m 3947) source

theorem rule15198 (p2005 p2027 p2202 p2493 p2589 p2928 p3389 : Prop) (h : (¬ p2589) ∨ (¬ p3389) ∨ p2202 ∨ (¬ p2928) ∨ (¬ p2005) ∨ p2027 ∨ (¬ p2493)) : (¬ p2005) ∨ (p2027) ∨ (p2202) ∨ (¬ p2493) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial15198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory4582 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule15198 (meaning t m 2005) (meaning t m 2027) (meaning t m 2202) (meaning t m 2493) (meaning t m 2589) (meaning t m 2928) (meaning t m 3389) source

theorem rule15199 (p1977 p2027 p2177 p2667 p2997 p3941 p4154 p4197 p5590 : Prop) (h : (¬ p2667) ∨ (¬ p4154) ∨ (¬ p2177) ∨ p2997 ∨ p2027 ∨ (¬ p4197) ∨ (¬ p1977) ∨ (¬ p3941) ∨ (¬ p5590)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2667) ∨ (p2997) ∨ (¬ p3941) ∨ (¬ p4154) ∨ (¬ p4197) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial15199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory4583 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule15199 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2667) (meaning t m 2997) (meaning t m 3941) (meaning t m 4154) (meaning t m 4197) (meaning t m 5590) source

theorem rule15200 (p2011 p2027 p2284 p2323 p2946 p2982 p4110 : Prop) (h : (¬ p2011) ∨ p2323 ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2982)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p2982) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4584 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule15200 (meaning t m 2011) (meaning t m 2027) (meaning t m 2284) (meaning t m 2323) (meaning t m 2946) (meaning t m 2982) (meaning t m 4110) source

theorem rule15201 (p2004 p2027 p2202 p2417 p2589 p3389 p3817 : Prop) (h : p2027 ∨ (¬ p3817) ∨ (¬ p2004) ∨ (¬ p2417) ∨ (¬ p3389) ∨ (¬ p2589) ∨ p2202) : (¬ p2004) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial15201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory4585 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule15201 (meaning t m 2004) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2589) (meaning t m 3389) (meaning t m 3817) source

theorem rule15202 (p1988 p2027 p2177 p2761 p2997 p3546 p3551 p3631 : Prop) (h : (¬ p3551) ∨ p2027 ∨ (¬ p3546) ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p3631) ∨ p2997 ∨ (¬ p2177)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2761) ∨ (p2997) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial15202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory4586 t (m.theta 0 7) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule15202 (meaning t m 1988) (meaning t m 2027) (meaning t m 2177) (meaning t m 2761) (meaning t m 2997) (meaning t m 3546) (meaning t m 3551) (meaning t m 3631) source

theorem rule15204 (p1982 p2027 p2177 p2997 p3146 p3960 p3998 p5568 : Prop) (h : (¬ p1982) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p3960) ∨ (¬ p2177) ∨ p2997 ∨ (¬ p5568) ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3146) ∨ (¬ p3960) ∨ (¬ p3998) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial15204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory4588 t (m.theta 0 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15204 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3146) (meaning t m 3960) (meaning t m 3998) (meaning t m 5568) source

theorem rule15205 (p1997 p2027 p2191 p2192 p2619 p2842 p3582 p4110 : Prop) (h : (¬ p1997) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3582) ∨ p2842 ∨ (¬ p4110) ∨ (¬ p2619) ∨ (¬ p2191)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2619) ∨ (p2842) ∨ (¬ p3582) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4589 t (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15205 (meaning t m 1997) (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2619) (meaning t m 2842) (meaning t m 3582) (meaning t m 4110) source

theorem rule15210 (p1980 p2027 p2177 p2641 p2996 p2997 p3551 p4155 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p1980) ∨ (¬ p2641) ∨ (¬ p3551) ∨ (¬ p2177) ∨ (¬ p2996) ∨ (¬ p4155)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial15210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory4594 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15210 (meaning t m 1980) (meaning t m 2027) (meaning t m 2177) (meaning t m 2641) (meaning t m 2996) (meaning t m 2997) (meaning t m 3551) (meaning t m 4155) source

theorem rule15211 (p1977 p2027 p2177 p2462 p2996 p3551 p4107 p4155 : Prop) (h : (¬ p4155) ∨ (¬ p3551) ∨ p2462 ∨ (¬ p2177) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2996) ∨ (¬ p4107)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial15211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory4595 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15211 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 2996) (meaning t m 3551) (meaning t m 4107) (meaning t m 4155) source

theorem rule15213 (p1997 p2027 p2633 p3434 p3659 p3690 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3434) ∨ p2633 ∨ (¬ p3690)) : (¬ p1997) ∨ (p2027) ∨ (p2633) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3690) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4597 t (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15213 (meaning t m 1997) (meaning t m 2027) (meaning t m 2633) (meaning t m 3434) (meaning t m 3659) (meaning t m 3690) (meaning t m 4235) source

theorem rule15214 (p1982 p2027 p2177 p2997 p3146 p3941 p4115 p5590 : Prop) (h : (¬ p1982) ∨ p2997 ∨ (¬ p5590) ∨ (¬ p3941) ∨ (¬ p3146) ∨ (¬ p2177) ∨ (¬ p4115) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3146) ∨ (¬ p3941) ∨ (¬ p4115) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial15214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory4598 t (m.theta 0 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15214 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3146) (meaning t m 3941) (meaning t m 4115) (meaning t m 5590) source

theorem rule15215 (p1976 p2027 p2396 p2997 p3055 p3876 p4278 : Prop) (h : (¬ p2396) ∨ p2997 ∨ (¬ p4278) ∨ (¬ p3055) ∨ (¬ p1976) ∨ (¬ p3876) ∨ p2027) : (¬ p1976) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4599 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule15215 (meaning t m 1976) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) source

theorem rule15216 (p1977 p2027 p2667 p2766 p3266 p3946 p4154 p4191 : Prop) (h : (¬ p3266) ∨ p2766 ∨ (¬ p4191) ∨ (¬ p3946) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2667)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2667) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4600 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15216 (meaning t m 1977) (meaning t m 2027) (meaning t m 2667) (meaning t m 2766) (meaning t m 3266) (meaning t m 3946) (meaning t m 4154) (meaning t m 4191) source

theorem rule15218 (p2311 p2577 p5197 : Prop) (h : (¬ p2577) ∨ (¬ p2311) ∨ p5197) : (¬ p2311) ∨ (¬ p2577) ∨ (p5197) := by
  classical
  tauto

theorem initial15218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 5197) := by
  have source := ElevenTheory.theory4602 (m.theta 0 4) (m.theta 0 6) (m.theta 0 7)
  exact rule15218 (meaning t m 2311) (meaning t m 2577) (meaning t m 5197) source

theorem rule15219 (p1982 p2027 p2528 p2608 p2699 p3367 p3641 : Prop) (h : (¬ p3641) ∨ p2699 ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p2608) ∨ (¬ p1982) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3367) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial15219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory4603 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9)
  exact rule15219 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2608) (meaning t m 2699) (meaning t m 3367) (meaning t m 3641) source

theorem rule15220 (p2005 p2027 p2311 p2881 p2938 p3551 p3654 p4137 : Prop) (h : p2938 ∨ (¬ p3654) ∨ (¬ p3551) ∨ (¬ p2311) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2005) ∨ (¬ p4137)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2311) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3551) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4604 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8)
  exact rule15220 (meaning t m 2005) (meaning t m 2027) (meaning t m 2311) (meaning t m 2881) (meaning t m 2938) (meaning t m 3551) (meaning t m 3654) (meaning t m 4137) source

theorem rule15222 (p1977 p2027 p2766 p2957 p3646 p3662 p3989 p4347 : Prop) (h : (¬ p1977) ∨ (¬ p3662) ∨ (¬ p2957) ∨ (¬ p3989) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p4347) ∨ p2766) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial15222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4606 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule15222 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 3989) (meaning t m 4347) source

theorem rule15224 (p1977 p2027 p2177 p2957 p2997 p3556 p3570 p3662 : Prop) (h : (¬ p2957) ∨ p2027 ∨ p2997 ∨ (¬ p2177) ∨ (¬ p3662) ∨ (¬ p1977) ∨ (¬ p3556) ∨ (¬ p3570)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial15224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory4608 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15224 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2957) (meaning t m 2997) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) source

theorem rule15226 (p1977 p2027 p2299 p2579 p2588 p2633 p2662 p4111 : Prop) (h : p2027 ∨ (¬ p1977) ∨ (¬ p4111) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2662) ∨ p2633 ∨ (¬ p2588)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4610 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15226 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2633) (meaning t m 2662) (meaning t m 4111) source

theorem rule15227 (p2015 p2027 p2122 p2622 p2774 p3365 p3549 : Prop) (h : (¬ p3365) ∨ (¬ p2015) ∨ p2622 ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2122) ∨ (¬ p2774)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2122) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial15227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory4611 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule15227 (meaning t m 2015) (meaning t m 2027) (meaning t m 2122) (meaning t m 2622) (meaning t m 2774) (meaning t m 3365) (meaning t m 3549) source

theorem rule15228 (p1992 p2027 p2633 p2774 p3425 p3659 p3688 : Prop) (h : p2633 ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3659)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial15228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory4612 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 7 8)
  exact rule15228 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 2774) (meaning t m 3425) (meaning t m 3659) (meaning t m 3688) source

theorem rule15230 (p2005 p2027 p2323 p2493 p2509 p2651 p3083 : Prop) (h : p2323 ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2323) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2651) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial15230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory4614 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule15230 (meaning t m 2005) (meaning t m 2027) (meaning t m 2323) (meaning t m 2493) (meaning t m 2509) (meaning t m 2651) (meaning t m 3083) source

theorem rule15231 (p1979 p2027 p2459 p2633 p2992 p4118 p4360 : Prop) (h : (¬ p4360) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2992) ∨ (¬ p1979) ∨ p2633 ∨ (¬ p4118)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2992) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial15231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory4615 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15231 (meaning t m 1979) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2992) (meaning t m 4118) (meaning t m 4360) source

theorem rule15233 (p1997 p2027 p2132 p2619 p2780 p3586 p3880 : Prop) (h : p3586 ∨ (¬ p3880) ∨ (¬ p2132) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (p3586) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4617 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8)
  exact rule15233 (meaning t m 1997) (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2780) (meaning t m 3586) (meaning t m 3880) source

theorem rule15234 (p1979 p2027 p2766 p3136 p3570 p3572 p3699 p4348 : Prop) (h : p2027 ∨ (¬ p3699) ∨ (¬ p3570) ∨ p2766 ∨ (¬ p3572) ∨ (¬ p4348) ∨ (¬ p1979) ∨ (¬ p3136)) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p3136) ∨ (¬ p3570) ∨ (¬ p3572) ∨ (¬ p3699) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4618 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15234 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 3136) (meaning t m 3570) (meaning t m 3572) (meaning t m 3699) (meaning t m 4348) source

theorem rule15235 (p2005 p2588 p2938 p4559 : Prop) (h : (¬ p2005) ∨ p2938 ∨ (¬ p2588) ∨ p4559) : (¬ p2005) ∨ (¬ p2588) ∨ (p2938) ∨ (p4559) := by
  classical
  tauto

theorem initial15235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2938) ∨ (meaning t m 4559) := by
  have source := ElevenTheory.theory4619 t (m.theta 4 6) (m.theta 5 7) (m.theta 6 7)
  exact rule15235 (meaning t m 2005) (meaning t m 2588) (meaning t m 2938) (meaning t m 4559) source

theorem rule15236 (p1979 p2027 p2299 p2396 p2633 p3690 p4320 : Prop) (h : (¬ p4320) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3690) ∨ (¬ p1979) ∨ p2027) : (¬ p1979) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3690) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory4620 t (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15236 (meaning t m 1979) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3690) (meaning t m 4320) source

theorem rule15237 (p1992 p2027 p2143 p2299 p2633 p3097 p3583 p3646 : Prop) (h : (¬ p3646) ∨ p2633 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial15237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory4621 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15237 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2299) (meaning t m 2633) (meaning t m 3097) (meaning t m 3583) (meaning t m 3646) source

theorem rule15238 (p1997 p2027 p2156 p2299 p2633 p3556 p4110 p4275 : Prop) (h : p2633 ∨ (¬ p4110) ∨ (¬ p1997) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4275) ∨ (¬ p3556) ∨ (¬ p2299)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial15238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory4622 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15238 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2299) (meaning t m 2633) (meaning t m 3556) (meaning t m 4110) (meaning t m 4275) source

theorem rule15239 (p2001 p2027 p2220 p2462 p3097 p3646 p4107 : Prop) (h : (¬ p4107) ∨ p2462 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2001) ∨ (¬ p3646) ∨ (¬ p2220)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2220) ∨ (p2462) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial15239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4623 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9)
  exact rule15239 (meaning t m 2001) (meaning t m 2027) (meaning t m 2220) (meaning t m 2462) (meaning t m 3097) (meaning t m 3646) (meaning t m 4107) source

theorem rule15242 (p1977 p2027 p2187 p2387 p2957 p2997 p3097 p3662 p4198 : Prop) (h : (¬ p1977) ∨ (¬ p3662) ∨ (¬ p2957) ∨ p2997 ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2187) ∨ (¬ p4198)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial15242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory4626 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15242 (meaning t m 1977) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2957) (meaning t m 2997) (meaning t m 3097) (meaning t m 3662) (meaning t m 4198) source

theorem rule15244 (p1992 p2027 p2132 p2881 p2938 p3551 p3583 p3820 : Prop) (h : p2938 ∨ (¬ p2881) ∨ (¬ p1992) ∨ (¬ p2132) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3820) ∨ (¬ p3551)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3551) ∨ (¬ p3583) ∨ (¬ p3820) := by
  classical
  tauto

theorem initial15244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3820)) := by
  have source := ElevenTheory.theory4628 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15244 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2881) (meaning t m 2938) (meaning t m 3551) (meaning t m 3583) (meaning t m 3820) source

theorem rule15245 (p1992 p2027 p2169 p3125 p3583 p3917 p3989 p4193 : Prop) (h : (¬ p4193) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3583) ∨ p2169 ∨ (¬ p3917) ∨ (¬ p3125) ∨ (¬ p3989)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p3125) ∨ (¬ p3583) ∨ (¬ p3917) ∨ (¬ p3989) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial15245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory4629 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15245 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 3125) (meaning t m 3583) (meaning t m 3917) (meaning t m 3989) (meaning t m 4193) source

theorem rule15246 (p1992 p2027 p2143 p2764 p3583 p3646 p3744 p4191 : Prop) (h : (¬ p3744) ∨ (¬ p3646) ∨ (¬ p1992) ∨ p2764 ∨ p2027 ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p4191)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4630 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15246 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2764) (meaning t m 3583) (meaning t m 3646) (meaning t m 3744) (meaning t m 4191) source

theorem rule15252 (p1997 p2027 p2462 p2761 p3744 p4110 p4191 : Prop) (h : (¬ p3744) ∨ (¬ p1997) ∨ (¬ p2761) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p4191) ∨ p2462) : (¬ p1997) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4636 t (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15252 (meaning t m 1997) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3744) (meaning t m 4110) (meaning t m 4191) source

theorem rule15255 (p1997 p2027 p2839 p2842 p3105 p3585 p4948 : Prop) (h : (¬ p1997) ∨ p2842 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3105) ∨ (¬ p2839) ∨ (¬ p4948)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p3105) ∨ (¬ p3585) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial15255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory4639 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule15255 (meaning t m 1997) (meaning t m 2027) (meaning t m 2839) (meaning t m 2842) (meaning t m 3105) (meaning t m 3585) (meaning t m 4948) source

theorem rule15258 (p1992 p2027 p2299 p2313 p2766 p2785 p3688 p4348 : Prop) (h : p2766 ∨ (¬ p1992) ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2299)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4642 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15258 (meaning t m 1992) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2766) (meaning t m 2785) (meaning t m 3688) (meaning t m 4348) source

theorem rule15259 (p2005 p2027 p2323 p2588 p2651 p3027 p3552 p4111 : Prop) (h : (¬ p2005) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p4111) ∨ p2323 ∨ (¬ p3552)) : (¬ p2005) ∨ (p2027) ∨ (p2323) ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4643 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule15259 (meaning t m 2005) (meaning t m 2027) (meaning t m 2323) (meaning t m 2588) (meaning t m 2651) (meaning t m 3027) (meaning t m 3552) (meaning t m 4111) source

theorem rule15261 (p5691 p5692 p5693 p5694 p5695 : Prop) : (p5693) ∨ (((¬ p5692) ∨ (¬ p5693) ∨ (¬ p5691) ∨ (¬ p5694) ∨ (¬ p5695))) := by
  classical
  tauto

theorem initial15261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5693) ∨ (meaning t m 6181) := by
  exact rule15261 (meaning t m 5691) (meaning t m 5692) (meaning t m 5693) (meaning t m 5694) (meaning t m 5695)

theorem rule15266 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p5697) ∨ (((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5697) ∨ (meaning t m 6182) := by
  exact rule15266 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15267 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p5698) ∨ (((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5698) ∨ (meaning t m 6182) := by
  exact rule15267 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15268 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p4181) ∨ (((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4181) ∨ (meaning t m 6182) := by
  exact rule15268 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15269 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p5699) ∨ (((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5699) ∨ (meaning t m 6182) := by
  exact rule15269 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15270 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p5700) ∨ (((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5700) ∨ (meaning t m 6182) := by
  exact rule15270 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15271 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ p4181) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p5699) ∨ (¬ p5700) ∨ (¬ ((¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) ∨ (¬ p5699) ∨ (¬ p5700))) := by
  classical
  tauto

theorem initial15271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5697)) ∨ (¬ (meaning t m 5698)) ∨ (¬ (meaning t m 5699)) ∨ (¬ (meaning t m 5700)) ∨ (¬ (meaning t m 6182)) := by
  exact rule15271 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule15274 (p6181 p6182 : Prop) : (¬ ((¬ p6181) ∨ (¬ p6182))) ∨ (¬ p6181) ∨ (¬ p6182) := by
  classical
  tauto

theorem initial15274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6180)) ∨ (¬ (meaning t m 6181)) ∨ (¬ (meaning t m 6182)) := by
  exact rule15274 (meaning t m 6181) (meaning t m 6182)

theorem rule15275 (p5689 p6180 : Prop) (h : (p5689 ↔ p6180)) : (¬ p5689) ∨ (p6180) := by
  classical
  tauto

theorem initial15275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5689)) ∨ (meaning t m 6180) := by
  have source := ElevenTheory.theory4644 t (m.theta 1 10) (m.theta 1 8) (m.theta 8 10)
  exact rule15275 (meaning t m 5689) (meaning t m 6180) source

theorem rule15278 (p1977 p2027 p2313 p2667 p2764 p4107 p4154 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p2313) ∨ (¬ p1977) ∨ (¬ p4154) ∨ (¬ p2667) ∨ p2027 ∨ (¬ p4107) ∨ p2764) : (¬ p1977) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4154) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4646 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15278 (meaning t m 1977) (meaning t m 2027) (meaning t m 2313) (meaning t m 2667) (meaning t m 2764) (meaning t m 4107) (meaning t m 4154) (meaning t m 4381) source

theorem rule15279 (p1977 p2027 p2299 p2313 p2667 p2766 p4154 p4348 : Prop) (h : p2027 ∨ (¬ p2313) ∨ (¬ p1977) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p4348) ∨ p2766 ∨ (¬ p2299)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (p2766) ∨ (¬ p4154) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4647 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15279 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2667) (meaning t m 2766) (meaning t m 4154) (meaning t m 4348) source

theorem rule15280 (p1987 p2027 p2299 p2588 p2633 p2810 p3574 : Prop) (h : (¬ p2588) ∨ (¬ p1987) ∨ (¬ p2299) ∨ (¬ p2810) ∨ (¬ p3574) ∨ p2633 ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p2810) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial15280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory4648 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15280 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 2633) (meaning t m 2810) (meaning t m 3574) source

theorem rule15281 (p1980 p2027 p2641 p2766 p2996 p3551 p4155 p4348 : Prop) (h : (¬ p3551) ∨ p2766 ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p1980) ∨ p2027 ∨ (¬ p4155) ∨ (¬ p4348)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2641) ∨ (p2766) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4649 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15281 (meaning t m 1980) (meaning t m 2027) (meaning t m 2641) (meaning t m 2766) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) (meaning t m 4348) source

theorem rule15286 (p1985 p2027 p2166 p2210 p2699 p2870 p3694 : Prop) (h : p2699 ∨ (¬ p3694) ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2870) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial15286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory4654 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule15286 (meaning t m 1985) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 2870) (meaning t m 3694) source

theorem rule15287 (p1994 p2027 p2210 p2630 p2699 p2891 p4244 p4392 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2630) ∨ (¬ p1994) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p4392) ∨ (¬ p4244)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p4244) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial15287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory4655 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 5 7)
  exact rule15287 (meaning t m 1994) (meaning t m 2027) (meaning t m 2210) (meaning t m 2630) (meaning t m 2699) (meaning t m 2891) (meaning t m 4244) (meaning t m 4392) source

theorem rule15288 (p1994 p2027 p2299 p2440 p2633 p3097 p4110 : Prop) (h : (¬ p2299) ∨ (¬ p1994) ∨ p2633 ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4656 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15288 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2440) (meaning t m 2633) (meaning t m 3097) (meaning t m 4110) source

theorem rule15289 (p1990 p2027 p2253 p2284 p2699 p2807 p2992 p2996 : Prop) (h : (¬ p2996) ∨ p2699 ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial15289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory4657 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule15289 (meaning t m 1990) (meaning t m 2027) (meaning t m 2253) (meaning t m 2284) (meaning t m 2699) (meaning t m 2807) (meaning t m 2992) (meaning t m 2996) source

theorem rule15292 (p2000 p2027 p2299 p2579 p2633 p3422 p3876 p3921 : Prop) (h : (¬ p2000) ∨ (¬ p2579) ∨ p2633 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3876) ∨ (¬ p3422) ∨ (¬ p3921)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (p2633) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial15292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory4660 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15292 (meaning t m 2000) (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2633) (meaning t m 3422) (meaning t m 3876) (meaning t m 3921) source

theorem rule15295 (p2241 p3452 p4281 : Prop) (h : (¬ p3452) ∨ (¬ p4281) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p3452) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial15295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory4663 (m.theta 0 1) (m.theta 1 3) (m.theta 1 4)
  exact rule15295 (meaning t m 2241) (meaning t m 3452) (meaning t m 4281) source

theorem rule15296 (p1984 p2027 p2299 p2499 p2588 p2633 p3452 : Prop) (h : (¬ p2299) ∨ p2633 ∨ (¬ p1984) ∨ (¬ p3452) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2499)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial15296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4664 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15296 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2499) (meaning t m 2588) (meaning t m 2633) (meaning t m 3452) source

end SunPrize.SMT
