import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory051
import SunPrize.Certificate.Theory052
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule29325 (p2027 p2493 p2509 p2668 p4432 p4976 : Prop) (h : (¬ p4976) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4432) ∨ (¬ p2668) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p4432) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial29325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory18581 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule29325 (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2668) (meaning t m 4432) (meaning t m 4976) source

theorem rule29327 (p1998 p2027 p2274 p2396 p2765 p3527 p3817 : Prop) (h : p2765 ∨ (¬ p2274) ∨ (¬ p3527) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (p2765) ∨ (¬ p3527) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial29327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory18583 t (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29327 (meaning t m 1998) (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 2765) (meaning t m 3527) (meaning t m 3817) source

theorem rule29331 (p2027 p2598 p2685 p3414 p4236 p4752 : Prop) (h : (¬ p4236) ∨ (¬ p4752) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p4236) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial29331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory18587 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule29331 (meaning t m 2027) (meaning t m 2598) (meaning t m 2685) (meaning t m 3414) (meaning t m 4236) (meaning t m 4752) source

theorem rule29333 (p2663 p3389 p3414 p3740 : Prop) (h : (¬ p2663) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p3389)) : (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3414) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial29333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory18589 (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 7)
  exact rule29333 (meaning t m 2663) (meaning t m 3389) (meaning t m 3414) (meaning t m 3740) source

theorem rule29343 (p1982 p2027 p2202 p2482 p2589 p3146 p3998 p5568 : Prop) (h : p2202 ∨ p2027 ∨ (¬ p2482) ∨ (¬ p3998) ∨ (¬ p3146) ∨ (¬ p5568) ∨ (¬ p1982) ∨ (¬ p2589)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2482) ∨ (¬ p2589) ∨ (¬ p3146) ∨ (¬ p3998) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial29343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory18599 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29343 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2482) (meaning t m 2589) (meaning t m 3146) (meaning t m 3998) (meaning t m 5568) source

theorem rule29345 (p2027 p2122 p2312 p2641 p2996 p4155 p4846 : Prop) (h : (¬ p2996) ∨ (¬ p2122) ∨ (¬ p4155) ∨ (¬ p2312) ∨ (¬ p4846) ∨ p2027 ∨ (¬ p2641)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2312) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4155) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial29345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory18601 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule29345 (meaning t m 2027) (meaning t m 2122) (meaning t m 2312) (meaning t m 2641) (meaning t m 2996) (meaning t m 4155) (meaning t m 4846) source

theorem rule29346 (p2027 p2241 p2387 p3063 p4756 p5015 : Prop) (h : (¬ p4756) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p5015)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p4756) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial29346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4756)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory18602 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 6 8)
  exact rule29346 (meaning t m 2027) (meaning t m 2241) (meaning t m 2387) (meaning t m 3063) (meaning t m 4756) (meaning t m 5015) source

theorem rule29347 (p2027 p2352 p2641 p3177 p4170 p4360 p4973 : Prop) (h : (¬ p2352) ∨ (¬ p4973) ∨ p2027 ∨ (¬ p3177) ∨ (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4170)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2641) ∨ (¬ p3177) ∨ (¬ p4170) ∨ (¬ p4360) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial29347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory18603 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule29347 (meaning t m 2027) (meaning t m 2352) (meaning t m 2641) (meaning t m 3177) (meaning t m 4170) (meaning t m 4360) (meaning t m 4973) source

theorem rule29349 (p3747 p3880 p4235 : Prop) (h : (¬ p3880) ∨ (¬ p3747) ∨ p4235) : (¬ p3747) ∨ (¬ p3880) ∨ (p4235) := by
  classical
  tauto

theorem initial29349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3880)) ∨ (meaning t m 4235) := by
  have source := ElevenTheory.theory18605 (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule29349 (meaning t m 3747) (meaning t m 3880) (meaning t m 4235) source

theorem rule29351 (p1994 p2027 p2622 p2651 p2743 p2839 p2952 p5051 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p1994) ∨ (¬ p2839) ∨ p2622 ∨ (¬ p2952) ∨ (¬ p5051) ∨ (¬ p2743)) : (¬ p1994) ∨ (p2027) ∨ (p2622) ∨ (¬ p2651) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2952) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial29351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory18607 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule29351 (meaning t m 1994) (meaning t m 2027) (meaning t m 2622) (meaning t m 2651) (meaning t m 2743) (meaning t m 2839) (meaning t m 2952) (meaning t m 5051) source

theorem rule29352 (p1977 p2027 p2241 p2406 p2499 p2589 p3008 p4108 : Prop) (h : (¬ p4108) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2499) ∨ p3008 ∨ (¬ p2406) ∨ (¬ p2241) ∨ (¬ p2589)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (p3008) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial29352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory18608 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6)
  exact rule29352 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2406) (meaning t m 2499) (meaning t m 2589) (meaning t m 3008) (meaning t m 4108) source

theorem rule29353 (p1982 p2027 p2688 p2952 p2992 p3146 p3166 p4311 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p2992) ∨ (¬ p1982) ∨ p2688 ∨ (¬ p2952) ∨ (¬ p4311) ∨ (¬ p3166)) : (¬ p1982) ∨ (p2027) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3166) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial29353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory18609 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29353 (meaning t m 1982) (meaning t m 2027) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) (meaning t m 3146) (meaning t m 3166) (meaning t m 4311) source

theorem rule29355 (p2027 p2499 p2619 p3051 p3452 p3956 p4244 p4433 p4521 : Prop) (h : (¬ p3452) ∨ (¬ p2499) ∨ (¬ p4433) ∨ (¬ p4521) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4244)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4244) ∨ (¬ p4433) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial29355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory18611 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule29355 (meaning t m 2027) (meaning t m 2499) (meaning t m 2619) (meaning t m 3051) (meaning t m 3452) (meaning t m 3956) (meaning t m 4244) (meaning t m 4433) (meaning t m 4521) source

theorem rule29356 (p2027 p2528 p3646 p3692 p3741 p3875 p3988 p4533 : Prop) (h : (¬ p3875) ∨ (¬ p3741) ∨ (¬ p4533) ∨ (¬ p3988) ∨ (¬ p3646) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3692)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3741) ∨ (¬ p3875) ∨ (¬ p3988) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial29356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory18612 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule29356 (meaning t m 2027) (meaning t m 2528) (meaning t m 3646) (meaning t m 3692) (meaning t m 3741) (meaning t m 3875) (meaning t m 3988) (meaning t m 4533) source

theorem rule29363 (p2110 p2786 p4197 : Prop) (h : (¬ p2110) ∨ (¬ p4197) ∨ p2786) : (¬ p2110) ∨ (p2786) ∨ (¬ p4197) := by
  classical
  tauto

theorem initial29363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2110)) ∨ (meaning t m 2786) ∨ (¬ (meaning t m 4197)) := by
  have source := ElevenTheory.theory18619 (m.theta 0 2) (m.theta 0 6) (m.theta 0 8)
  exact rule29363 (meaning t m 2110) (meaning t m 2786) (meaning t m 4197) source

theorem rule29369 (p2027 p2311 p2396 p2553 p2581 p3821 : Prop) (h : (¬ p2396) ∨ (¬ p2311) ∨ (¬ p2581) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3821)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial29369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory18625 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule29369 (meaning t m 2027) (meaning t m 2311) (meaning t m 2396) (meaning t m 2553) (meaning t m 2581) (meaning t m 3821) source

theorem rule29371 (p1980 p2027 p2307 p2657 p2688 p2727 p3568 p3987 : Prop) (h : (¬ p2307) ∨ (¬ p3987) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2727) ∨ p2688 ∨ (¬ p1980) ∨ (¬ p3568)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3568) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial29371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory18627 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule29371 (meaning t m 1980) (meaning t m 2027) (meaning t m 2307) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3568) (meaning t m 3987) source

theorem rule29372 (p2027 p2088 p2248 p2928 p3178 p3452 p4009 p4118 p5503 p5565 : Prop) (h : (¬ p5565) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p4009) ∨ (¬ p2088) ∨ (¬ p3178) ∨ (¬ p2928) ∨ (¬ p4118) ∨ (¬ p5503)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3178) ∨ (¬ p3452) ∨ (¬ p4009) ∨ (¬ p4118) ∨ (¬ p5503) ∨ (¬ p5565) := by
  classical
  tauto

theorem initial29372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5565)) := by
  have source := ElevenTheory.theory18628 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 8) (m.theta 1 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 10) (m.theta 8 9)
  exact rule29372 (meaning t m 2027) (meaning t m 2088) (meaning t m 2248) (meaning t m 2928) (meaning t m 3178) (meaning t m 3452) (meaning t m 4009) (meaning t m 4118) (meaning t m 5503) (meaning t m 5565) source

theorem rule29384 (p1990 p2027 p2764 p3063 p3989 p4026 p4191 : Prop) (h : (¬ p3989) ∨ (¬ p1990) ∨ p2027 ∨ p2764 ∨ (¬ p4191) ∨ (¬ p4026) ∨ (¬ p3063)) : (¬ p1990) ∨ (p2027) ∨ (p2764) ∨ (¬ p3063) ∨ (¬ p3989) ∨ (¬ p4026) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial29384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory18640 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule29384 (meaning t m 1990) (meaning t m 2027) (meaning t m 2764) (meaning t m 3063) (meaning t m 3989) (meaning t m 4026) (meaning t m 4191) source

theorem rule29385 (p4185 p4718 p5222 : Prop) (h : (¬ p4718) ∨ (¬ p4185) ∨ p5222) : (¬ p4185) ∨ (¬ p4718) ∨ (p5222) := by
  classical
  tauto

theorem initial29385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4718)) ∨ (meaning t m 5222) := by
  have source := ElevenTheory.theory18641 t (m.theta 2 6) (m.theta 4 6) (m.theta 5 6)
  exact rule29385 (meaning t m 4185) (meaning t m 4718) (meaning t m 5222) source

theorem rule29386 (p2027 p2132 p2619 p2657 p3146 p3742 p4278 p4669 p4789 : Prop) (h : (¬ p2619) ∨ (¬ p4789) ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p2132) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial29386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory18642 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule29386 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2657) (meaning t m 3146) (meaning t m 3742) (meaning t m 4278) (meaning t m 4669) (meaning t m 4789) source

theorem rule29389 (p1991 p2027 p2169 p2657 p2727 p3956 p4154 p4389 : Prop) (h : p2027 ∨ (¬ p4154) ∨ p2169 ∨ (¬ p3956) ∨ (¬ p4389) ∨ (¬ p1991) ∨ (¬ p2727) ∨ (¬ p2657)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3956) ∨ (¬ p4154) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial29389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory18645 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule29389 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2657) (meaning t m 2727) (meaning t m 3956) (meaning t m 4154) (meaning t m 4389) source

theorem rule29392 (p2027 p2295 p2396 p3324 p4138 p4668 : Prop) (h : (¬ p4138) ∨ (¬ p4668) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial29392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory18648 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule29392 (meaning t m 2027) (meaning t m 2295) (meaning t m 2396) (meaning t m 3324) (meaning t m 4138) (meaning t m 4668) source

theorem rule29396 (p2027 p2241 p3189 p3256 p3540 p3644 p5118 p5193 p5558 : Prop) (h : (¬ p3644) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p5558) ∨ (¬ p5118) ∨ (¬ p3540) ∨ (¬ p3256) ∨ (¬ p5193) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p5118) ∨ (¬ p5193) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial29396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory18652 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29396 (meaning t m 2027) (meaning t m 2241) (meaning t m 3189) (meaning t m 3256) (meaning t m 3540) (meaning t m 3644) (meaning t m 5118) (meaning t m 5193) (meaning t m 5558) source

theorem rule29398 (p2027 p3516 p3690 p4120 p4204 p4507 p4988 : Prop) (h : p2027 ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4988) ∨ (¬ p4507) ∨ (¬ p4120)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4120) ∨ (¬ p4204) ∨ (¬ p4507) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial29398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory18654 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule29398 (meaning t m 2027) (meaning t m 3516) (meaning t m 3690) (meaning t m 4120) (meaning t m 4204) (meaning t m 4507) (meaning t m 4988) source

theorem rule29404 (p2027 p3434 p3684 p3821 p4279 p4646 p5085 : Prop) (h : (¬ p3821) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p5085) ∨ (¬ p3434) ∨ (¬ p4279) ∨ (¬ p3684)) : (p2027) ∨ (¬ p3434) ∨ (¬ p3684) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4646) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial29404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory18660 t (m.theta 0 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule29404 (meaning t m 2027) (meaning t m 3434) (meaning t m 3684) (meaning t m 3821) (meaning t m 4279) (meaning t m 4646) (meaning t m 5085) source

theorem rule29405 (p2011 p2027 p2611 p2946 p2982 p4117 p4272 p5433 : Prop) (h : (¬ p2946) ∨ (¬ p4117) ∨ p2611 ∨ (¬ p2011) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p4272) ∨ (¬ p5433)) : (¬ p2011) ∨ (p2027) ∨ (p2611) ∨ (¬ p2946) ∨ (¬ p2982) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial29405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory18661 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 10) (m.theta 5 9)
  exact rule29405 (meaning t m 2011) (meaning t m 2027) (meaning t m 2611) (meaning t m 2946) (meaning t m 2982) (meaning t m 4117) (meaning t m 4272) (meaning t m 5433) source

theorem rule29406 (p2027 p2252 p2901 p2963 p2992 p3745 p4558 : Prop) (h : (¬ p4558) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p3745) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2901) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial29406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory18662 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule29406 (meaning t m 2027) (meaning t m 2252) (meaning t m 2901) (meaning t m 2963) (meaning t m 2992) (meaning t m 3745) (meaning t m 4558) source

theorem rule29408 (p2027 p2742 p2901 p2992 p3745 p4195 p4558 : Prop) (h : p2027 ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p2901) ∨ (¬ p2742) ∨ (¬ p4558) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial29408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory18664 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule29408 (meaning t m 2027) (meaning t m 2742) (meaning t m 2901) (meaning t m 2992) (meaning t m 3745) (meaning t m 4195) (meaning t m 4558) source

theorem rule29411 (p2027 p2657 p3516 p3947 p4067 p4104 p4975 : Prop) (h : (¬ p4104) ∨ (¬ p3516) ∨ (¬ p4975) ∨ p2027 ∨ (¬ p4067) ∨ (¬ p2657) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4104) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial29411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory18667 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9)
  exact rule29411 (meaning t m 2027) (meaning t m 2657) (meaning t m 3516) (meaning t m 3947) (meaning t m 4067) (meaning t m 4104) (meaning t m 4975) source

theorem rule29412 (p2027 p2761 p3516 p4066 p4425 p4635 p4653 : Prop) (h : (¬ p3516) ∨ p2027 ∨ (¬ p4653) ∨ (¬ p2761) ∨ (¬ p4066) ∨ (¬ p4635) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4425) ∨ (¬ p4635) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial29412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory18668 t (m.theta 0 7) (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29412 (meaning t m 2027) (meaning t m 2761) (meaning t m 3516) (meaning t m 4066) (meaning t m 4425) (meaning t m 4635) (meaning t m 4653) source

theorem rule29416 (p2027 p2579 p2655 p2946 p3016 p4704 : Prop) (h : (¬ p2946) ∨ (¬ p4704) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p3016) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial29416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory18672 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule29416 (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2946) (meaning t m 3016) (meaning t m 4704) source

theorem rule29417 (p1994 p2027 p2274 p2651 p2765 p2963 p3822 p4328 : Prop) (h : (¬ p3822) ∨ (¬ p4328) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2651) ∨ (¬ p2963) ∨ p2765 ∨ (¬ p2274)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2651) ∨ (p2765) ∨ (¬ p2963) ∨ (¬ p3822) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial29417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory18673 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule29417 (meaning t m 1994) (meaning t m 2027) (meaning t m 2274) (meaning t m 2651) (meaning t m 2765) (meaning t m 2963) (meaning t m 3822) (meaning t m 4328) source

theorem rule29418 (p3868 p4106 p4253 : Prop) (h : (¬ p4253) ∨ (¬ p4106) ∨ p3868) : (p3868) ∨ (¬ p4106) ∨ (¬ p4253) := by
  classical
  tauto

theorem initial29418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3868) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4253)) := by
  have source := ElevenTheory.theory18674 (m.theta 2 7) (m.theta 4 7) (m.theta 7 10)
  exact rule29418 (meaning t m 3868) (meaning t m 4106) (meaning t m 4253) source

theorem rule29422 (p1992 p2027 p2143 p2766 p3266 p3583 p4032 p4322 : Prop) (h : (¬ p4032) ∨ (¬ p1992) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p2143) ∨ p2766 ∨ (¬ p3266)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3583) ∨ (¬ p4032) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial29422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory18678 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29422 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2766) (meaning t m 3266) (meaning t m 3583) (meaning t m 4032) (meaning t m 4322) source

theorem rule29426 (p2504 p2505 p3584 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p2504) ∨ (¬ p3584) ∨ (¬ p2505)) : (¬ p2504) ∨ (¬ p2505) ∨ (¬ p3584) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial29426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory18682 (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6)
  exact rule29426 (meaning t m 2504) (meaning t m 2505) (meaning t m 3584) (meaning t m 3590) source

theorem rule29430 (p2027 p2177 p2254 p2952 p3093 p3146 p3309 p3661 p4118 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p2952) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p2177) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3309) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial29430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory18686 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29430 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2952) (meaning t m 3093) (meaning t m 3146) (meaning t m 3309) (meaning t m 3661) (meaning t m 4118) (meaning t m 4905) source

theorem rule29435 (p2027 p3537 p3688 p3989 p4326 p4342 p4718 : Prop) (h : (¬ p4718) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p3688) ∨ (¬ p4326) ∨ (¬ p4342) ∨ (¬ p3989)) : (p2027) ∨ (¬ p3537) ∨ (¬ p3688) ∨ (¬ p3989) ∨ (¬ p4326) ∨ (¬ p4342) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial29435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory18691 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule29435 (meaning t m 2027) (meaning t m 3537) (meaning t m 3688) (meaning t m 3989) (meaning t m 4326) (meaning t m 4342) (meaning t m 4718) source

theorem rule29438 (p2138 p2780 p3985 : Prop) (h : (¬ p2780) ∨ (¬ p3985) ∨ p2138) : (p2138) ∨ (¬ p2780) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial29438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2138) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory18694 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule29438 (meaning t m 2138) (meaning t m 2780) (meaning t m 3985) source

theorem rule29439 (p1985 p2027 p2241 p2264 p2699 p3027 p3570 : Prop) (h : (¬ p3027) ∨ p2699 ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3570) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial29439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory18695 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule29439 (meaning t m 1985) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2699) (meaning t m 3027) (meaning t m 3570) source

theorem rule29441 (p1992 p2027 p2202 p2440 p2499 p2668 p3019 p3956 p4257 : Prop) (h : (¬ p2440) ∨ p2202 ∨ (¬ p2668) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2499) ∨ (¬ p3019) ∨ (¬ p4257) ∨ (¬ p3956)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2499) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3956) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial29441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory18697 t (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule29441 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2499) (meaning t m 2668) (meaning t m 3019) (meaning t m 3956) (meaning t m 4257) source

theorem rule29442 (p2027 p2657 p2685 p2761 p3516 p4066 p4256 p4286 p4787 p5123 : Prop) (h : (¬ p4066) ∨ (¬ p2685) ∨ (¬ p4787) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2657) ∨ (¬ p4256) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2685) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4787) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial29442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory18698 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule29442 (meaning t m 2027) (meaning t m 2657) (meaning t m 2685) (meaning t m 2761) (meaning t m 3516) (meaning t m 4066) (meaning t m 4256) (meaning t m 4286) (meaning t m 4787) (meaning t m 5123) source

theorem rule29443 (p2027 p2241 p2313 p2992 p4107 p4272 p4381 p5021 p5400 : Prop) (h : (¬ p5021) ∨ (¬ p5400) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4107) ∨ (¬ p4272) ∨ (¬ p2313) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2992) ∨ (¬ p4107) ∨ (¬ p4272) ∨ (¬ p4381) ∨ (¬ p5021) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial29443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5021)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory18699 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule29443 (meaning t m 2027) (meaning t m 2241) (meaning t m 2313) (meaning t m 2992) (meaning t m 4107) (meaning t m 4272) (meaning t m 4381) (meaning t m 5021) (meaning t m 5400) source

theorem rule29446 (p2027 p2187 p2573 p3759 p3874 p3958 p4432 : Prop) (h : (¬ p2187) ∨ (¬ p3874) ∨ (¬ p3759) ∨ (¬ p4432) ∨ (¬ p2573) ∨ (¬ p3958) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p2573) ∨ (¬ p3759) ∨ (¬ p3874) ∨ (¬ p3958) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial29446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory18702 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule29446 (meaning t m 2027) (meaning t m 2187) (meaning t m 2573) (meaning t m 3759) (meaning t m 3874) (meaning t m 3958) (meaning t m 4432) source

theorem rule29447 (p1976 p2027 p2542 p2545 p2707 p3425 p3583 p3698 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2542) ∨ (¬ p1976) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3425)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3583) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial29447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory18703 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5)
  exact rule29447 (meaning t m 1976) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2707) (meaning t m 3425) (meaning t m 3583) (meaning t m 3698) source

theorem rule29448 (p2027 p2247 p2363 p2383 p4111 p4256 p4348 p4438 p5017 : Prop) (h : (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p2363) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p2383) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial29448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory18704 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29448 (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2383) (meaning t m 4111) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) (meaning t m 5017) source

theorem rule29451 (p2027 p2187 p2476 p2573 p3958 p4432 : Prop) (h : p2027 ∨ (¬ p2476) ∨ (¬ p3958) ∨ (¬ p2187) ∨ (¬ p4432) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3958) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial29451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory18707 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule29451 (meaning t m 2027) (meaning t m 2187) (meaning t m 2476) (meaning t m 2573) (meaning t m 3958) (meaning t m 4432) source

theorem rule29452 (p2027 p2252 p2750 p3292 p3399 p3461 p3631 p3954 p4625 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p3292) ∨ (¬ p3631) ∨ (¬ p2252) ∨ (¬ p3954) ∨ (¬ p3461) ∨ (¬ p2750) ∨ (¬ p4625) ∨ (¬ p3399) ∨ p2027) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4625) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18708 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29452 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 3292) (meaning t m 3399) (meaning t m 3461) (meaning t m 3631) (meaning t m 3954) (meaning t m 4625) (meaning t m 5284) source

theorem rule29453 (p2192 p2860 p4243 : Prop) (h : (¬ p2860) ∨ (¬ p4243) ∨ p2192) : (p2192) ∨ (¬ p2860) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial29453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory18709 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule29453 (meaning t m 2192) (meaning t m 2860) (meaning t m 4243) source

theorem rule29456 (p1982 p2027 p2470 p2528 p2579 p2588 p2997 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2528) ∨ p2997 ∨ (¬ p2579) ∨ (¬ p2470)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) := by
  classical
  tauto

theorem initial29456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) := by
  have source := ElevenTheory.theory18712 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 8 9)
  exact rule29456 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) source

theorem rule29457 (p2027 p2470 p2663 p2952 p3573 p3574 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p3574) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p3573)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3573) ∨ (¬ p3574) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial29457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory18713 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 8)
  exact rule29457 (meaning t m 2027) (meaning t m 2470) (meaning t m 2663) (meaning t m 2952) (meaning t m 3573) (meaning t m 3574) (meaning t m 4701) source

theorem rule29466 (p2027 p2427 p3744 p4110 p4140 p4620 : Prop) (h : (¬ p4620) ∨ (¬ p4140) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial29466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory18722 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule29466 (meaning t m 2027) (meaning t m 2427) (meaning t m 3744) (meaning t m 4110) (meaning t m 4140) (meaning t m 4620) source

theorem rule29468 (p1975 p2027 p2192 p2409 p2553 p3125 p3948 p4137 : Prop) (h : p2409 ∨ (¬ p3948) ∨ (¬ p4137) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2553) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (p2409) ∨ (¬ p2553) ∨ (¬ p3125) ∨ (¬ p3948) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial29468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory18724 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule29468 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2409) (meaning t m 2553) (meaning t m 3125) (meaning t m 3948) (meaning t m 4137) source

theorem rule29469 (p2220 p3051 p4119 : Prop) (h : (¬ p4119) ∨ (¬ p2220) ∨ p3051) : (¬ p2220) ∨ (p3051) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial29469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (meaning t m 3051) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory18725 (m.theta 0 5) (m.theta 5 7) (m.theta 5 8)
  exact rule29469 (meaning t m 2220) (meaning t m 3051) (meaning t m 4119) source

theorem rule29471 (p2010 p2027 p2545 p3019 p3201 p3323 p3584 p4137 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3323) ∨ (¬ p4137) ∨ (¬ p3019) ∨ (¬ p2010)) : (¬ p2010) ∨ (p2027) ∨ (p2545) ∨ (¬ p3019) ∨ (¬ p3201) ∨ (¬ p3323) ∨ (¬ p3584) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial29471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory18727 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule29471 (meaning t m 2010) (meaning t m 2027) (meaning t m 2545) (meaning t m 3019) (meaning t m 3201) (meaning t m 3323) (meaning t m 3584) (meaning t m 4137) source

theorem rule29472 (p2027 p2274 p2311 p3527 p3551 p4427 p4486 : Prop) (h : (¬ p4486) ∨ (¬ p2311) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2274) ∨ (¬ p3527) ∨ (¬ p4427)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2311) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4427) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial29472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory18728 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule29472 (meaning t m 2027) (meaning t m 2274) (meaning t m 2311) (meaning t m 3527) (meaning t m 3551) (meaning t m 4427) (meaning t m 4486) source

theorem rule29476 (p2839 p3537 p4744 : Prop) (h : (¬ p2839) ∨ (¬ p4744) ∨ p3537) : (¬ p2839) ∨ (p3537) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial29476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (meaning t m 3537) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory18732 (m.theta 1 2) (m.theta 2 5) (m.theta 2 8)
  exact rule29476 (meaning t m 2839) (meaning t m 3537) (meaning t m 4744) source

theorem rule29480 (p1990 p2027 p2246 p2284 p2766 p2946 p4118 p4360 : Prop) (h : (¬ p4118) ∨ (¬ p4360) ∨ (¬ p2246) ∨ (¬ p2946) ∨ p2766 ∨ p2027 ∨ (¬ p2284) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (p2766) ∨ (¬ p2946) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial29480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory18736 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 8 9)
  exact rule29480 (meaning t m 1990) (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2766) (meaning t m 2946) (meaning t m 4118) (meaning t m 4360) source

theorem rule29483 (p2027 p3324 p4228 p4503 p5558 p5584 : Prop) (h : (¬ p4503) ∨ (¬ p4228) ∨ (¬ p5584) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p5558)) : (p2027) ∨ (¬ p3324) ∨ (¬ p4228) ∨ (¬ p4503) ∨ (¬ p5558) ∨ (¬ p5584) := by
  classical
  tauto

theorem initial29483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5558)) ∨ (¬ (meaning t m 5584)) := by
  have source := ElevenTheory.theory18739 t (m.theta 3 6) (m.theta 6 10) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule29483 (meaning t m 2027) (meaning t m 3324) (meaning t m 4228) (meaning t m 4503) (meaning t m 5558) (meaning t m 5584) source

theorem rule29487 (p1981 p2027 p2122 p2313 p2383 p2545 p2810 p4426 : Prop) (h : p2545 ∨ (¬ p2383) ∨ (¬ p1981) ∨ (¬ p2122) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p4426) ∨ (¬ p2313)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial29487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory18743 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 6 7) (m.theta 6 8)
  exact rule29487 (meaning t m 1981) (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2383) (meaning t m 2545) (meaning t m 2810) (meaning t m 4426) source

theorem rule29498 (p2027 p2254 p2284 p2608 p2707 p2717 p2950 p3497 p3646 p4905 : Prop) (h : (¬ p2950) ∨ (¬ p3646) ∨ (¬ p2284) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2950) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial29498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory18754 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule29498 (meaning t m 2027) (meaning t m 2254) (meaning t m 2284) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 2950) (meaning t m 3497) (meaning t m 3646) (meaning t m 4905) source

theorem rule29501 (p2027 p2534 p3256 p3874 p4121 p4750 : Prop) (h : (¬ p2534) ∨ (¬ p3874) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p3256) ∨ (¬ p4121)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3874) ∨ (¬ p4121) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial29501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory18757 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule29501 (meaning t m 2027) (meaning t m 2534) (meaning t m 3256) (meaning t m 3874) (meaning t m 4121) (meaning t m 4750) source

theorem rule29504 (p2027 p2252 p2459 p2750 p2819 p3093 p3414 p3919 p3954 p4024 p4118 p4133 : Prop) (h : (¬ p3093) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2252) ∨ (¬ p3414) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p3919) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4118) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial29504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory18760 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 7) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29504 (meaning t m 2027) (meaning t m 2252) (meaning t m 2459) (meaning t m 2750) (meaning t m 2819) (meaning t m 3093) (meaning t m 3414) (meaning t m 3919) (meaning t m 3954) (meaning t m 4024) (meaning t m 4118) (meaning t m 4133) source

theorem rule29506 (p1979 p2027 p2622 p2630 p2657 p2958 p3051 p4320 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p2630) ∨ p2622 ∨ (¬ p4320) ∨ (¬ p2958) ∨ (¬ p1979) ∨ (¬ p3051)) : (¬ p1979) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial29506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory18762 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule29506 (meaning t m 1979) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2958) (meaning t m 3051) (meaning t m 4320) source

theorem rule29507 (p2982 p3115 p4241 : Prop) (h : (¬ p4241) ∨ (¬ p2982) ∨ p3115) : (¬ p2982) ∨ (p3115) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial29507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (meaning t m 3115) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory18763 (m.theta 3 5) (m.theta 4 5) (m.theta 5 9)
  exact rule29507 (meaning t m 2982) (meaning t m 3115) (meaning t m 4241) source

theorem rule29508 (p2027 p2417 p2598 p3201 p3461 p3834 p4321 p4625 p4733 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p4625) ∨ (¬ p3834) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3461) ∨ (¬ p4733) ∨ (¬ p4321)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3461) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p4625) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18764 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 9) (m.theta 2 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29508 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3461) (meaning t m 3834) (meaning t m 4321) (meaning t m 4625) (meaning t m 4733) source

theorem rule29510 (p2027 p2274 p2313 p2608 p3367 p3641 p3989 p4198 p4524 p4596 : Prop) (h : (¬ p2608) ∨ (¬ p4596) ∨ (¬ p3641) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p4198) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3367) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial29510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory18766 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule29510 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2608) (meaning t m 3367) (meaning t m 3641) (meaning t m 3989) (meaning t m 4198) (meaning t m 4524) (meaning t m 4596) source

theorem rule29513 (p2027 p2138 p2253 p2331 p3189 p3570 p4154 p4244 p4550 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p4550) ∨ (¬ p2331) ∨ (¬ p2253) ∨ (¬ p4154) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4244) ∨ (¬ p4550) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18769 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule29513 (meaning t m 2027) (meaning t m 2138) (meaning t m 2253) (meaning t m 2331) (meaning t m 3189) (meaning t m 3570) (meaning t m 4154) (meaning t m 4244) (meaning t m 4550) (meaning t m 4736) source

theorem rule29516 (p2027 p2553 p2573 p3365 p3791 p4035 p4419 p4826 p5284 : Prop) (h : (¬ p4035) ∨ (¬ p5284) ∨ (¬ p3365) ∨ (¬ p4419) ∨ (¬ p3791) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3791) ∨ (¬ p4035) ∨ (¬ p4419) ∨ (¬ p4826) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18772 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule29516 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 3365) (meaning t m 3791) (meaning t m 4035) (meaning t m 4419) (meaning t m 4826) (meaning t m 5284) source

theorem rule29517 (p2027 p3256 p3692 p4237 p4320 p4904 : Prop) (h : (¬ p3692) ∨ p2027 ∨ (¬ p4904) ∨ (¬ p4237) ∨ (¬ p3256) ∨ (¬ p4320)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial29517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory18773 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule29517 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 4237) (meaning t m 4320) (meaning t m 4904) source

theorem rule29525 (p2470 p2656 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p2656) ∨ (¬ p2470)) : (¬ p2470) ∨ (¬ p2656) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial29525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory18781 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8)
  exact rule29525 (meaning t m 2470) (meaning t m 2656) (meaning t m 4256) source

theorem rule29528 (p2027 p2743 p2774 p2952 p3073 p3361 p3497 p3918 p4134 p4317 p4347 p4737 : Prop) (h : (¬ p4737) ∨ (¬ p2774) ∨ (¬ p3361) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p2743) ∨ (¬ p4347) ∨ (¬ p4134) ∨ (¬ p3918) ∨ (¬ p4317) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3918) ∨ (¬ p4134) ∨ (¬ p4317) ∨ (¬ p4347) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial29528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18784 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule29528 (meaning t m 2027) (meaning t m 2743) (meaning t m 2774) (meaning t m 2952) (meaning t m 3073) (meaning t m 3361) (meaning t m 3497) (meaning t m 3918) (meaning t m 4134) (meaning t m 4317) (meaning t m 4347) (meaning t m 4737) source

theorem rule29531 (p2027 p2132 p2252 p2619 p2657 p2750 p2753 p3146 p3742 p4278 p4669 : Prop) (h : (¬ p2750) ∨ (¬ p2132) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p4669) ∨ (¬ p4278) ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial29531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory18787 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule29531 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2619) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3742) (meaning t m 4278) (meaning t m 4669) source

theorem rule29532 (p2027 p2132 p2252 p2619 p2657 p2750 p2753 p3359 p3969 p4425 p5119 : Prop) (h : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3359) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4425) ∨ (¬ p2657) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p3969)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3359) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial29532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory18788 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29532 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2619) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3359) (meaning t m 3969) (meaning t m 4425) (meaning t m 5119) source

theorem rule29534 (p2027 p2417 p3822 p3920 p4107 p5222 : Prop) (h : (¬ p3822) ∨ p2027 ∨ (¬ p5222) ∨ (¬ p3920) ∨ (¬ p2417) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3822) ∨ (¬ p3920) ∨ (¬ p4107) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial29534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory18790 t (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule29534 (meaning t m 2027) (meaning t m 2417) (meaning t m 3822) (meaning t m 3920) (meaning t m 4107) (meaning t m 5222) source

theorem rule29538 (p1988 p2027 p2633 p3222 p3276 p3379 p3425 p3570 p4129 p4423 p4736 : Prop) (h : (¬ p3570) ∨ (¬ p3276) ∨ (¬ p3425) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p4423) ∨ (¬ p4736) ∨ (¬ p3222) ∨ (¬ p1988) ∨ (¬ p3379) ∨ p2633) : (¬ p1988) ∨ (p2027) ∨ (p2633) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4129) ∨ (¬ p4423) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18794 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule29538 (meaning t m 1988) (meaning t m 2027) (meaning t m 2633) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 3425) (meaning t m 3570) (meaning t m 4129) (meaning t m 4423) (meaning t m 4736) source

theorem rule29539 (p2027 p2138 p3692 p3694 p3707 p3830 p4191 p4330 p4736 : Prop) (h : (¬ p2138) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p3830) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p3707)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18795 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 9) (m.theta 2 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29539 (meaning t m 2027) (meaning t m 2138) (meaning t m 3692) (meaning t m 3694) (meaning t m 3707) (meaning t m 3830) (meaning t m 4191) (meaning t m 4330) (meaning t m 4736) source

theorem rule29540 (p2027 p2952 p3105 p4208 p4313 p4787 : Prop) (h : (¬ p4208) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p4313) ∨ (¬ p2952) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3105) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial29540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory18796 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 9)
  exact rule29540 (meaning t m 2027) (meaning t m 2952) (meaning t m 3105) (meaning t m 4208) (meaning t m 4313) (meaning t m 4787) source

theorem rule29541 (p1997 p2027 p2406 p2928 p2938 p3246 p4278 : Prop) (h : (¬ p2928) ∨ (¬ p4278) ∨ (¬ p1997) ∨ p2938 ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3246)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial29541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18797 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29541 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2928) (meaning t m 2938) (meaning t m 3246) (meaning t m 4278) source

theorem rule29542 (p1975 p2027 p2765 p2870 p3246 p3952 p4107 p4316 : Prop) (h : (¬ p4107) ∨ (¬ p1975) ∨ p2765 ∨ (¬ p4316) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3246)) : (¬ p1975) ∨ (p2027) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial29542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory18798 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule29542 (meaning t m 1975) (meaning t m 2027) (meaning t m 2765) (meaning t m 2870) (meaning t m 3246) (meaning t m 3952) (meaning t m 4107) (meaning t m 4316) source

theorem rule29543 (p2027 p2449 p2870 p4362 p4382 p4385 : Prop) (h : (¬ p4382) ∨ (¬ p2449) ∨ (¬ p4362) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2870) ∨ (¬ p4362) ∨ (¬ p4382) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial29543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory18799 t (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule29543 (meaning t m 2027) (meaning t m 2449) (meaning t m 2870) (meaning t m 4362) (meaning t m 4382) (meaning t m 4385) source

theorem rule29547 (p2027 p2474 p2528 p2641 p2668 p2696 p2742 p3363 p3585 p3857 p4384 p4737 : Prop) (h : (¬ p2742) ∨ (¬ p2696) ∨ (¬ p3857) ∨ (¬ p2641) ∨ (¬ p2528) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3585) ∨ (¬ p2668) ∨ (¬ p4384) ∨ (¬ p2474)) : (p2027) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3857) ∨ (¬ p4384) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial29547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18803 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule29547 (meaning t m 2027) (meaning t m 2474) (meaning t m 2528) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) (meaning t m 3363) (meaning t m 3585) (meaning t m 3857) (meaning t m 4384) (meaning t m 4737) source

theorem rule29548 (p2027 p2417 p3694 p3741 p3821 p4115 p4590 p4882 : Prop) (h : (¬ p4590) ∨ (¬ p3694) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p4115) ∨ (¬ p3741) ∨ (¬ p3821) ∨ (¬ p4882)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3694) ∨ (¬ p3741) ∨ (¬ p3821) ∨ (¬ p4115) ∨ (¬ p4590) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial29548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory18804 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9)
  exact rule29548 (meaning t m 2027) (meaning t m 2417) (meaning t m 3694) (meaning t m 3741) (meaning t m 3821) (meaning t m 4115) (meaning t m 4590) (meaning t m 4882) source

theorem rule29549 (p2027 p2449 p2761 p2807 p3055 p3874 p4286 p4786 p5123 : Prop) (h : (¬ p5123) ∨ (¬ p3874) ∨ (¬ p3055) ∨ (¬ p2761) ∨ (¬ p4786) ∨ (¬ p2449) ∨ (¬ p4286) ∨ p2027 ∨ (¬ p2807)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4786) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial29549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory18805 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule29549 (meaning t m 2027) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3055) (meaning t m 3874) (meaning t m 4286) (meaning t m 4786) (meaning t m 5123) source

theorem rule29550 (p2027 p2230 p2901 p3246 p3588 p3659 p3879 p3954 p4668 p5190 : Prop) (h : (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5190) ∨ (¬ p3659) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3879) ∨ (¬ p2230) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial29550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory18806 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29550 (meaning t m 2027) (meaning t m 2230) (meaning t m 2901) (meaning t m 3246) (meaning t m 3588) (meaning t m 3659) (meaning t m 3879) (meaning t m 3954) (meaning t m 4668) (meaning t m 5190) source

theorem rule29551 (p2001 p2027 p2842 p3537 p3585 p3609 p3692 : Prop) (h : (¬ p2001) ∨ (¬ p3585) ∨ p2842 ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3537) ∨ (¬ p3609)) : (¬ p2001) ∨ (p2027) ∨ (p2842) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3609) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial29551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory18807 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29551 (meaning t m 2001) (meaning t m 2027) (meaning t m 2842) (meaning t m 3537) (meaning t m 3585) (meaning t m 3609) (meaning t m 3692) source

theorem rule29556 (p2005 p2027 p2169 p3016 p3359 p3483 p4264 p4358 p5379 : Prop) (h : (¬ p3359) ∨ p2169 ∨ (¬ p4264) ∨ (¬ p3016) ∨ (¬ p4358) ∨ (¬ p2005) ∨ (¬ p5379) ∨ (¬ p3483) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (p2169) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p4264) ∨ (¬ p4358) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial29556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4264)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory18812 t (m.theta 0 9) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9)
  exact rule29556 (meaning t m 2005) (meaning t m 2027) (meaning t m 2169) (meaning t m 3016) (meaning t m 3359) (meaning t m 3483) (meaning t m 4264) (meaning t m 4358) (meaning t m 5379) source

theorem rule29557 (p2927 p4106 p4424 : Prop) (h : (¬ p4424) ∨ (¬ p4106) ∨ p2927) : (p2927) ∨ (¬ p4106) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial29557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2927) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory18813 (m.theta 1 7) (m.theta 2 7) (m.theta 4 7)
  exact rule29557 (meaning t m 2927) (meaning t m 4106) (meaning t m 4424) source

theorem rule29562 (p1975 p2027 p2274 p2633 p3434 p3553 p3744 p4396 p4777 : Prop) (h : p2027 ∨ (¬ p4396) ∨ (¬ p3744) ∨ (¬ p3434) ∨ p2633 ∨ (¬ p4777) ∨ (¬ p3553) ∨ (¬ p1975) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2633) ∨ (¬ p3434) ∨ (¬ p3553) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial29562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory18818 t (m.theta 2 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule29562 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2633) (meaning t m 3434) (meaning t m 3553) (meaning t m 3744) (meaning t m 4396) (meaning t m 4777) source

theorem rule29566 (p2027 p3365 p3366 p3399 p3553 p3555 p3572 p3631 p4377 p4668 : Prop) (h : (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3572) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4668)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3553) ∨ (¬ p3555) ∨ (¬ p3572) ∨ (¬ p3631) ∨ (¬ p4377) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial29566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory18822 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29566 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3553) (meaning t m 3555) (meaning t m 3572) (meaning t m 3631) (meaning t m 4377) (meaning t m 4668) source

theorem rule29574 (p1977 p2027 p2807 p2996 p3042 p3170 p3256 p3857 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p3256) ∨ p3042 ∨ (¬ p2807) ∨ (¬ p3170) ∨ (¬ p3857)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (p3042) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial29574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory18830 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule29574 (meaning t m 1977) (meaning t m 2027) (meaning t m 2807) (meaning t m 2996) (meaning t m 3042) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) source

theorem rule29579 (p2027 p2248 p2651 p3016 p3888 p3954 p4379 p5250 p5387 : Prop) (h : (¬ p3954) ∨ (¬ p4379) ∨ (¬ p3016) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3888) ∨ (¬ p5250) ∨ (¬ p5387)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3888) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5250) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial29579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5250)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory18835 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 9) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 9 10)
  exact rule29579 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3888) (meaning t m 3954) (meaning t m 4379) (meaning t m 5250) (meaning t m 5387) source

theorem rule29581 (p2027 p2177 p2246 p2307 p2459 p2608 p2744 p3555 p3987 p4363 p5059 : Prop) (h : (¬ p2307) ∨ (¬ p2177) ∨ (¬ p5059) ∨ (¬ p2459) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2246) ∨ (¬ p3987) ∨ (¬ p2744) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2246) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p3987) ∨ (¬ p4363) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial29581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18837 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29581 (meaning t m 2027) (meaning t m 2177) (meaning t m 2246) (meaning t m 2307) (meaning t m 2459) (meaning t m 2608) (meaning t m 2744) (meaning t m 3555) (meaning t m 3987) (meaning t m 4363) (meaning t m 5059) source

theorem rule29583 (p2191 p2533 p4363 : Prop) (h : (¬ p2533) ∨ (¬ p4363) ∨ p2191) : (p2191) ∨ (¬ p2533) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial29583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory18839 (m.theta 1 5) (m.theta 5 8) (m.theta 5 9)
  exact rule29583 (meaning t m 2191) (meaning t m 2533) (meaning t m 4363) source

theorem rule29584 (p2027 p2136 p2264 p2459 p2807 p2860 p3646 p4385 p4786 p5059 : Prop) (h : (¬ p2459) ∨ (¬ p4786) ∨ (¬ p5059) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p3646) ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial29584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18840 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule29584 (meaning t m 2027) (meaning t m 2136) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 2860) (meaning t m 3646) (meaning t m 4385) (meaning t m 4786) (meaning t m 5059) source

theorem rule29585 (p1992 p2027 p2997 p3097 p3105 p3758 p4363 p4874 : Prop) (h : (¬ p1992) ∨ (¬ p3758) ∨ p2997 ∨ (¬ p4363) ∨ (¬ p4874) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p3097)) : (¬ p1992) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p4363) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial29585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory18841 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule29585 (meaning t m 1992) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3105) (meaning t m 3758) (meaning t m 4363) (meaning t m 4874) source

theorem rule29588 (p1982 p2027 p2323 p2331 p3323 p3461 p4444 : Prop) (h : (¬ p3323) ∨ p2323 ∨ (¬ p2331) ∨ (¬ p3461) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial29588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory18844 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29588 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 3323) (meaning t m 3461) (meaning t m 4444) source

theorem rule29590 (p3422 p3574 p4343 : Prop) (h : (¬ p3422) ∨ (¬ p4343) ∨ (¬ p3574)) : (¬ p3422) ∨ (¬ p3574) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial29590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory18846 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule29590 (meaning t m 3422) (meaning t m 3574) (meaning t m 4343) source

theorem rule29593 (p3019 p4111 p4154 : Prop) (h : (¬ p3019) ∨ (¬ p4154) ∨ p4111) : (¬ p3019) ∨ (p4111) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial29593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3019)) ∨ (meaning t m 4111) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory18849 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule29593 (meaning t m 3019) (meaning t m 4111) (meaning t m 4154) source

theorem rule29594 (p1984 p2027 p2881 p2938 p3588 p3659 p3954 : Prop) (h : (¬ p3659) ∨ (¬ p3954) ∨ (¬ p3588) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p1984) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial29594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory18850 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule29594 (meaning t m 1984) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) source

theorem rule29597 (p2922 p3590 p3876 : Prop) (h : (¬ p3590) ∨ (¬ p3876) ∨ (¬ p2922)) : (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial29597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory18853 (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule29597 (meaning t m 2922) (meaning t m 3590) (meaning t m 3876) source

theorem rule29599 (p2005 p2027 p2611 p2651 p2810 p2819 p3956 p4117 p4426 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p4117) ∨ (¬ p2005) ∨ (¬ p4426) ∨ (¬ p3956)) : (¬ p2005) ∨ (p2027) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial29599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory18855 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule29599 (meaning t m 2005) (meaning t m 2027) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 2819) (meaning t m 3956) (meaning t m 4117) (meaning t m 4426) source

theorem rule29600 (p2027 p2779 p2829 p3583 p4110 p4356 p4885 : Prop) (h : (¬ p4356) ∨ (¬ p2779) ∨ (¬ p4885) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial29600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory18856 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6)
  exact rule29600 (meaning t m 2027) (meaning t m 2779) (meaning t m 2829) (meaning t m 3583) (meaning t m 4110) (meaning t m 4356) (meaning t m 4885) source

theorem rule29601 (p2027 p2248 p2780 p2829 p2881 p2901 p2946 p3873 p4242 p4503 p4857 : Prop) (h : (¬ p4857) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p2881) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4242) ∨ (¬ p2780) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4242) ∨ (¬ p4503) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial29601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory18857 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule29601 (meaning t m 2027) (meaning t m 2248) (meaning t m 2780) (meaning t m 2829) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3873) (meaning t m 4242) (meaning t m 4503) (meaning t m 4857) source

theorem rule29603 (p2027 p2248 p2807 p3256 p3688 p3954 p4044 p4348 p4358 p4503 : Prop) (h : (¬ p4044) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p2248) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial29603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory18859 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29603 (meaning t m 2027) (meaning t m 2248) (meaning t m 2807) (meaning t m 3256) (meaning t m 3688) (meaning t m 3954) (meaning t m 4044) (meaning t m 4348) (meaning t m 4358) (meaning t m 4503) source

theorem rule29604 (p2027 p2761 p3434 p3471 p3555 p4173 p4393 p4733 p5254 : Prop) (h : (¬ p3434) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4733) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2761) ∨ (¬ p4393)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4393) ∨ (¬ p4733) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial29604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory18860 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule29604 (meaning t m 2027) (meaning t m 2761) (meaning t m 3434) (meaning t m 3471) (meaning t m 3555) (meaning t m 4173) (meaning t m 4393) (meaning t m 4733) (meaning t m 5254) source

theorem rule29610 (p2027 p2132 p2753 p2870 p2881 p3379 p4366 p4442 p5216 p5559 : Prop) (h : (¬ p2870) ∨ (¬ p2132) ∨ (¬ p2881) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p5559) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4442)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p5216) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial29610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory18866 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule29610 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 3379) (meaning t m 4366) (meaning t m 4442) (meaning t m 5216) (meaning t m 5559) source

theorem rule29611 (p2027 p2210 p2982 p3834 p4388 p4629 : Prop) (h : (¬ p4629) ∨ (¬ p4388) ∨ (¬ p3834) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2982) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial29611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4388)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory18867 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 4 5) (m.theta 5 9)
  exact rule29611 (meaning t m 2027) (meaning t m 2210) (meaning t m 2982) (meaning t m 3834) (meaning t m 4388) (meaning t m 4629) source

theorem rule29612 (p1980 p2027 p2797 p3128 p3461 p4035 p5284 : Prop) (h : (¬ p1980) ∨ (¬ p2797) ∨ p3128 ∨ (¬ p4035) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p5284)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2797) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18868 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule29612 (meaning t m 1980) (meaning t m 2027) (meaning t m 2797) (meaning t m 3128) (meaning t m 3461) (meaning t m 4035) (meaning t m 5284) source

theorem rule29613 (p1990 p2027 p2114 p2132 p2737 p2860 p3365 : Prop) (h : (¬ p2860) ∨ (¬ p1990) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2132)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p2860) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial29613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory18869 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule29613 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2737) (meaning t m 2860) (meaning t m 3365) source

theorem rule29614 (p2027 p2299 p2449 p2685 p2696 p3549 p3591 p4668 p4733 : Prop) (h : (¬ p3549) ∨ (¬ p2299) ∨ (¬ p3591) ∨ (¬ p2685) ∨ (¬ p4733) ∨ (¬ p2696) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18870 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29614 (meaning t m 2027) (meaning t m 2299) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3549) (meaning t m 3591) (meaning t m 4668) (meaning t m 4733) source

theorem rule29615 (p4024 p4514 p4889 : Prop) (h : (¬ p4889) ∨ (¬ p4024) ∨ p4514) : (¬ p4024) ∨ (p4514) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial29615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4024)) ∨ (meaning t m 4514) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory18871 t (m.theta 1 6) (m.theta 2 6) (m.theta 5 6)
  exact rule29615 (meaning t m 4024) (meaning t m 4514) (meaning t m 4889) source

theorem rule29617 (p2027 p2210 p2753 p2774 p2819 p3834 p3979 p4202 p4321 p5119 p5216 : Prop) (h : (¬ p4202) ∨ (¬ p4321) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p5216) ∨ (¬ p2210) ∨ (¬ p2819) ∨ (¬ p2753) ∨ (¬ p5119) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3834) ∨ (¬ p3979) ∨ (¬ p4202) ∨ (¬ p4321) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18873 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 1 9) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29617 (meaning t m 2027) (meaning t m 2210) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3834) (meaning t m 3979) (meaning t m 4202) (meaning t m 4321) (meaning t m 5119) (meaning t m 5216) source

theorem rule29619 (p2027 p2138 p2247 p2744 p3093 p3319 p3366 p3692 p3694 p4330 : Prop) (h : (¬ p4330) ∨ (¬ p2744) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p2247) ∨ (¬ p3692) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial29619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory18875 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule29619 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3692) (meaning t m 3694) (meaning t m 4330) source

theorem rule29620 (p2027 p2449 p2696 p2742 p3027 p3583 p3692 p3694 p3950 p4737 : Prop) (h : (¬ p3950) ∨ (¬ p2449) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial29620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18876 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule29620 (meaning t m 2027) (meaning t m 2449) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3583) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4737) source

theorem rule29625 (p1983 p2027 p2210 p2699 p3246 p3527 p3570 p4431 : Prop) (h : (¬ p2210) ∨ (¬ p1983) ∨ (¬ p3527) ∨ p2699 ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4431) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3246) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial29625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory18881 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29625 (meaning t m 1983) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 3246) (meaning t m 3527) (meaning t m 3570) (meaning t m 4431) source

theorem rule29626 (p2003 p2027 p2202 p2352 p2387 p3422 p3684 : Prop) (h : p2202 ∨ (¬ p2003) ∨ (¬ p3684) ∨ (¬ p2352) ∨ (¬ p3422) ∨ (¬ p2387) ∨ p2027) : (¬ p2003) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial29626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory18882 t (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule29626 (meaning t m 2003) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 2387) (meaning t m 3422) (meaning t m 3684) source

theorem rule29630 (p2027 p2104 p2437 p2651 p3868 p4340 p4444 p4786 p4826 : Prop) (h : (¬ p4786) ∨ (¬ p2651) ∨ (¬ p2437) ∨ (¬ p3868) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p4444) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial29630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory18886 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule29630 (meaning t m 2027) (meaning t m 2104) (meaning t m 2437) (meaning t m 2651) (meaning t m 3868) (meaning t m 4340) (meaning t m 4444) (meaning t m 4786) (meaning t m 4826) source

theorem rule29631 (p1997 p2027 p2499 p2542 p2573 p2622 p3362 p3365 p3487 : Prop) (h : (¬ p2542) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3365) ∨ p2622 ∨ (¬ p2499) ∨ (¬ p3487) ∨ (¬ p2573) ∨ (¬ p3362)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial29631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory18887 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule29631 (meaning t m 1997) (meaning t m 2027) (meaning t m 2499) (meaning t m 2542) (meaning t m 2573) (meaning t m 2622) (meaning t m 3362) (meaning t m 3365) (meaning t m 3487) source

theorem rule29632 (p1977 p2027 p2589 p2662 p2764 p4111 p4322 p4948 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p4948) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4322)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p4111) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial29632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory18888 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule29632 (meaning t m 1977) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2764) (meaning t m 4111) (meaning t m 4322) (meaning t m 4948) source

theorem rule29635 (p1987 p2027 p2462 p2727 p2810 p2996 p3575 p4155 p4278 : Prop) (h : (¬ p2727) ∨ p2462 ∨ (¬ p3575) ∨ (¬ p4155) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2996) ∨ (¬ p1987) ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2996) ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial29635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18891 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule29635 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2727) (meaning t m 2810) (meaning t m 2996) (meaning t m 3575) (meaning t m 4155) (meaning t m 4278) source

theorem rule29638 (p1994 p2027 p2518 p2764 p3193 p4256 p4425 : Prop) (h : (¬ p4425) ∨ (¬ p3193) ∨ p2764 ∨ p2027 ∨ (¬ p4256) ∨ (¬ p1994) ∨ (¬ p2518)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2518) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p4256) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial29638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory18894 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 9 10)
  exact rule29638 (meaning t m 1994) (meaning t m 2027) (meaning t m 2518) (meaning t m 2764) (meaning t m 3193) (meaning t m 4256) (meaning t m 4425) source

theorem rule29642 (p2027 p2122 p2753 p2774 p3227 p3379 p3791 p3834 p4425 p4826 p5216 : Prop) (h : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2753) ∨ (¬ p3834) ∨ (¬ p4826) ∨ (¬ p3379) ∨ (¬ p3227) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p5216) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p3791) ∨ (¬ p3834) ∨ (¬ p4425) ∨ (¬ p4826) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18898 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule29642 (meaning t m 2027) (meaning t m 2122) (meaning t m 2753) (meaning t m 2774) (meaning t m 3227) (meaning t m 3379) (meaning t m 3791) (meaning t m 3834) (meaning t m 4425) (meaning t m 4826) (meaning t m 5216) source

theorem rule29643 (p2027 p2122 p2145 p2531 p2534 p2774 p3791 p4120 p4444 p4826 : Prop) (h : p2027 ∨ (¬ p4826) ∨ (¬ p3791) ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p4444) ∨ (¬ p2531) ∨ (¬ p4120) ∨ (¬ p2145) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2145) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial29643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory18899 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule29643 (meaning t m 2027) (meaning t m 2122) (meaning t m 2145) (meaning t m 2531) (meaning t m 2534) (meaning t m 2774) (meaning t m 3791) (meaning t m 4120) (meaning t m 4444) (meaning t m 4826) source

theorem rule29649 (p1984 p2027 p2245 p2657 p2727 p2997 p3568 p4154 : Prop) (h : (¬ p1984) ∨ (¬ p2657) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2245) ∨ (¬ p4154) ∨ p2997) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial29649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory18905 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule29649 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2997) (meaning t m 3568) (meaning t m 4154) source

theorem rule29652 (p2027 p2247 p2363 p2774 p2819 p3662 p4208 p4733 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p2247) ∨ (¬ p2819) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2363) ∨ (¬ p4208) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4733) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial29652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18908 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule29652 (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 3662) (meaning t m 4208) (meaning t m 4733) (meaning t m 5059) source

theorem rule29654 (p2027 p2248 p2284 p2946 p3125 p3954 p4242 p4330 p4340 : Prop) (h : (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4330) ∨ (¬ p3954) ∨ (¬ p2946) ∨ (¬ p4242) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p4340)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4330) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial29654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory18910 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule29654 (meaning t m 2027) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3125) (meaning t m 3954) (meaning t m 4242) (meaning t m 4330) (meaning t m 4340) source

theorem rule29657 (p2017 p2027 p2114 p2780 p2829 p3471 p4253 : Prop) (h : p2027 ∨ (¬ p2017) ∨ (¬ p3471) ∨ (¬ p4253) ∨ p2114 ∨ (¬ p2780) ∨ (¬ p2829)) : (¬ p2017) ∨ (p2027) ∨ (p2114) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3471) ∨ (¬ p4253) := by
  classical
  tauto

theorem initial29657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4253)) := by
  have source := ElevenTheory.theory18913 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 7 10)
  exact rule29657 (meaning t m 2017) (meaning t m 2027) (meaning t m 2114) (meaning t m 2780) (meaning t m 2829) (meaning t m 3471) (meaning t m 4253) source

theorem rule29658 (p2027 p2417 p3741 p3821 p4244 p4283 p4882 : Prop) (h : (¬ p3821) ∨ (¬ p4882) ∨ (¬ p4283) ∨ (¬ p4244) ∨ (¬ p2417) ∨ (¬ p3741) ∨ p2027) : (p2027) ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p3821) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial29658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory18914 t (m.theta 0 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29658 (meaning t m 2027) (meaning t m 2417) (meaning t m 3741) (meaning t m 3821) (meaning t m 4244) (meaning t m 4283) (meaning t m 4882) source

theorem rule29661 (p1995 p2027 p2202 p2509 p2563 p3083 p3952 p4700 : Prop) (h : (¬ p2563) ∨ (¬ p4700) ∨ (¬ p2509) ∨ (¬ p1995) ∨ p2027 ∨ (¬ p3083) ∨ p2202 ∨ (¬ p3952)) : (¬ p1995) ∨ (p2027) ∨ (p2202) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3083) ∨ (¬ p3952) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial29661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory18917 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule29661 (meaning t m 1995) (meaning t m 2027) (meaning t m 2202) (meaning t m 2509) (meaning t m 2563) (meaning t m 3083) (meaning t m 3952) (meaning t m 4700) source

theorem rule29662 (p2027 p2307 p2396 p2761 p2781 p3055 p3684 p5405 p5433 : Prop) (h : (¬ p2781) ∨ (¬ p5433) ∨ (¬ p5405) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3684) ∨ (¬ p3055) ∨ (¬ p2396) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial29662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory18918 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule29662 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2761) (meaning t m 2781) (meaning t m 3055) (meaning t m 3684) (meaning t m 5405) (meaning t m 5433) source

theorem rule29666 (p1977 p2027 p2542 p2545 p2589 p2655 p3166 p4360 : Prop) (h : p2027 ∨ (¬ p1977) ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2655) ∨ (¬ p2589) ∨ (¬ p4360) ∨ (¬ p3166)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial29666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory18922 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule29666 (meaning t m 1977) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 2655) (meaning t m 3166) (meaning t m 4360) source

theorem rule29667 (p2027 p2132 p2252 p2363 p2750 p2753 p2870 p2881 p3172 p4118 p4503 : Prop) (h : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p4118) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2881) ∨ (¬ p4503) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial29667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory18923 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29667 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2363) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 3172) (meaning t m 4118) (meaning t m 4503) source

theorem rule29668 (p1992 p2027 p2608 p2766 p3266 p3834 p3847 p5284 : Prop) (h : p2766 ∨ (¬ p3834) ∨ (¬ p1992) ∨ (¬ p3847) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p5284) ∨ (¬ p3266)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18924 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29668 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2766) (meaning t m 3266) (meaning t m 3834) (meaning t m 3847) (meaning t m 5284) source

theorem rule29669 (p3847 p4321 p5284 : Prop) (h : (¬ p3847) ∨ (¬ p5284) ∨ p4321) : (¬ p3847) ∨ (p4321) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3847)) ∨ (meaning t m 4321) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18925 (m.theta 1 9) (m.theta 3 9) (m.theta 9 10)
  exact rule29669 (meaning t m 3847) (meaning t m 4321) (meaning t m 5284) source

theorem rule29672 (p2027 p2247 p2528 p2598 p3641 p4037 p4154 p4604 p4733 : Prop) (h : (¬ p3641) ∨ (¬ p4604) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4733) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18928 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule29672 (meaning t m 2027) (meaning t m 2247) (meaning t m 2528) (meaning t m 2598) (meaning t m 3641) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 4733) source

theorem rule29673 (p1982 p2027 p2264 p2459 p2545 p3027 p4111 : Prop) (h : p2545 ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2264)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial29673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory18929 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29673 (meaning t m 1982) (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2545) (meaning t m 3027) (meaning t m 4111) source

theorem rule29674 (p1982 p2027 p2459 p2707 p2842 p2911 p3577 p3585 p4279 : Prop) (h : (¬ p4279) ∨ (¬ p2707) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3577) ∨ (¬ p3585) ∨ p2842 ∨ (¬ p2459) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p3577) ∨ (¬ p3585) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial29674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory18930 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29674 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2707) (meaning t m 2842) (meaning t m 2911) (meaning t m 3577) (meaning t m 3585) (meaning t m 4279) source

theorem rule29676 (p2027 p2274 p2341 p3548 p3575 p3921 p4105 p4514 : Prop) (h : (¬ p3575) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4105) ∨ p2027 ∨ (¬ p3921) ∨ (¬ p2274) ∨ (¬ p4514)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3575) ∨ (¬ p3921) ∨ (¬ p4105) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial29676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory18932 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule29676 (meaning t m 2027) (meaning t m 2274) (meaning t m 2341) (meaning t m 3548) (meaning t m 3575) (meaning t m 3921) (meaning t m 4105) (meaning t m 4514) source

theorem rule29678 (p2027 p2598 p2829 p3425 p3585 p4472 : Prop) (h : p2027 ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p2829) ∨ (¬ p4472) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2829) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p4472) := by
  classical
  tauto

theorem initial29678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4472)) := by
  have source := ElevenTheory.theory18934 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7)
  exact rule29678 (meaning t m 2027) (meaning t m 2598) (meaning t m 2829) (meaning t m 3425) (meaning t m 3585) (meaning t m 4472) source

theorem rule29681 (p1982 p2027 p2518 p2528 p2963 p2997 p3097 p3125 p3379 p4037 p4236 p4736 : Prop) (h : (¬ p2963) ∨ (¬ p4236) ∨ (¬ p2528) ∨ p2997 ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p1982) ∨ (¬ p4037) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4736) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4236) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18937 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule29681 (meaning t m 1982) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2963) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3379) (meaning t m 4037) (meaning t m 4236) (meaning t m 4736) source

theorem rule29684 (p1982 p2027 p2132 p2611 p3146 p3537 p3583 p4188 : Prop) (h : p2027 ∨ (¬ p3537) ∨ (¬ p4188) ∨ (¬ p3146) ∨ (¬ p2132) ∨ p2611 ∨ (¬ p1982) ∨ (¬ p3583)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p3146) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p4188) := by
  classical
  tauto

theorem initial29684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4188)) := by
  have source := ElevenTheory.theory18940 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29684 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 3146) (meaning t m 3537) (meaning t m 3583) (meaning t m 4188) source

theorem rule29685 (p2000 p2027 p2542 p2589 p2766 p3692 p3693 p4256 : Prop) (h : (¬ p3693) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p4256) ∨ (¬ p2000) ∨ p2766 ∨ (¬ p2542)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3693) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial29685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory18941 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29685 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2766) (meaning t m 3692) (meaning t m 3693) (meaning t m 4256) source

theorem rule29686 (p4031 p4032 p4948 : Prop) (h : (¬ p4031) ∨ (¬ p4032) ∨ p4948) : (¬ p4031) ∨ (¬ p4032) ∨ (p4948) := by
  classical
  tauto

theorem initial29686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4032)) ∨ (meaning t m 4948) := by
  have source := ElevenTheory.theory18942 (m.theta 0 5) (m.theta 4 5) (m.theta 5 9)
  exact rule29686 (meaning t m 4031) (meaning t m 4032) (meaning t m 4948) source

theorem rule29688 (p1998 p2027 p2177 p2699 p3399 p3631 p4107 : Prop) (h : (¬ p2177) ∨ p2027 ∨ p2699 ∨ (¬ p1998) ∨ (¬ p4107) ∨ (¬ p3399) ∨ (¬ p3631)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial29688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory18944 t (m.theta 0 1) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29688 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2699) (meaning t m 3399) (meaning t m 3631) (meaning t m 4107) source

theorem rule29696 (p4112 p4156 p4194 : Prop) (h : (¬ p4112) ∨ (¬ p4156) ∨ p4194) : (¬ p4112) ∨ (¬ p4156) ∨ (p4194) := by
  classical
  tauto

theorem initial29696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4156)) ∨ (meaning t m 4194) := by
  have source := ElevenTheory.theory18952 (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule29696 (meaning t m 4112) (meaning t m 4156) (meaning t m 4194) source

theorem rule29699 (p2027 p2241 p2992 p3115 p3425 p3659 p4348 p4450 p4736 : Prop) (h : (¬ p3659) ∨ (¬ p2241) ∨ (¬ p4736) ∨ (¬ p3115) ∨ (¬ p2992) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18955 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule29699 (meaning t m 2027) (meaning t m 2241) (meaning t m 2992) (meaning t m 3115) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4450) (meaning t m 4736) source

theorem rule29704 (p2027 p2138 p2761 p3399 p3631 p3758 p4393 p4736 p5254 : Prop) (h : (¬ p2138) ∨ (¬ p4736) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p5254) ∨ (¬ p2761) ∨ (¬ p3631) ∨ (¬ p4393)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4736) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial29704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory18960 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule29704 (meaning t m 2027) (meaning t m 2138) (meaning t m 2761) (meaning t m 3399) (meaning t m 3631) (meaning t m 3758) (meaning t m 4393) (meaning t m 4736) (meaning t m 5254) source

theorem rule29707 (p1977 p2027 p2589 p2662 p2766 p3692 p3880 p4111 : Prop) (h : p2766 ∨ (¬ p3692) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p3880)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial29707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory18963 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule29707 (meaning t m 1977) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2766) (meaning t m 3692) (meaning t m 3880) (meaning t m 4111) source

theorem rule29710 (p2027 p2255 p2957 p3286 p3556 p3662 p3690 p3707 p3847 p4191 p4621 : Prop) (h : (¬ p4621) ∨ (¬ p3707) ∨ (¬ p3847) ∨ (¬ p3286) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p3286) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p3707) ∨ (¬ p3847) ∨ (¬ p4191) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial29710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory18966 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 3 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29710 (meaning t m 2027) (meaning t m 2255) (meaning t m 2957) (meaning t m 3286) (meaning t m 3556) (meaning t m 3662) (meaning t m 3690) (meaning t m 3707) (meaning t m 3847) (meaning t m 4191) (meaning t m 4621) source

theorem rule29718 (p3516 p4372 p4829 : Prop) (h : (¬ p4372) ∨ (¬ p3516) ∨ (¬ p4829)) : (¬ p3516) ∨ (¬ p4372) ∨ (¬ p4829) := by
  classical
  tauto

theorem initial29718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4372)) ∨ (¬ (meaning t m 4829)) := by
  have source := ElevenTheory.theory18974 (m.theta 0 7) (m.theta 7 10) (m.theta 7 9)
  exact rule29718 (meaning t m 3516) (meaning t m 4372) (meaning t m 4829) source

theorem rule29721 (p1980 p2027 p2406 p2699 p2797 p3364 p3379 p3684 : Prop) (h : p2699 ∨ (¬ p2406) ∨ p2027 ∨ (¬ p1980) ∨ (¬ p2797) ∨ (¬ p3684) ∨ (¬ p3379) ∨ (¬ p3364)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p2797) ∨ (¬ p3364) ∨ (¬ p3379) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial29721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory18977 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5)
  exact rule29721 (meaning t m 1980) (meaning t m 2027) (meaning t m 2406) (meaning t m 2699) (meaning t m 2797) (meaning t m 3364) (meaning t m 3379) (meaning t m 3684) source

theorem rule29722 (p2027 p3238 p3449 p3452 p4610 p4687 : Prop) (h : (¬ p3238) ∨ (¬ p3449) ∨ (¬ p4610) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4687)) : (p2027) ∨ (¬ p3238) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4610) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial29722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory18978 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 8)
  exact rule29722 (meaning t m 2027) (meaning t m 3238) (meaning t m 3449) (meaning t m 3452) (meaning t m 4610) (meaning t m 4687) source

theorem rule29723 (p2027 p2589 p2608 p2737 p3690 p3755 p4235 p4658 p5193 : Prop) (h : (¬ p4658) ∨ (¬ p4235) ∨ (¬ p3755) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p3690) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2737)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p4235) ∨ (¬ p4658) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial29723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory18979 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule29723 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2737) (meaning t m 3690) (meaning t m 3755) (meaning t m 4235) (meaning t m 4658) (meaning t m 5193) source

theorem rule29727 (p1986 p2027 p2598 p2911 p2914 p3425 p3659 : Prop) (h : (¬ p2598) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3659) ∨ p2914 ∨ (¬ p3425) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial29727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory18983 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule29727 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2911) (meaning t m 2914) (meaning t m 3425) (meaning t m 3659) source

theorem rule29734 (p2027 p2579 p2727 p2751 p3016 p3363 p3364 : Prop) (h : (¬ p2751) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3363) ∨ (¬ p3364) ∨ (¬ p2727) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3016) ∨ (¬ p3363) ∨ (¬ p3364) := by
  classical
  tauto

theorem initial29734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3364)) := by
  have source := ElevenTheory.theory18990 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule29734 (meaning t m 2027) (meaning t m 2579) (meaning t m 2727) (meaning t m 2751) (meaning t m 3016) (meaning t m 3363) (meaning t m 3364) source

theorem rule29735 (p1986 p2027 p2493 p2914 p2928 p3888 p4329 p5220 : Prop) (h : (¬ p3888) ∨ (¬ p2928) ∨ (¬ p2493) ∨ (¬ p5220) ∨ p2027 ∨ (¬ p1986) ∨ p2914 ∨ (¬ p4329)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2493) ∨ (p2914) ∨ (¬ p2928) ∨ (¬ p3888) ∨ (¬ p4329) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial29735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory18991 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule29735 (meaning t m 1986) (meaning t m 2027) (meaning t m 2493) (meaning t m 2914) (meaning t m 2928) (meaning t m 3888) (meaning t m 4329) (meaning t m 5220) source

theorem rule29737 (p1977 p2027 p2169 p2440 p3989 p4110 p4111 : Prop) (h : (¬ p1977) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2440) ∨ p2169 ∨ (¬ p3989)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2440) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial29737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory18993 t (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule29737 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2440) (meaning t m 3989) (meaning t m 4110) (meaning t m 4111) source

theorem rule29743 (p2000 p2027 p2169 p2313 p2577 p3872 p3989 p4129 p4260 : Prop) (h : p2027 ∨ (¬ p2000) ∨ (¬ p2313) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p2577) ∨ (¬ p4129) ∨ (¬ p4260) ∨ (¬ p3872)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4129) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial29743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory18999 t (m.theta 0 4) (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule29743 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2577) (meaning t m 3872) (meaning t m 3989) (meaning t m 4129) (meaning t m 4260) source

theorem rule29755 (p2027 p2220 p2245 p2657 p2727 p3146 p4041 p4348 p4360 p4521 : Prop) (h : (¬ p2220) ∨ (¬ p4521) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2727) ∨ (¬ p2245) ∨ (¬ p3146) ∨ (¬ p4348) ∨ (¬ p4041)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3146) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial29755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory19011 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29755 (meaning t m 2027) (meaning t m 2220) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 3146) (meaning t m 4041) (meaning t m 4348) (meaning t m 4360) (meaning t m 4521) source

theorem rule29758 (p1988 p2027 p2307 p2344 p2761 p3097 p3125 p4623 : Prop) (h : (¬ p4623) ∨ p2344 ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3097) ∨ (¬ p1988) ∨ (¬ p3125)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p2761) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial29758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory19014 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29758 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2344) (meaning t m 2761) (meaning t m 3097) (meaning t m 3125) (meaning t m 4623) source

theorem rule29759 (p3744 p3989 p3990 : Prop) (h : (¬ p3990) ∨ (¬ p3744) ∨ p3989) : (¬ p3744) ∨ (p3989) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial29759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3744)) ∨ (meaning t m 3989) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory19015 (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule29759 (meaning t m 3744) (meaning t m 3989) (meaning t m 3990) source

theorem rule29764 (p2027 p2247 p2761 p3051 p3246 p4154 p4521 p5254 p5717 : Prop) (h : (¬ p2761) ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p3246) ∨ (¬ p4154) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5717)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial29764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory19020 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule29764 (meaning t m 2027) (meaning t m 2247) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 4154) (meaning t m 4521) (meaning t m 5254) (meaning t m 5717) source

theorem rule29767 (p2027 p2132 p2241 p2750 p2753 p2870 p3246 p3591 p4026 p4625 : Prop) (h : (¬ p4026) ∨ (¬ p2750) ∨ (¬ p3591) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2241) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial29767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory19023 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule29767 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3591) (meaning t m 4026) (meaning t m 4625) source

theorem rule29768 (p1990 p2027 p2220 p2563 p2688 p2951 p2992 p3880 : Prop) (h : (¬ p2563) ∨ (¬ p2220) ∨ p2027 ∨ p2688 ∨ (¬ p1990) ∨ (¬ p2992) ∨ (¬ p3880) ∨ (¬ p2951)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2563) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial29768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory19024 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule29768 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2563) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) (meaning t m 3880) source

theorem rule29774 (p2027 p2177 p2315 p3556 p3570 p3961 p4238 : Prop) (h : (¬ p2177) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p3570) ∨ (¬ p2315) ∨ (¬ p4238)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3961) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial29774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory19030 t (m.theta 0 5) (m.theta 0 7) (m.theta 0 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule29774 (meaning t m 2027) (meaning t m 2177) (meaning t m 2315) (meaning t m 3556) (meaning t m 3570) (meaning t m 3961) (meaning t m 4238) source

theorem rule29775 (p4110 p4205 p4948 : Prop) (h : (¬ p4205) ∨ (¬ p4110) ∨ p4948) : (¬ p4110) ∨ (¬ p4205) ∨ (p4948) := by
  classical
  tauto

theorem initial29775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4205)) ∨ (meaning t m 4948) := by
  have source := ElevenTheory.theory19031 (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule29775 (meaning t m 4110) (meaning t m 4205) (meaning t m 4948) source

theorem rule29778 (p2982 p4110 p4205 : Prop) (h : (¬ p4205) ∨ (¬ p4110) ∨ (¬ p2982)) : (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4205) := by
  classical
  tauto

theorem initial29778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4205)) := by
  have source := ElevenTheory.theory19034 (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule29778 (meaning t m 2982) (meaning t m 4110) (meaning t m 4205) source

theorem rule29783 (p1987 p2027 p2313 p2667 p2764 p4107 p4195 p4381 : Prop) (h : (¬ p1987) ∨ p2764 ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2667) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p2313)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4195) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial29783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory19039 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule29783 (meaning t m 1987) (meaning t m 2027) (meaning t m 2313) (meaning t m 2667) (meaning t m 2764) (meaning t m 4107) (meaning t m 4195) (meaning t m 4381) source

theorem rule29785 (p3645 p3880 p4120 p4210 : Prop) (h : (¬ p3645) ∨ (¬ p4210) ∨ (¬ p4120) ∨ p3880) : (¬ p3645) ∨ (p3880) ∨ (¬ p4120) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial29785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3645)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory19041 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule29785 (meaning t m 3645) (meaning t m 3880) (meaning t m 4120) (meaning t m 4210) source

theorem rule29788 (p2027 p2177 p2274 p2311 p2386 p3551 p3958 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p2311) ∨ (¬ p3551) ∨ (¬ p2274) ∨ (¬ p2386) ∨ (¬ p3958)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial29788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory19044 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule29788 (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2311) (meaning t m 2386) (meaning t m 3551) (meaning t m 3958) source

theorem rule29795 (p1998 p2027 p2765 p3146 p3156 p3952 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3952) ∨ p2765 ∨ (¬ p3146) ∨ (¬ p3156)) : (¬ p1998) ∨ (p2027) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial29795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory19051 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29795 (meaning t m 1998) (meaning t m 2027) (meaning t m 2765) (meaning t m 3146) (meaning t m 3156) (meaning t m 3952) (meaning t m 4348) source

theorem rule29798 (p3246 p3516 p3575 p4001 : Prop) (h : (¬ p4001) ∨ (¬ p3516) ∨ (¬ p3575) ∨ p3246) : (p3246) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial29798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3246) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory19054 (m.theta 0 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29798 (meaning t m 3246) (meaning t m 3516) (meaning t m 3575) (meaning t m 4001) source

theorem rule29800 (p3097 p3549 p3957 : Prop) (h : (¬ p3097) ∨ (¬ p3957) ∨ p3549) : (¬ p3097) ∨ (p3549) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial29800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (meaning t m 3549) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory19056 (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule29800 (meaning t m 3097) (meaning t m 3549) (meaning t m 3957) source

theorem rule29802 (p2027 p2417 p2651 p3201 p3297 p3680 p3773 p3951 p4035 p4343 p4790 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4790) ∨ (¬ p4343) ∨ (¬ p3951) ∨ (¬ p3773) ∨ (¬ p3297) ∨ (¬ p3680) ∨ (¬ p4035) ∨ (¬ p3201) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p3201) ∨ (¬ p3297) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3951) ∨ (¬ p4035) ∨ (¬ p4343) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial29802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory19058 t (m.theta 0 3) (m.theta 0 9) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29802 (meaning t m 2027) (meaning t m 2417) (meaning t m 2651) (meaning t m 3201) (meaning t m 3297) (meaning t m 3680) (meaning t m 3773) (meaning t m 3951) (meaning t m 4035) (meaning t m 4343) (meaning t m 4790) source

theorem rule29807 (p2027 p2441 p3051 p3246 p4278 p4539 : Prop) (h : p2027 ∨ (¬ p4539) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p4278) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial29807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory19063 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29807 (meaning t m 2027) (meaning t m 2441) (meaning t m 3051) (meaning t m 3246) (meaning t m 4278) (meaning t m 4539) source

theorem rule29808 (p2027 p2441 p2449 p3051 p3699 p4278 p4539 : Prop) (h : (¬ p2449) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4539) ∨ (¬ p4278) ∨ (¬ p2441) ∨ (¬ p3699)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3051) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial29808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory19064 t (m.theta 0 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29808 (meaning t m 2027) (meaning t m 2441) (meaning t m 2449) (meaning t m 3051) (meaning t m 3699) (meaning t m 4278) (meaning t m 4539) source

theorem rule29817 (p2027 p2946 p3170 p3256 p3857 p5062 : Prop) (h : (¬ p5062) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p3170)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p5062) := by
  classical
  tauto

theorem initial29817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 5062)) := by
  have source := ElevenTheory.theory19073 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule29817 (meaning t m 2027) (meaning t m 2946) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) (meaning t m 5062) source

theorem rule29818 (p1987 p2027 p2696 p2766 p2780 p4347 p4358 : Prop) (h : (¬ p1987) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p2780) ∨ (¬ p2696) ∨ p2766) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial29818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory19074 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule29818 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2766) (meaning t m 2780) (meaning t m 4347) (meaning t m 4358) source

theorem rule29819 (p3212 p4109 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4109) ∨ (¬ p3212)) : (¬ p3212) ∨ (¬ p4109) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial29819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory19075 (m.theta 0 5) (m.theta 4 5) (m.theta 5 9)
  exact rule29819 (meaning t m 3212) (meaning t m 4109) (meaning t m 4948) source

theorem rule29821 (p2027 p2156 p3588 p3680 p3954 p4106 p4191 p4278 p4334 p4521 p4621 : Prop) (h : (¬ p3588) ∨ (¬ p4191) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4106) ∨ (¬ p2156) ∨ (¬ p4334) ∨ (¬ p4521) ∨ (¬ p3680) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3588) ∨ (¬ p3680) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4334) ∨ (¬ p4521) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial29821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory19077 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29821 (meaning t m 2027) (meaning t m 2156) (meaning t m 3588) (meaning t m 3680) (meaning t m 3954) (meaning t m 4106) (meaning t m 4191) (meaning t m 4278) (meaning t m 4334) (meaning t m 4521) (meaning t m 4621) source

theorem rule29824 (p2027 p2396 p2589 p3093 p3309 p3692 p3880 p3905 p3950 p4736 : Prop) (h : (¬ p2589) ∨ (¬ p3093) ∨ (¬ p2396) ∨ (¬ p4736) ∨ (¬ p3905) ∨ (¬ p3880) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3905) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial29824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory19080 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule29824 (meaning t m 2027) (meaning t m 2396) (meaning t m 2589) (meaning t m 3093) (meaning t m 3309) (meaning t m 3692) (meaning t m 3880) (meaning t m 3905) (meaning t m 3950) (meaning t m 4736) source

theorem rule29827 (p2027 p2192 p2210 p2254 p2534 p2657 p3125 p4256 p4330 : Prop) (h : (¬ p2534) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2254) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4330) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3125) ∨ (¬ p4256) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial29827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory19083 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule29827 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2534) (meaning t m 2657) (meaning t m 3125) (meaning t m 4256) (meaning t m 4330) source

theorem rule29829 (p1975 p2027 p2202 p2274 p2440 p3343 p3744 p4331 : Prop) (h : (¬ p3744) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p4331) ∨ p2202 ∨ (¬ p3343)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial29829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory19085 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule29829 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2274) (meaning t m 2440) (meaning t m 3343) (meaning t m 3744) (meaning t m 4331) source

theorem rule29830 (p4636 p4669 p4697 : Prop) (h : (¬ p4636) ∨ (¬ p4669) ∨ p4697) : (¬ p4636) ∨ (¬ p4669) ∨ (p4697) := by
  classical
  tauto

theorem initial29830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4669)) ∨ (meaning t m 4697) := by
  have source := ElevenTheory.theory19086 t (m.theta 4 9) (m.theta 7 9) (m.theta 8 9)
  exact rule29830 (meaning t m 4636) (meaning t m 4669) (meaning t m 4697) source

theorem rule29832 (p1998 p2027 p2177 p2202 p2563 p2891 p4140 p4173 : Prop) (h : (¬ p4173) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p4140) ∨ (¬ p2891)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p4140) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial29832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory19088 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule29832 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2563) (meaning t m 2891) (meaning t m 4140) (meaning t m 4173) source

theorem rule29833 (p2027 p2573 p3201 p3540 p3684 p4717 : Prop) (h : (¬ p2573) ∨ (¬ p3684) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial29833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory19089 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule29833 (meaning t m 2027) (meaning t m 2573) (meaning t m 3201) (meaning t m 3540) (meaning t m 3684) (meaning t m 4717) source

theorem rule29835 (p2027 p2122 p2737 p3097 p4173 p4842 p4874 : Prop) (h : (¬ p2122) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p4842) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2737) ∨ (¬ p3097) ∨ (¬ p4173) ∨ (¬ p4842) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial29835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4842)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory19091 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule29835 (meaning t m 2027) (meaning t m 2122) (meaning t m 2737) (meaning t m 3097) (meaning t m 4173) (meaning t m 4842) (meaning t m 4874) source

theorem rule29841 (p2797 p3005 p4196 : Prop) (h : (¬ p3005) ∨ (¬ p4196) ∨ p2797) : (p2797) ∨ (¬ p3005) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial29841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2797) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory19097 (m.theta 2 3) (m.theta 3 6) (m.theta 3 8)
  exact rule29841 (meaning t m 2797) (meaning t m 3005) (meaning t m 4196) source

theorem rule29848 (p1990 p2027 p2192 p2299 p2396 p2633 p3554 p3817 : Prop) (h : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2192) ∨ (¬ p1990) ∨ (¬ p3554) ∨ p2633 ∨ p2027 ∨ (¬ p3817)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3554) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial29848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory19104 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29848 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3554) (meaning t m 3817) source

theorem rule29853 (p1998 p2027 p2363 p2373 p2542 p2545 p4348 p4441 : Prop) (h : (¬ p4348) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p4441) ∨ (¬ p1998) ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2373)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p4348) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial29853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory19109 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29853 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2373) (meaning t m 2542) (meaning t m 2545) (meaning t m 4348) (meaning t m 4441) source

theorem rule29855 (p2027 p2138 p2470 p2528 p3367 p3744 p3759 p4173 p4243 p4604 p4734 : Prop) (h : (¬ p3759) ∨ (¬ p3367) ∨ (¬ p4243) ∨ (¬ p2470) ∨ (¬ p4604) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p4734) ∨ (¬ p2138) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3744) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4604) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial29855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19111 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule29855 (meaning t m 2027) (meaning t m 2138) (meaning t m 2470) (meaning t m 2528) (meaning t m 3367) (meaning t m 3744) (meaning t m 3759) (meaning t m 4173) (meaning t m 4243) (meaning t m 4604) (meaning t m 4734) source

theorem rule29857 (p2839 p4242 p4744 : Prop) (h : (¬ p2839) ∨ (¬ p4744) ∨ (¬ p4242)) : (¬ p2839) ∨ (¬ p4242) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial29857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory19113 (m.theta 1 2) (m.theta 2 5) (m.theta 2 8)
  exact rule29857 (meaning t m 2839) (meaning t m 4242) (meaning t m 4744) source

theorem rule29858 (p2027 p2102 p3537 p3609 p3857 p4734 : Prop) (h : p2027 ∨ (¬ p3537) ∨ (¬ p2102) ∨ (¬ p4734) ∨ (¬ p3609) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2102) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial29858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2102)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19114 t (m.theta 0 2) (m.theta 0 8) (m.theta 1 2) (m.theta 2 8) (m.theta 8 9)
  exact rule29858 (meaning t m 2027) (meaning t m 2102) (meaning t m 3537) (meaning t m 3609) (meaning t m 3857) (meaning t m 4734) source

theorem rule29861 (p2829 p2839 p3985 : Prop) (h : (¬ p3985) ∨ (¬ p2839) ∨ p2829) : (p2829) ∨ (¬ p2839) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial29861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2829) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory19117 (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule29861 (meaning t m 2829) (meaning t m 2839) (meaning t m 3985) source

theorem rule29862 (p2027 p2319 p2341 p3644 p3946 p4620 p4710 : Prop) (h : (¬ p2319) ∨ (¬ p4710) ∨ (¬ p2341) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3946) ∨ (¬ p4620)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3946) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial29862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory19118 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule29862 (meaning t m 2027) (meaning t m 2319) (meaning t m 2341) (meaning t m 3644) (meaning t m 3946) (meaning t m 4620) (meaning t m 4710) source

theorem rule29864 (p2020 p2027 p2528 p2545 p3083 p3941 p4348 : Prop) (h : p2027 ∨ (¬ p2020) ∨ (¬ p3083) ∨ p2545 ∨ (¬ p2528) ∨ (¬ p3941) ∨ (¬ p4348)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2528) ∨ (p2545) ∨ (¬ p3083) ∨ (¬ p3941) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial29864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory19120 t (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29864 (meaning t m 2020) (meaning t m 2027) (meaning t m 2528) (meaning t m 2545) (meaning t m 3083) (meaning t m 3941) (meaning t m 4348) source

theorem rule29865 (p2027 p2441 p2563 p3246 p3658 p4324 p4555 : Prop) (h : (¬ p3658) ∨ (¬ p2563) ∨ (¬ p4555) ∨ (¬ p2441) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p3246) ∨ (¬ p3658) ∨ (¬ p4324) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial29865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory19121 t (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule29865 (meaning t m 2027) (meaning t m 2441) (meaning t m 2563) (meaning t m 3246) (meaning t m 3658) (meaning t m 4324) (meaning t m 4555) source

theorem rule29866 (p2819 p3989 p4428 : Prop) (h : (¬ p3989) ∨ (¬ p4428) ∨ (¬ p2819)) : (¬ p2819) ∨ (¬ p3989) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial29866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory19122 (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule29866 (meaning t m 2819) (meaning t m 3989) (meaning t m 4428) source

theorem rule29867 (p2027 p2696 p2972 p3425 p3590 p3680 p3948 p4191 p4324 p4621 p4749 : Prop) (h : p2027 ∨ (¬ p2972) ∨ (¬ p4749) ∨ (¬ p2696) ∨ (¬ p3590) ∨ (¬ p4621) ∨ (¬ p4324) ∨ (¬ p3948) ∨ (¬ p3425) ∨ (¬ p3680) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2972) ∨ (¬ p3425) ∨ (¬ p3590) ∨ (¬ p3680) ∨ (¬ p3948) ∨ (¬ p4191) ∨ (¬ p4324) ∨ (¬ p4621) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial29867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory19123 t (m.theta 0 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29867 (meaning t m 2027) (meaning t m 2696) (meaning t m 2972) (meaning t m 3425) (meaning t m 3590) (meaning t m 3680) (meaning t m 3948) (meaning t m 4191) (meaning t m 4324) (meaning t m 4621) (meaning t m 4749) source

end SunPrize.SMT
