import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory048
import SunPrize.Certificate.Theory049
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule27760 (p1977 p2027 p2462 p2651 p3414 p3947 p4111 : Prop) (h : (¬ p1977) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3947) ∨ p2462 ∨ (¬ p3414)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial27760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory17016 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule27760 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2651) (meaning t m 3414) (meaning t m 3947) (meaning t m 4111) source

theorem rule27761 (p1977 p2027 p2579 p2662 p2766 p3956 p4111 p4347 : Prop) (h : p2766 ∨ (¬ p4347) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p1977) ∨ (¬ p2579) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial27761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory17017 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule27761 (meaning t m 1977) (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2766) (meaning t m 3956) (meaning t m 4111) (meaning t m 4347) source

theorem rule27767 (p1984 p2027 p2202 p2247 p2440 p2518 p2528 p3324 p4116 p4154 p4348 p4503 : Prop) (h : (¬ p2247) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4154) ∨ p2202 ∨ (¬ p4116) ∨ (¬ p2518) ∨ (¬ p2440) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2247) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17023 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27767 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2247) (meaning t m 2440) (meaning t m 2518) (meaning t m 2528) (meaning t m 3324) (meaning t m 4116) (meaning t m 4154) (meaning t m 4348) (meaning t m 4503) source

theorem rule27770 (p2027 p2248 p2331 p3005 p3238 p3452 p3880 p4195 p5063 : Prop) (h : (¬ p3005) ∨ (¬ p3452) ∨ (¬ p2248) ∨ (¬ p3238) ∨ (¬ p5063) ∨ (¬ p3880) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4195)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4195) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial27770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory17026 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule27770 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3005) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 4195) (meaning t m 5063) source

theorem rule27771 (p2027 p2284 p2992 p2996 p3699 p4555 : Prop) (h : (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial27771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory17027 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule27771 (meaning t m 2027) (meaning t m 2284) (meaning t m 2992) (meaning t m 2996) (meaning t m 3699) (meaning t m 4555) source

theorem rule27772 (p4503 p4506 p4905 : Prop) (h : (¬ p4503) ∨ (¬ p4506) ∨ p4905) : (¬ p4503) ∨ (¬ p4506) ∨ (p4905) := by
  classical
  tauto

theorem initial27772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4506)) ∨ (meaning t m 4905) := by
  have source := ElevenTheory.theory17028 t (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule27772 (meaning t m 4503) (meaning t m 4506) (meaning t m 4905) source

theorem rule27774 (p2027 p2363 p2774 p2819 p2928 p3452 p4278 p4669 p4733 : Prop) (h : (¬ p2928) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p3452) ∨ (¬ p2819) ∨ (¬ p4733) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial27774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17030 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27774 (meaning t m 2027) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4669) (meaning t m 4733) source

theorem rule27778 (p1984 p2027 p2363 p2641 p2668 p2688 p3238 p3452 p3880 p4348 p4905 : Prop) (h : (¬ p1984) ∨ (¬ p4905) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p3238) ∨ (¬ p3452) ∨ p2027 ∨ p2688 ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p2363)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (p2688) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial27778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory17034 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27778 (meaning t m 1984) (meaning t m 2027) (meaning t m 2363) (meaning t m 2641) (meaning t m 2668) (meaning t m 2688) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 4348) (meaning t m 4905) source

theorem rule27783 (p2027 p2717 p2737 p3551 p3820 p4734 p4781 : Prop) (h : (¬ p4734) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3820) ∨ (¬ p3551) ∨ (¬ p2717) ∨ (¬ p4781)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial27783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory17039 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule27783 (meaning t m 2027) (meaning t m 2717) (meaning t m 2737) (meaning t m 3551) (meaning t m 3820) (meaning t m 4734) (meaning t m 4781) source

theorem rule27786 (p2027 p2449 p2881 p3551 p4107 p4155 p4559 : Prop) (h : (¬ p3551) ∨ (¬ p4155) ∨ (¬ p2449) ∨ (¬ p2881) ∨ (¬ p4559) ∨ p2027 ∨ (¬ p4107)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4155) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial27786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory17042 t (m.theta 0 7) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27786 (meaning t m 2027) (meaning t m 2449) (meaning t m 2881) (meaning t m 3551) (meaning t m 4107) (meaning t m 4155) (meaning t m 4559) source

theorem rule27787 (p1984 p2027 p2191 p2972 p3369 p3982 p4032 p5568 : Prop) (h : (¬ p1984) ∨ (¬ p3369) ∨ (¬ p5568) ∨ p2027 ∨ p3982 ∨ (¬ p2972) ∨ (¬ p4032) ∨ (¬ p2191)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2972) ∨ (¬ p3369) ∨ (p3982) ∨ (¬ p4032) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial27787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3369)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory17043 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10)
  exact rule27787 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2972) (meaning t m 3369) (meaning t m 3982) (meaning t m 4032) (meaning t m 5568) source

theorem rule27789 (p1976 p2027 p2737 p3008 p3365 p3574 p3585 p4343 : Prop) (h : (¬ p1976) ∨ (¬ p2737) ∨ (¬ p3365) ∨ p3008 ∨ p2027 ∨ (¬ p4343) ∨ (¬ p3574) ∨ (¬ p3585)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2737) ∨ (p3008) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial27789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory17045 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule27789 (meaning t m 1976) (meaning t m 2027) (meaning t m 2737) (meaning t m 3008) (meaning t m 3365) (meaning t m 3574) (meaning t m 3585) (meaning t m 4343) source

theorem rule27791 (p2027 p2088 p2249 p2499 p2657 p3027 p3171 p3487 p3956 p4044 p4348 p4503 : Prop) (h : (¬ p3027) ∨ (¬ p2088) ∨ (¬ p4044) ∨ (¬ p3171) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p3487) ∨ (¬ p2499) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2249)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3487) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17047 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27791 (meaning t m 2027) (meaning t m 2088) (meaning t m 2249) (meaning t m 2499) (meaning t m 2657) (meaning t m 3027) (meaning t m 3171) (meaning t m 3487) (meaning t m 3956) (meaning t m 4044) (meaning t m 4348) (meaning t m 4503) source

theorem rule27793 (p2027 p2220 p2499 p3146 p3452 p3956 p4348 p4503 p4521 : Prop) (h : (¬ p4521) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2220) ∨ (¬ p3956) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2499) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial27793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory17049 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27793 (meaning t m 2027) (meaning t m 2220) (meaning t m 2499) (meaning t m 3146) (meaning t m 3452) (meaning t m 3956) (meaning t m 4348) (meaning t m 4503) (meaning t m 4521) source

theorem rule27796 (p2027 p2248 p2499 p2807 p3256 p3452 p3956 p4044 p4348 p4503 : Prop) (h : (¬ p3452) ∨ (¬ p2499) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4503) ∨ (¬ p2807) ∨ (¬ p4348) ∨ (¬ p4044) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17052 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27796 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2807) (meaning t m 3256) (meaning t m 3452) (meaning t m 3956) (meaning t m 4044) (meaning t m 4348) (meaning t m 4503) source

theorem rule27803 (p1994 p2027 p2114 p2138 p2630 p2696 p2839 : Prop) (h : (¬ p2630) ∨ (¬ p1994) ∨ (¬ p2138) ∨ p2114 ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2696)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2138) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2839) := by
  classical
  tauto

theorem initial27803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2839)) := by
  have source := ElevenTheory.theory17059 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule27803 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2138) (meaning t m 2630) (meaning t m 2696) (meaning t m 2839) source

theorem rule27805 (p2027 p3276 p3358 p4322 p4355 p4385 p4882 : Prop) (h : (¬ p4355) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3358) ∨ (¬ p3276) ∨ (¬ p4882) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4322) ∨ (¬ p4355) ∨ (¬ p4385) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial27805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory17061 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 8) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule27805 (meaning t m 2027) (meaning t m 3276) (meaning t m 3358) (meaning t m 4322) (meaning t m 4355) (meaning t m 4385) (meaning t m 4882) source

theorem rule27806 (p2027 p2589 p2608 p2707 p2717 p3989 p4110 p4503 p5193 : Prop) (h : (¬ p2717) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2589) ∨ (¬ p4503) ∨ (¬ p4110) ∨ (¬ p2707) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17062 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule27806 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3989) (meaning t m 4110) (meaning t m 4503) (meaning t m 5193) source

theorem rule27809 (p3923 p3957 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p3957) ∨ p3923) : (p3923) ∨ (¬ p3957) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial27809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3923) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory17065 (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule27809 (meaning t m 3923) (meaning t m 3957) (meaning t m 3989) source

theorem rule27814 (p2027 p2241 p2264 p2589 p3027 p3989 p4110 p4503 p5193 : Prop) (h : (¬ p2264) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p2241) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17070 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule27814 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2589) (meaning t m 3027) (meaning t m 3989) (meaning t m 4110) (meaning t m 4503) (meaning t m 5193) source

theorem rule27819 (p3434 p3527 p3945 p4424 : Prop) (h : (¬ p4424) ∨ (¬ p3527) ∨ (¬ p3945) ∨ p3434) : (p3434) ∨ (¬ p3527) ∨ (¬ p3945) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial27819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3434) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory17075 (m.theta 1 7) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27819 (meaning t m 3434) (meaning t m 3527) (meaning t m 3945) (meaning t m 4424) source

theorem rule27822 (p2027 p2528 p4009 p4118 p4434 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p4434) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4009)) : (p2027) ∨ (¬ p2528) ∨ (¬ p4009) ∨ (¬ p4118) ∨ (¬ p4434) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial27822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory17078 t (m.theta 3 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27822 (meaning t m 2027) (meaning t m 2528) (meaning t m 4009) (meaning t m 4118) (meaning t m 4434) (meaning t m 5568) source

theorem rule27824 (p3950 p4171 p4625 : Prop) (h : (¬ p3950) ∨ (¬ p4171) ∨ p4625) : (¬ p3950) ∨ (¬ p4171) ∨ (p4625) := by
  classical
  tauto

theorem initial27824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4171)) ∨ (meaning t m 4625) := by
  have source := ElevenTheory.theory17080 t (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule27824 (meaning t m 3950) (meaning t m 4171) (meaning t m 4625) source

theorem rule27832 (p2027 p2132 p2363 p2476 p2534 p2750 p2753 p2870 p2881 p3347 p3402 p4503 : Prop) (h : p2027 ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2870) ∨ (¬ p4503) ∨ (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p3347) ∨ (¬ p3402)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3347) ∨ (¬ p3402) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17088 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27832 (meaning t m 2027) (meaning t m 2132) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 3347) (meaning t m 3402) (meaning t m 4503) source

theorem rule27836 (p1997 p2027 p2476 p2542 p3389 p3498 p3742 : Prop) (h : p3498 ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p1997) ∨ (¬ p2476) ∨ (¬ p3389)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2542) ∨ (¬ p3389) ∨ (p3498) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial27836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3389)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory17092 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule27836 (meaning t m 1997) (meaning t m 2027) (meaning t m 2476) (meaning t m 2542) (meaning t m 3389) (meaning t m 3498) (meaning t m 3742) source

theorem rule27844 (p2027 p2630 p2655 p2922 p3540 p4116 p4787 : Prop) (h : (¬ p2655) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p4116) ∨ (¬ p2922) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4116) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial27844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory17100 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule27844 (meaning t m 2027) (meaning t m 2630) (meaning t m 2655) (meaning t m 2922) (meaning t m 3540) (meaning t m 4116) (meaning t m 4787) source

theorem rule27845 (p2027 p2630 p3083 p3572 p3879 p4156 p4336 p4610 : Prop) (h : (¬ p4610) ∨ (¬ p3879) ∨ (¬ p4156) ∨ (¬ p4336) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3083) ∨ (¬ p3572) ∨ (¬ p3879) ∨ (¬ p4156) ∨ (¬ p4336) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial27845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory17101 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 8)
  exact rule27845 (meaning t m 2027) (meaning t m 2630) (meaning t m 3083) (meaning t m 3572) (meaning t m 3879) (meaning t m 4156) (meaning t m 4336) (meaning t m 4610) source

theorem rule27850 (p2027 p2166 p2210 p2459 p2534 p3347 p3540 p3954 p4186 p4902 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4902) ∨ (¬ p2210) ∨ (¬ p5216) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial27850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory17106 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27850 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2459) (meaning t m 2534) (meaning t m 3347) (meaning t m 3540) (meaning t m 3954) (meaning t m 4186) (meaning t m 4902) (meaning t m 5216) source

theorem rule27852 (p2027 p2295 p2313 p2946 p3983 p4563 : Prop) (h : (¬ p2313) ∨ (¬ p4563) ∨ (¬ p2295) ∨ (¬ p3983) ∨ (¬ p2946) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3983) ∨ (¬ p4563) := by
  classical
  tauto

theorem initial27852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4563)) := by
  have source := ElevenTheory.theory17108 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule27852 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2946) (meaning t m 3983) (meaning t m 4563) source

theorem rule27861 (p1977 p2027 p2177 p2241 p2997 p3548 p4366 : Prop) (h : (¬ p2177) ∨ p2997 ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p1977) ∨ (¬ p3548)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (p2997) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial27861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory17117 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27861 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2997) (meaning t m 3548) (meaning t m 4366) source

theorem rule27864 (p2027 p2264 p2363 p2696 p2742 p3027 p3688 p4078 p4340 p4503 p4737 : Prop) (h : (¬ p2264) ∨ (¬ p4737) ∨ (¬ p3688) ∨ (¬ p3027) ∨ (¬ p4503) ∨ (¬ p4340) ∨ (¬ p4078) ∨ (¬ p2696) ∨ (¬ p2742) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial27864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory17120 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27864 (meaning t m 2027) (meaning t m 2264) (meaning t m 2363) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3688) (meaning t m 4078) (meaning t m 4340) (meaning t m 4503) (meaning t m 4737) source

theorem rule27871 (p2027 p2598 p2911 p3201 p3555 p3989 p4173 p4503 p4733 : Prop) (h : (¬ p3555) ∨ (¬ p4173) ∨ (¬ p2598) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p4503) ∨ (¬ p3989) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial27871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17127 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule27871 (meaning t m 2027) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) (meaning t m 4503) (meaning t m 4733) source

theorem rule27875 (p2027 p2470 p2528 p3555 p3989 p4173 p4348 p4503 p5190 : Prop) (h : (¬ p3555) ∨ (¬ p5190) ∨ (¬ p2470) ∨ (¬ p4173) ∨ (¬ p2528) ∨ (¬ p4348) ∨ (¬ p3989) ∨ (¬ p4503) ∨ p2027) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial27875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory17131 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27875 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) (meaning t m 4348) (meaning t m 4503) (meaning t m 5190) source

theorem rule27879 (p1982 p2027 p2114 p2657 p2727 p2749 p3166 p3256 : Prop) (h : (¬ p2727) ∨ (¬ p3256) ∨ (¬ p2657) ∨ (¬ p3166) ∨ p2114 ∨ (¬ p2749) ∨ (¬ p1982) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial27879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory17135 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule27879 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) (meaning t m 3166) (meaning t m 3256) source

theorem rule27881 (p2027 p2156 p2850 p3952 p4109 p4700 p4753 : Prop) (h : (¬ p4700) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p2850) ∨ (¬ p3952) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial27881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory17137 t (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule27881 (meaning t m 2027) (meaning t m 2156) (meaning t m 2850) (meaning t m 3952) (meaning t m 4109) (meaning t m 4700) (meaning t m 4753) source

theorem rule27884 (p2027 p2396 p2891 p4363 p4382 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p4363) ∨ (¬ p4382)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial27884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory17140 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule27884 (meaning t m 2027) (meaning t m 2396) (meaning t m 2891) (meaning t m 4363) (meaning t m 4382) (meaning t m 4556) source

theorem rule27887 (p1982 p2027 p2633 p3246 p3570 p3767 p4444 p5295 : Prop) (h : (¬ p3767) ∨ (¬ p5295) ∨ (¬ p3570) ∨ p2633 ∨ (¬ p1982) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3767) ∨ (¬ p4444) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial27887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory17143 t (m.theta 0 9) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule27887 (meaning t m 1982) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3767) (meaning t m 4444) (meaning t m 5295) source

theorem rule27892 (p2007 p2027 p2241 p2534 p2699 p3189 p3256 : Prop) (h : (¬ p2241) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3256) ∨ p2699 ∨ (¬ p2007)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2534) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial27892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory17148 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule27892 (meaning t m 2007) (meaning t m 2027) (meaning t m 2241) (meaning t m 2534) (meaning t m 2699) (meaning t m 3189) (meaning t m 3256) source

theorem rule27893 (p2957 p3497 p3646 p3988 : Prop) (h : (¬ p3646) ∨ (¬ p3988) ∨ (¬ p2957) ∨ p3497) : (¬ p2957) ∨ (p3497) ∨ (¬ p3646) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial27893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (meaning t m 3497) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory17149 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule27893 (meaning t m 2957) (meaning t m 3497) (meaning t m 3646) (meaning t m 3988) source

theorem rule27894 (p2027 p2341 p2363 p3821 p4445 p4503 : Prop) (h : p2027 ∨ (¬ p2341) ∨ (¬ p3821) ∨ (¬ p4503) ∨ (¬ p4445) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2363) ∨ (¬ p3821) ∨ (¬ p4445) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17150 t (m.theta 0 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27894 (meaning t m 2027) (meaning t m 2341) (meaning t m 2363) (meaning t m 3821) (meaning t m 4445) (meaning t m 4503) source

theorem rule27895 (p2252 p2946 p2992 : Prop) (h : (¬ p2992) ∨ (¬ p2252) ∨ p2946) : (¬ p2252) ∨ (p2946) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial27895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (meaning t m 2946) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory17151 (m.theta 0 3) (m.theta 1 3) (m.theta 3 5)
  exact rule27895 (meaning t m 2252) (meaning t m 2946) (meaning t m 2992) source

theorem rule27898 (p2027 p2264 p2363 p2598 p3201 p3688 p3740 p4078 p4340 p4503 p4737 : Prop) (h : (¬ p2363) ∨ (¬ p2598) ∨ (¬ p4340) ∨ (¬ p4737) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p2264) ∨ (¬ p3740) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p4503)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3688) ∨ (¬ p3740) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial27898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory17154 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 8) (m.theta 3 7) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27898 (meaning t m 2027) (meaning t m 2264) (meaning t m 2363) (meaning t m 2598) (meaning t m 3201) (meaning t m 3688) (meaning t m 3740) (meaning t m 4078) (meaning t m 4340) (meaning t m 4503) (meaning t m 4737) source

theorem rule27900 (p2027 p2156 p2901 p3556 p4110 p4705 : Prop) (h : (¬ p2156) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4705) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial27900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17156 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule27900 (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 3556) (meaning t m 4110) (meaning t m 4705) source

theorem rule27901 (p2027 p2406 p2509 p3156 p3693 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p3156) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3693) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial27901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17157 t (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule27901 (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 3156) (meaning t m 3693) (meaning t m 4705) source

theorem rule27902 (p2027 p2441 p2901 p3246 p4278 p4705 : Prop) (h : (¬ p2441) ∨ (¬ p4278) ∨ (¬ p4705) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p3246)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial27902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17158 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule27902 (meaning t m 2027) (meaning t m 2441) (meaning t m 2901) (meaning t m 3246) (meaning t m 4278) (meaning t m 4705) source

theorem rule27905 (p2027 p2427 p3661 p3691 p3767 p4349 p4702 p5284 p5300 : Prop) (h : (¬ p5300) ∨ (¬ p2427) ∨ (¬ p3767) ∨ (¬ p3691) ∨ (¬ p4702) ∨ (¬ p3661) ∨ (¬ p4349) ∨ (¬ p5284) ∨ p2027) : (p2027) ∨ (¬ p2427) ∨ (¬ p3661) ∨ (¬ p3691) ∨ (¬ p3767) ∨ (¬ p4349) ∨ (¬ p4702) ∨ (¬ p5284) ∨ (¬ p5300) := by
  classical
  tauto

theorem initial27905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5300)) := by
  have source := ElevenTheory.theory17161 t (m.theta 0 7) (m.theta 0 9) (m.theta 3 5) (m.theta 3 8) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 9 10)
  exact rule27905 (meaning t m 2027) (meaning t m 2427) (meaning t m 3661) (meaning t m 3691) (meaning t m 3767) (meaning t m 4349) (meaning t m 4702) (meaning t m 5284) (meaning t m 5300) source

theorem rule27906 (p2027 p2241 p2264 p2363 p3027 p3646 p3692 p3988 p4503 p4524 : Prop) (h : (¬ p3692) ∨ (¬ p2363) ∨ (¬ p3646) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p2241) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3988)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4503) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial27906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory17162 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27906 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2363) (meaning t m 3027) (meaning t m 3646) (meaning t m 3692) (meaning t m 3988) (meaning t m 4503) (meaning t m 4524) source

theorem rule27907 (p2027 p2819 p3985 p3989 p4244 p4555 : Prop) (h : p2027 ∨ (¬ p3985) ∨ (¬ p4244) ∨ (¬ p3989) ∨ (¬ p2819) ∨ (¬ p4555)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p4244) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial27907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory17163 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule27907 (meaning t m 2027) (meaning t m 2819) (meaning t m 3985) (meaning t m 3989) (meaning t m 4244) (meaning t m 4555) source

theorem rule27910 (p2027 p2295 p2579 p2588 p3019 p3347 p4811 : Prop) (h : (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3019) ∨ (¬ p4811) ∨ (¬ p2295) ∨ (¬ p2588) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p3347) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial27910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory17166 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule27910 (meaning t m 2027) (meaning t m 2295) (meaning t m 2579) (meaning t m 2588) (meaning t m 3019) (meaning t m 3347) (meaning t m 4811) source

theorem rule27911 (p1994 p2027 p2651 p2764 p2952 p3879 p4322 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4322) ∨ (¬ p3879) ∨ (¬ p2952) ∨ p2764 ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2651)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial27911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory17167 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule27911 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 2952) (meaning t m 3879) (meaning t m 4322) (meaning t m 4948) source

theorem rule27915 (p2027 p2255 p2579 p2662 p3166 p3256 p3956 p4111 p4348 p4503 : Prop) (h : (¬ p2662) ∨ (¬ p3256) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3166) ∨ (¬ p2579) ∨ (¬ p2255) ∨ (¬ p4503) ∨ (¬ p3956) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17171 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27915 (meaning t m 2027) (meaning t m 2255) (meaning t m 2579) (meaning t m 2662) (meaning t m 3166) (meaning t m 3256) (meaning t m 3956) (meaning t m 4111) (meaning t m 4348) (meaning t m 4503) source

theorem rule27918 (p1994 p2027 p2247 p2406 p2440 p2688 p3379 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3379) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2688) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial27918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory17174 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule27918 (meaning t m 1994) (meaning t m 2027) (meaning t m 2247) (meaning t m 2406) (meaning t m 2440) (meaning t m 2688) (meaning t m 3379) source

theorem rule27919 (p2027 p2579 p2662 p2810 p3136 p4241 p4715 : Prop) (h : (¬ p2662) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p2810) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial27919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory17175 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule27919 (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2810) (meaning t m 3136) (meaning t m 4241) (meaning t m 4715) source

theorem rule27920 (p1998 p2027 p2579 p2842 p2911 p3389 p3422 : Prop) (h : (¬ p3422) ∨ (¬ p2579) ∨ (¬ p3389) ∨ p2842 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2579) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial27920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory17176 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule27920 (meaning t m 1998) (meaning t m 2027) (meaning t m 2579) (meaning t m 2842) (meaning t m 2911) (meaning t m 3389) (meaning t m 3422) source

theorem rule27921 (p2027 p2579 p3389 p3422 p3742 p4753 : Prop) (h : (¬ p3422) ∨ (¬ p2579) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3742) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial27921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory17177 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule27921 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 3422) (meaning t m 3742) (meaning t m 4753) source

theorem rule27930 (p1992 p2027 p2608 p2938 p3238 p3452 p4235 : Prop) (h : (¬ p2608) ∨ p2938 ∨ (¬ p1992) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3238)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2938) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial27930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory17186 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7)
  exact rule27930 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2938) (meaning t m 3238) (meaning t m 3452) (meaning t m 4235) source

theorem rule27932 (p1998 p2027 p2914 p3073 p3083 p3742 p4348 p4370 : Prop) (h : p2914 ∨ (¬ p4370) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3073) ∨ (¬ p3083) ∨ (¬ p4348) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2914) ∨ (¬ p3073) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p4348) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial27932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory17188 t (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27932 (meaning t m 1998) (meaning t m 2027) (meaning t m 2914) (meaning t m 3073) (meaning t m 3083) (meaning t m 3742) (meaning t m 4348) (meaning t m 4370) source

theorem rule27934 (p2027 p2911 p2922 p3324 p3365 p3379 p4195 p4503 p4736 : Prop) (h : (¬ p2922) ∨ (¬ p4736) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p4195) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial27934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17190 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule27934 (meaning t m 2027) (meaning t m 2911) (meaning t m 2922) (meaning t m 3324) (meaning t m 3365) (meaning t m 3379) (meaning t m 4195) (meaning t m 4503) (meaning t m 4736) source

theorem rule27936 (p2027 p2743 p3367 p3683 p3877 p5008 : Prop) (h : (¬ p3683) ∨ (¬ p5008) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p3877) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial27936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory17192 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8)
  exact rule27936 (meaning t m 2027) (meaning t m 2743) (meaning t m 3367) (meaning t m 3683) (meaning t m 3877) (meaning t m 5008) source

theorem rule27937 (p2027 p2156 p2901 p2911 p3548 p3952 p4366 p4521 p4647 : Prop) (h : (¬ p3548) ∨ (¬ p2156) ∨ (¬ p3952) ∨ (¬ p4521) ∨ (¬ p2901) ∨ (¬ p4647) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4521) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial27937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory17193 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule27937 (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 2911) (meaning t m 3548) (meaning t m 3952) (meaning t m 4366) (meaning t m 4521) (meaning t m 4647) source

theorem rule27940 (p1976 p2027 p2388 p2743 p3055 p3367 p4315 : Prop) (h : p2027 ∨ p2388 ∨ (¬ p3367) ∨ (¬ p1976) ∨ (¬ p2743) ∨ (¬ p4315) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2388) ∨ (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial27940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory17196 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule27940 (meaning t m 1976) (meaning t m 2027) (meaning t m 2388) (meaning t m 2743) (meaning t m 3055) (meaning t m 3367) (meaning t m 4315) source

theorem rule27941 (p1998 p2027 p2622 p2707 p2743 p2881 p3434 p3690 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p2881) ∨ (¬ p1998) ∨ (¬ p2707) ∨ (¬ p3690)) : (¬ p1998) ∨ (p2027) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial27941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory17197 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27941 (meaning t m 1998) (meaning t m 2027) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 2881) (meaning t m 3434) (meaning t m 3690) source

theorem rule27942 (p2027 p2254 p2657 p3073 p3449 p3574 p3956 p4348 p4503 : Prop) (h : (¬ p2254) ∨ (¬ p3574) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3073) ∨ (¬ p3956) ∨ (¬ p2657) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17198 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27942 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3073) (meaning t m 3449) (meaning t m 3574) (meaning t m 3956) (meaning t m 4348) (meaning t m 4503) source

theorem rule27944 (p2001 p2027 p2148 p2156 p2187 p2363 p3692 : Prop) (h : (¬ p2156) ∨ (¬ p3692) ∨ (¬ p2001) ∨ p2027 ∨ p2148 ∨ (¬ p2187) ∨ (¬ p2363)) : (¬ p2001) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial27944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory17200 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27944 (meaning t m 2001) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3692) source

theorem rule27945 (p2352 p3322 p3564 : Prop) (h : (¬ p3322) ∨ (¬ p3564) ∨ p2352) : (p2352) ∨ (¬ p3322) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial27945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory17201 (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule27945 (meaning t m 2352) (meaning t m 3322) (meaning t m 3564) source

theorem rule27946 (p2027 p2241 p2579 p2992 p3115 p3956 p4347 p4450 p5193 : Prop) (h : (¬ p2241) ∨ p2027 ∨ (¬ p3115) ∨ (¬ p4450) ∨ (¬ p4347) ∨ (¬ p3956) ∨ (¬ p5193) ∨ (¬ p2992) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17202 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule27946 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 2992) (meaning t m 3115) (meaning t m 3956) (meaning t m 4347) (meaning t m 4450) (meaning t m 5193) source

theorem rule27947 (p2027 p2166 p2210 p2254 p3414 p3947 p3969 p4381 p5119 : Prop) (h : (¬ p2254) ∨ (¬ p3414) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p2210) ∨ (¬ p4381) ∨ (¬ p3947) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3969) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial27947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory17203 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule27947 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 3414) (meaning t m 3947) (meaning t m 3969) (meaning t m 4381) (meaning t m 5119) source

theorem rule27950 (p2027 p2210 p2363 p2476 p2534 p2881 p2891 p4503 p5193 : Prop) (h : (¬ p2363) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2534) ∨ (¬ p2476) ∨ (¬ p5193) ∨ (¬ p2210) ∨ (¬ p4503) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4503) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17206 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27950 (meaning t m 2027) (meaning t m 2210) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 2881) (meaning t m 2891) (meaning t m 4503) (meaning t m 5193) source

theorem rule27951 (p2000 p2027 p2177 p2462 p3540 p3644 p4107 : Prop) (h : p2027 ∨ (¬ p2000) ∨ (¬ p4107) ∨ (¬ p3540) ∨ (¬ p2177) ∨ p2462 ∨ (¬ p3644)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial27951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory17207 t (m.theta 0 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27951 (meaning t m 2000) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3540) (meaning t m 3644) (meaning t m 4107) source

theorem rule27952 (p1992 p2027 p2202 p2440 p2668 p3019 p3688 p4358 : Prop) (h : (¬ p1992) ∨ p2027 ∨ (¬ p2668) ∨ p2202 ∨ (¬ p4358) ∨ (¬ p2440) ∨ (¬ p3688) ∨ (¬ p3019)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial27952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory17208 t (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 8)
  exact rule27952 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2668) (meaning t m 3019) (meaning t m 3688) (meaning t m 4358) source

theorem rule27953 (p1976 p2027 p2462 p2476 p3641 p3876 p3905 p4278 : Prop) (h : (¬ p2476) ∨ (¬ p3641) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p3876) ∨ p2462 ∨ (¬ p4278)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial27953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory17209 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 9)
  exact rule27953 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2476) (meaning t m 3641) (meaning t m 3876) (meaning t m 3905) (meaning t m 4278) source

theorem rule27956 (p2027 p2210 p2254 p2363 p2881 p2891 p2963 p4118 p4196 p4503 : Prop) (h : p2027 ∨ (¬ p2363) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p2891) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17212 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27956 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2363) (meaning t m 2881) (meaning t m 2891) (meaning t m 2963) (meaning t m 4118) (meaning t m 4196) (meaning t m 4503) source

theorem rule27957 (p2027 p3323 p3324 p4345 p4348 p4503 : Prop) (h : p2027 ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4503) ∨ (¬ p4348) ∨ (¬ p3323)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17213 t (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27957 (meaning t m 2027) (meaning t m 3323) (meaning t m 3324) (meaning t m 4345) (meaning t m 4348) (meaning t m 4503) source

theorem rule27958 (p2010 p2027 p2476 p2534 p3146 p3389 p3578 : Prop) (h : (¬ p2534) ∨ (¬ p2010) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p3389) ∨ p3578) : (¬ p2010) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3389) ∨ (p3578) := by
  classical
  tauto

theorem initial27958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3389)) ∨ (meaning t m 3578) := by
  have source := ElevenTheory.theory17214 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule27958 (meaning t m 2010) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 3146) (meaning t m 3389) (meaning t m 3578) source

theorem rule27959 (p1990 p2027 p2295 p2829 p3097 p3474 p3583 p4328 : Prop) (h : (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2829) ∨ (¬ p4328) ∨ (¬ p3583) ∨ p2027 ∨ p3474 ∨ (¬ p2295)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (p3474) ∨ (¬ p3583) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial27959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory17215 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule27959 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2829) (meaning t m 3097) (meaning t m 3474) (meaning t m 3583) (meaning t m 4328) source

theorem rule27961 (p1991 p2027 p2274 p2588 p2657 p2765 p3574 : Prop) (h : (¬ p3574) ∨ p2765 ∨ p2027 ∨ (¬ p2274) ∨ (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2588)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial27961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory17217 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule27961 (meaning t m 1991) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2657) (meaning t m 2765) (meaning t m 3574) source

theorem rule27964 (p2707 p2839 p3587 : Prop) (h : (¬ p3587) ∨ (¬ p2839) ∨ p2707) : (p2707) ∨ (¬ p2839) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial27964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2707) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory17220 (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule27964 (meaning t m 2707) (meaning t m 2839) (meaning t m 3587) source

theorem rule27966 (p4042 p4433 p4503 : Prop) (h : (¬ p4042) ∨ (¬ p4503) ∨ p4433) : (¬ p4042) ∨ (p4433) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4042)) ∨ (meaning t m 4433) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17222 t (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule27966 (meaning t m 4042) (meaning t m 4433) (meaning t m 4503) source

theorem rule27967 (p1993 p2027 p2287 p2651 p2810 p2963 p3005 : Prop) (h : (¬ p2651) ∨ p2287 ∨ (¬ p2810) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p1993) ∨ (¬ p3005)) : (¬ p1993) ∨ (p2027) ∨ (p2287) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3005) := by
  classical
  tauto

theorem initial27967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3005)) := by
  have source := ElevenTheory.theory17223 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule27967 (meaning t m 1993) (meaning t m 2027) (meaning t m 2287) (meaning t m 2651) (meaning t m 2810) (meaning t m 2963) (meaning t m 3005) source

theorem rule27968 (p2027 p2156 p2177 p2274 p2528 p3452 p3453 p4261 p4438 p4521 : Prop) (h : (¬ p4438) ∨ (¬ p3452) ∨ (¬ p2528) ∨ (¬ p3453) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p4521) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial27968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory17224 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule27968 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2528) (meaning t m 3452) (meaning t m 3453) (meaning t m 4261) (meaning t m 4438) (meaning t m 4521) source

theorem rule27976 (p2098 p2774 p4861 : Prop) (h : (¬ p4861) ∨ (¬ p2774) ∨ p2098) : (p2098) ∨ (¬ p2774) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial27976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2098) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory17232 (m.theta 0 2) (m.theta 2 6) (m.theta 2 8)
  exact rule27976 (meaning t m 2098) (meaning t m 2774) (meaning t m 4861) source

theorem rule27978 (p2104 p2774 p4861 : Prop) (h : (¬ p4861) ∨ (¬ p2774) ∨ (¬ p2104)) : (¬ p2104) ∨ (¬ p2774) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial27978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory17234 (m.theta 0 2) (m.theta 2 6) (m.theta 2 8)
  exact rule27978 (meaning t m 2104) (meaning t m 2774) (meaning t m 4861) source

theorem rule27981 (p2027 p2427 p4129 p4386 p4391 p4702 : Prop) (h : (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4702) ∨ (¬ p4386) ∨ p2027 ∨ (¬ p4391)) : (p2027) ∨ (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial27981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory17237 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10)
  exact rule27981 (meaning t m 2027) (meaning t m 2427) (meaning t m 4129) (meaning t m 4386) (meaning t m 4391) (meaning t m 4702) source

theorem rule27984 (p2579 p3363 p3573 p3641 : Prop) (h : (¬ p2579) ∨ (¬ p3573) ∨ (¬ p3363) ∨ (¬ p3641)) : (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3573) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial27984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory17240 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule27984 (meaning t m 2579) (meaning t m 3363) (meaning t m 3573) (meaning t m 3641) source

theorem rule27985 (p2027 p2098 p2247 p3324 p3609 p4154 p4348 p4503 p4733 : Prop) (h : (¬ p4154) ∨ (¬ p3324) ∨ (¬ p4503) ∨ (¬ p2247) ∨ (¬ p4733) ∨ (¬ p2098) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p3609) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial27985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17241 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27985 (meaning t m 2027) (meaning t m 2098) (meaning t m 2247) (meaning t m 3324) (meaning t m 3609) (meaning t m 4154) (meaning t m 4348) (meaning t m 4503) (meaning t m 4733) source

theorem rule27989 (p2027 p2138 p2406 p2598 p3698 p5217 : Prop) (h : (¬ p2138) ∨ (¬ p3698) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p5217)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p3698) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial27989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory17245 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule27989 (meaning t m 2027) (meaning t m 2138) (meaning t m 2406) (meaning t m 2598) (meaning t m 3698) (meaning t m 5217) source

theorem rule27992 (p2027 p2363 p2780 p2911 p3367 p3389 p3759 p4078 p4340 p4503 p4734 : Prop) (h : (¬ p3389) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p3367) ∨ (¬ p2363) ∨ (¬ p3759) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p4340) ∨ (¬ p4078)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial27992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory17248 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27992 (meaning t m 2027) (meaning t m 2363) (meaning t m 2780) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) (meaning t m 4078) (meaning t m 4340) (meaning t m 4503) (meaning t m 4734) source

theorem rule28001 (p3425 p4232 p5228 : Prop) (h : (¬ p5228) ∨ (¬ p3425) ∨ p4232) : (¬ p3425) ∨ (p4232) ∨ (¬ p5228) := by
  classical
  tauto

theorem initial28001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3425)) ∨ (meaning t m 4232) ∨ (¬ (meaning t m 5228)) := by
  have source := ElevenTheory.theory17257 (m.theta 0 2) (m.theta 2 7) (m.theta 2 9)
  exact rule28001 (meaning t m 3425) (meaning t m 4232) (meaning t m 5228) source

theorem rule28004 (p2027 p2098 p3555 p3609 p3989 p4173 p4348 p4503 p4733 : Prop) (h : (¬ p3609) ∨ (¬ p3989) ∨ (¬ p3555) ∨ (¬ p4348) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p4503) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3555) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17260 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28004 (meaning t m 2027) (meaning t m 2098) (meaning t m 3555) (meaning t m 3609) (meaning t m 3989) (meaning t m 4173) (meaning t m 4348) (meaning t m 4503) (meaning t m 4733) source

theorem rule28011 (p1998 p2027 p2177 p2449 p2765 p2995 p3952 p4278 p4710 : Prop) (h : (¬ p2449) ∨ (¬ p4710) ∨ (¬ p2177) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p2995) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2449) ∨ (p2765) ∨ (¬ p2995) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial28011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory17267 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28011 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2449) (meaning t m 2765) (meaning t m 2995) (meaning t m 3952) (meaning t m 4278) (meaning t m 4710) source

theorem rule28013 (p1975 p2027 p2299 p2622 p2630 p2656 p2911 p3389 : Prop) (h : p2027 ∨ p2622 ∨ (¬ p2656) ∨ (¬ p3389) ∨ (¬ p2299) ∨ (¬ p1975) ∨ (¬ p2630) ∨ (¬ p2911)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2911) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial28013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory17269 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule28013 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2911) (meaning t m 3389) source

theorem rule28015 (p2027 p2230 p2247 p2427 p2608 p2881 p3031 p3519 p3817 p4376 p4666 : Prop) (h : (¬ p2608) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4376) ∨ (¬ p4666) ∨ (¬ p3519) ∨ (¬ p3031) ∨ (¬ p2247) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3031) ∨ (¬ p3519) ∨ (¬ p3817) ∨ (¬ p4376) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial28015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory17271 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28015 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 2608) (meaning t m 2881) (meaning t m 3031) (meaning t m 3519) (meaning t m 3817) (meaning t m 4376) (meaning t m 4666) source

theorem rule28017 (p2027 p2230 p2427 p2608 p2881 p3519 p3591 p3923 p4376 p4503 : Prop) (h : (¬ p3519) ∨ (¬ p2881) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3591) ∨ (¬ p2427) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17273 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule28017 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2608) (meaning t m 2881) (meaning t m 3519) (meaning t m 3591) (meaning t m 3923) (meaning t m 4376) (meaning t m 4503) source

theorem rule28020 (p1998 p2027 p2396 p2873 p2881 p3309 p3690 p4338 : Prop) (h : p2873 ∨ (¬ p4338) ∨ (¬ p3309) ∨ (¬ p1998) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3690)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2396) ∨ (p2873) ∨ (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial28020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory17276 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28020 (meaning t m 1998) (meaning t m 2027) (meaning t m 2396) (meaning t m 2873) (meaning t m 2881) (meaning t m 3309) (meaning t m 3690) (meaning t m 4338) source

theorem rule28025 (p1998 p2027 p2417 p2437 p2545 p3527 p3817 : Prop) (h : (¬ p2417) ∨ p2545 ∨ (¬ p2437) ∨ (¬ p1998) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3817)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p3527) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial28025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory17281 t (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28025 (meaning t m 1998) (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 2545) (meaning t m 3527) (meaning t m 3817) source

theorem rule28026 (p1976 p2027 p2437 p2545 p2737 p3365 p3585 p3876 : Prop) (h : (¬ p2437) ∨ (¬ p3585) ∨ (¬ p1976) ∨ (¬ p2737) ∨ (¬ p3365) ∨ p2545 ∨ p2027 ∨ (¬ p3876)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial28026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory17282 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule28026 (meaning t m 1976) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2737) (meaning t m 3365) (meaning t m 3585) (meaning t m 3876) source

theorem rule28030 (p2027 p2132 p2245 p2363 p2870 p2881 p2963 p4118 p4196 p4503 p4733 : Prop) (h : (¬ p2963) ∨ (¬ p4196) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4503) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17286 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28030 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2363) (meaning t m 2870) (meaning t m 2881) (meaning t m 2963) (meaning t m 4118) (meaning t m 4196) (meaning t m 4503) (meaning t m 4733) source

theorem rule28031 (p1998 p2027 p2363 p2388 p3189 p3662 p4348 p4417 : Prop) (h : p2027 ∨ (¬ p4417) ∨ (¬ p4348) ∨ (¬ p2363) ∨ (¬ p1998) ∨ (¬ p3189) ∨ p2388 ∨ (¬ p3662)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (p2388) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial28031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory17287 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28031 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2388) (meaning t m 3189) (meaning t m 3662) (meaning t m 4348) (meaning t m 4417) source

theorem rule28032 (p3550 p4042 p4441 : Prop) (h : (¬ p3550) ∨ (¬ p4441) ∨ p4042) : (¬ p3550) ∨ (p4042) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial28032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (meaning t m 4042) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory17288 (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule28032 (meaning t m 3550) (meaning t m 4042) (meaning t m 4441) source

theorem rule28033 (p2027 p2247 p2470 p2528 p3324 p4154 p4348 p4503 p5190 : Prop) (h : (¬ p2470) ∨ (¬ p3324) ∨ (¬ p2528) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p5190) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial28033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory17289 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28033 (meaning t m 2027) (meaning t m 2247) (meaning t m 2470) (meaning t m 2528) (meaning t m 3324) (meaning t m 4154) (meaning t m 4348) (meaning t m 4503) (meaning t m 5190) source

theorem rule28037 (p3872 p3988 p4119 : Prop) (h : p4119 ∨ (¬ p3872) ∨ (¬ p3988)) : (¬ p3872) ∨ (¬ p3988) ∨ (p4119) := by
  classical
  tauto

theorem initial28037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3988)) ∨ (meaning t m 4119) := by
  have source := ElevenTheory.theory17293 (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule28037 (meaning t m 3872) (meaning t m 3988) (meaning t m 4119) source

theorem rule28039 (p2027 p2668 p2696 p2797 p3097 p3555 p4173 p4405 p4733 : Prop) (h : (¬ p3097) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p4405) ∨ (¬ p4173) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory17295 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28039 (meaning t m 2027) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3097) (meaning t m 3555) (meaning t m 4173) (meaning t m 4405) (meaning t m 4733) source

theorem rule28040 (p2027 p2331 p2589 p3506 p3690 p4117 p4191 p4235 p4421 p4621 p4729 : Prop) (h : (¬ p4621) ∨ (¬ p2589) ∨ (¬ p4729) ∨ (¬ p2331) ∨ (¬ p4235) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p3506) ∨ (¬ p4191) ∨ (¬ p4421)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4235) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial28040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory17296 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule28040 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 3506) (meaning t m 3690) (meaning t m 4117) (meaning t m 4191) (meaning t m 4235) (meaning t m 4421) (meaning t m 4621) (meaning t m 4729) source

theorem rule28047 (p3544 p4105 p4371 : Prop) (h : (¬ p4105) ∨ (¬ p3544) ∨ p4371) : (¬ p3544) ∨ (¬ p4105) ∨ (p4371) := by
  classical
  tauto

theorem initial28047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4105)) ∨ (meaning t m 4371) := by
  have source := ElevenTheory.theory17303 (m.theta 1 6) (m.theta 1 7) (m.theta 1 8)
  exact rule28047 (meaning t m 3544) (meaning t m 4105) (meaning t m 4371) source

theorem rule28050 (p2027 p2470 p2528 p3324 p3365 p4079 p4195 p4348 p4503 p4736 : Prop) (h : (¬ p3324) ∨ (¬ p4736) ∨ (¬ p4079) ∨ (¬ p3365) ∨ (¬ p4348) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2470) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17306 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28050 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3324) (meaning t m 3365) (meaning t m 4079) (meaning t m 4195) (meaning t m 4348) (meaning t m 4503) (meaning t m 4736) source

theorem rule28051 (p2027 p2284 p2590 p3654 p3743 p4137 p4705 : Prop) (h : p2027 ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4137) ∨ (¬ p3654)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4137) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17307 t (m.theta 0 6) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule28051 (meaning t m 2027) (meaning t m 2284) (meaning t m 2590) (meaning t m 3654) (meaning t m 3743) (meaning t m 4137) (meaning t m 4705) source

theorem rule28053 (p2027 p2341 p2441 p2901 p3644 p3691 p4705 : Prop) (h : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p2901) ∨ (¬ p2441) ∨ (¬ p4705) ∨ (¬ p3644) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17309 t (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28053 (meaning t m 2027) (meaning t m 2341) (meaning t m 2441) (meaning t m 2901) (meaning t m 3644) (meaning t m 3691) (meaning t m 4705) source

theorem rule28055 (p2027 p2850 p3156 p3693 p3874 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p2850) ∨ (¬ p3693) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17311 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule28055 (meaning t m 2027) (meaning t m 2850) (meaning t m 3156) (meaning t m 3693) (meaning t m 3874) (meaning t m 4705) source

theorem rule28058 (p2027 p2441 p2881 p2901 p3644 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17314 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28058 (meaning t m 2027) (meaning t m 2441) (meaning t m 2881) (meaning t m 2901) (meaning t m 3644) (meaning t m 4705) source

theorem rule28059 (p2027 p2254 p2363 p2911 p2922 p3172 p3379 p4118 p4503 : Prop) (h : (¬ p2922) ∨ (¬ p4503) ∨ (¬ p3379) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p4118) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17315 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28059 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2911) (meaning t m 2922) (meaning t m 3172) (meaning t m 3379) (meaning t m 4118) (meaning t m 4503) source

theorem rule28064 (p2027 p2255 p2363 p2651 p2911 p2922 p3177 p3857 p4116 p4360 p4503 : Prop) (h : (¬ p4503) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p3177) ∨ (¬ p2922) ∨ (¬ p4116) ∨ (¬ p2911) ∨ (¬ p2651) ∨ (¬ p3857) ∨ (¬ p2363) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4116) ∨ (¬ p4360) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17320 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28064 (meaning t m 2027) (meaning t m 2255) (meaning t m 2363) (meaning t m 2651) (meaning t m 2911) (meaning t m 2922) (meaning t m 3177) (meaning t m 3857) (meaning t m 4116) (meaning t m 4360) (meaning t m 4503) source

theorem rule28065 (p2027 p3051 p3156 p3688 p3954 p4042 p4320 p4358 p4503 p4521 : Prop) (h : (¬ p4358) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p4320) ∨ (¬ p4042) ∨ (¬ p3156) ∨ (¬ p3688) ∨ (¬ p3954)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial28065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory17321 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule28065 (meaning t m 2027) (meaning t m 3051) (meaning t m 3156) (meaning t m 3688) (meaning t m 3954) (meaning t m 4042) (meaning t m 4320) (meaning t m 4358) (meaning t m 4503) (meaning t m 4521) source

theorem rule28066 (p2027 p2253 p2750 p3166 p3954 p4360 : Prop) (h : (¬ p2253) ∨ (¬ p3166) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p3166) ∨ (¬ p3954) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial28066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory17322 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 8)
  exact rule28066 (meaning t m 2027) (meaning t m 2253) (meaning t m 2750) (meaning t m 3166) (meaning t m 3954) (meaning t m 4360) source

theorem rule28068 (p1987 p2027 p2598 p2699 p2749 p2992 p3585 p3589 p4315 : Prop) (h : p2027 ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p3589) ∨ (¬ p1987) ∨ p2699 ∨ (¬ p2992) ∨ (¬ p2749) ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial28068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory17324 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule28068 (meaning t m 1987) (meaning t m 2027) (meaning t m 2598) (meaning t m 2699) (meaning t m 2749) (meaning t m 2992) (meaning t m 3585) (meaning t m 3589) (meaning t m 4315) source

theorem rule28069 (p1992 p2027 p2143 p2169 p2274 p2313 p3583 p3989 p4198 : Prop) (h : p2169 ∨ (¬ p1992) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3989) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p3583)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial28069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory17325 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28069 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 3583) (meaning t m 3989) (meaning t m 4198) source

theorem rule28071 (p2027 p2138 p3073 p3449 p3758 p3989 p4348 p4503 p4736 : Prop) (h : (¬ p3449) ∨ (¬ p4503) ∨ (¬ p4736) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17327 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28071 (meaning t m 2027) (meaning t m 2138) (meaning t m 3073) (meaning t m 3449) (meaning t m 3758) (meaning t m 3989) (meaning t m 4348) (meaning t m 4503) (meaning t m 4736) source

theorem rule28072 (p2027 p2138 p2911 p2922 p3379 p3758 p3989 p4503 p4736 : Prop) (h : (¬ p4503) ∨ (¬ p2911) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2922) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17328 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule28072 (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3758) (meaning t m 3989) (meaning t m 4503) (meaning t m 4736) source

theorem rule28074 (p2027 p2363 p2911 p2922 p3379 p3692 p4120 p4503 p4524 : Prop) (h : (¬ p4503) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2911) ∨ (¬ p4524) ∨ (¬ p2363) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4503) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial28074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory17330 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28074 (meaning t m 2027) (meaning t m 2363) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3692) (meaning t m 4120) (meaning t m 4503) (meaning t m 4524) source

theorem rule28075 (p2027 p2313 p2787 p2946 p3644 p3755 p4117 p4315 p4348 p4710 p5109 : Prop) (h : (¬ p3755) ∨ p2027 ∨ (¬ p2787) ∨ (¬ p4315) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p5109) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p4710)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4348) ∨ (¬ p4710) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial28075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory17331 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28075 (meaning t m 2027) (meaning t m 2313) (meaning t m 2787) (meaning t m 2946) (meaning t m 3644) (meaning t m 3755) (meaning t m 4117) (meaning t m 4315) (meaning t m 4348) (meaning t m 4710) (meaning t m 5109) source

theorem rule28076 (p2027 p2246 p2498 p2749 p2946 p3005 p3379 p3591 p3956 p4315 p4771 p5216 : Prop) (h : (¬ p2749) ∨ (¬ p3956) ∨ (¬ p3379) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p4771) ∨ (¬ p2946) ∨ (¬ p2498) ∨ (¬ p4315) ∨ (¬ p2246) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2498) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4315) ∨ (¬ p4771) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial28076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory17332 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule28076 (meaning t m 2027) (meaning t m 2246) (meaning t m 2498) (meaning t m 2749) (meaning t m 2946) (meaning t m 3005) (meaning t m 3379) (meaning t m 3591) (meaning t m 3956) (meaning t m 4315) (meaning t m 4771) (meaning t m 5216) source

theorem rule28078 (p2510 p2573 p2656 p3083 : Prop) (h : (¬ p2573) ∨ (¬ p2510) ∨ (¬ p2656) ∨ p3083) : (¬ p2510) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p3083) := by
  classical
  tauto

theorem initial28078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 3083) := by
  have source := ElevenTheory.theory17334 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule28078 (meaning t m 2510) (meaning t m 2573) (meaning t m 2656) (meaning t m 3083) source

theorem rule28080 (p2027 p2685 p4066 p4235 p4283 p4315 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p4315) ∨ (¬ p2685) ∨ (¬ p4283)) : (p2027) ∨ (¬ p2685) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4315) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17336 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule28080 (meaning t m 2027) (meaning t m 2685) (meaning t m 4066) (meaning t m 4235) (meaning t m 4283) (meaning t m 4315) (meaning t m 4705) source

theorem rule28082 (p2006 p2027 p2166 p2873 p3051 p4120 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p2006) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2166) ∨ (¬ p4120) ∨ p2873) : (¬ p2006) ∨ (p2027) ∨ (¬ p2166) ∨ (p2873) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial28082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory17338 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule28082 (meaning t m 2006) (meaning t m 2027) (meaning t m 2166) (meaning t m 2873) (meaning t m 3051) (meaning t m 4120) (meaning t m 4244) source

theorem rule28086 (p2027 p2230 p2247 p2427 p2881 p3324 p4154 p4503 p5190 : Prop) (h : (¬ p3324) ∨ (¬ p4503) ∨ (¬ p5190) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial28086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory17342 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule28086 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 2881) (meaning t m 3324) (meaning t m 4154) (meaning t m 4503) (meaning t m 5190) source

theorem rule28088 (p2027 p3319 p3923 p4345 p4348 p4503 : Prop) (h : (¬ p4345) ∨ (¬ p3923) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3319)) : (p2027) ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17344 t (m.theta 1 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule28088 (meaning t m 2027) (meaning t m 3319) (meaning t m 3923) (meaning t m 4345) (meaning t m 4348) (meaning t m 4503) source

theorem rule28089 (p2027 p2241 p2598 p2750 p2753 p2911 p3201 p3591 p3923 p4503 : Prop) (h : (¬ p3591) ∨ (¬ p2753) ∨ (¬ p2241) ∨ (¬ p2911) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p2750) ∨ (¬ p4503) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17345 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule28089 (meaning t m 2027) (meaning t m 2241) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2911) (meaning t m 3201) (meaning t m 3591) (meaning t m 3923) (meaning t m 4503) source

theorem rule28091 (p2027 p2797 p2810 p2963 p3286 p5177 : Prop) (h : (¬ p2810) ∨ (¬ p2963) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p5177) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p5177) := by
  classical
  tauto

theorem initial28091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 5177)) := by
  have source := ElevenTheory.theory17347 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 9)
  exact rule28091 (meaning t m 2027) (meaning t m 2797) (meaning t m 2810) (meaning t m 2963) (meaning t m 3286) (meaning t m 5177) source

theorem rule28092 (p2027 p2470 p2528 p2797 p2963 p3877 p4041 p4236 p4348 p4419 : Prop) (h : (¬ p4041) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p3877) ∨ (¬ p2797) ∨ (¬ p2470) ∨ (¬ p4419) ∨ (¬ p2963) ∨ (¬ p2528) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial28092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory17348 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28092 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2797) (meaning t m 2963) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) (meaning t m 4348) (meaning t m 4419) source

theorem rule28093 (p4042 p4433 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p4042) ∨ p4433) : (¬ p4042) ∨ (p4433) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4042)) ∨ (meaning t m 4433) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17349 t (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule28093 (meaning t m 4042) (meaning t m 4433) (meaning t m 4503) source

theorem rule28098 (p2027 p2284 p2386 p2406 p2499 p3743 p4705 : Prop) (h : p2027 ∨ (¬ p3743) ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p2499) ∨ (¬ p2406) ∨ (¬ p2386)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3743) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17354 t (m.theta 0 6) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule28098 (meaning t m 2027) (meaning t m 2284) (meaning t m 2386) (meaning t m 2406) (meaning t m 2499) (meaning t m 3743) (meaning t m 4705) source

theorem rule28100 (p1991 p2027 p2462 p2881 p3414 p3553 p3690 : Prop) (h : p2462 ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3553)) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial28100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory17356 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28100 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 3414) (meaning t m 3553) (meaning t m 3690) source

theorem rule28101 (p2027 p2307 p2440 p2657 p2786 p2819 p3822 p3880 p4134 p4789 : Prop) (h : p2027 ∨ (¬ p3822) ∨ (¬ p4789) ∨ (¬ p4134) ∨ (¬ p2819) ∨ (¬ p3880) ∨ (¬ p2307) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial28101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory17357 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule28101 (meaning t m 2027) (meaning t m 2307) (meaning t m 2440) (meaning t m 2657) (meaning t m 2786) (meaning t m 2819) (meaning t m 3822) (meaning t m 3880) (meaning t m 4134) (meaning t m 4789) source

theorem rule28103 (p2510 p3574 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p2510) ∨ p3574) : (¬ p2510) ∨ (p3574) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial28103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (meaning t m 3574) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory17359 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule28103 (meaning t m 2510) (meaning t m 3574) (meaning t m 4256) source

theorem rule28104 (p2027 p2499 p2573 p2737 p3759 p4257 p4749 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4257) ∨ (¬ p2573) ∨ (¬ p3759) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial28104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory17360 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule28104 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2737) (meaning t m 3759) (meaning t m 4257) (meaning t m 4749) source

theorem rule28105 (p2027 p3156 p3949 p3969 p4208 p5122 : Prop) (h : (¬ p3156) ∨ (¬ p3969) ∨ (¬ p3949) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p4208)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p3969) ∨ (¬ p4208) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial28105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory17361 t (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10) (m.theta 8 9)
  exact rule28105 (meaning t m 2027) (meaning t m 3156) (meaning t m 3949) (meaning t m 3969) (meaning t m 4208) (meaning t m 5122) source

theorem rule28107 (p1985 p2027 p2608 p2699 p2707 p3434 p3690 : Prop) (h : (¬ p3690) ∨ (¬ p2608) ∨ p2027 ∨ p2699 ∨ (¬ p1985) ∨ (¬ p3434) ∨ (¬ p2707)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial28107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory17363 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule28107 (meaning t m 1985) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 3434) (meaning t m 3690) source

theorem rule28112 (p1975 p2027 p2553 p2584 p2622 p2630 p2656 p3654 p4137 : Prop) (h : (¬ p2656) ∨ p2622 ∨ (¬ p2584) ∨ (¬ p4137) ∨ (¬ p2630) ∨ (¬ p2553) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2584) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial28112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2584)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory17368 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule28112 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2584) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3654) (meaning t m 4137) source

theorem rule28114 (p2027 p2284 p2319 p2341 p2441 p3644 p3743 p4705 : Prop) (h : (¬ p2341) ∨ (¬ p2319) ∨ (¬ p3644) ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p3743) ∨ (¬ p2441) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p3644) ∨ (¬ p3743) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial28114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory17370 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 7 8)
  exact rule28114 (meaning t m 2027) (meaning t m 2284) (meaning t m 2319) (meaning t m 2341) (meaning t m 2441) (meaning t m 3644) (meaning t m 3743) (meaning t m 4705) source

theorem rule28115 (p2027 p3166 p3414 p3644 p4653 p5074 p5307 : Prop) (h : (¬ p5307) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p5074) ∨ (¬ p3166) ∨ (¬ p4653) ∨ (¬ p3644)) : (p2027) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p5074) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial28115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4653)) ∨ (¬ (meaning t m 5074)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory17371 t (m.theta 0 3) (m.theta 1 8) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule28115 (meaning t m 2027) (meaning t m 3166) (meaning t m 3414) (meaning t m 3644) (meaning t m 4653) (meaning t m 5074) (meaning t m 5307) source

theorem rule28116 (p2027 p2299 p2313 p2406 p2982 p3379 p4348 p4450 p5021 : Prop) (h : (¬ p2299) ∨ (¬ p4450) ∨ (¬ p4348) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p5021) ∨ (¬ p2313) ∨ (¬ p3379) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial28116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory17372 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28116 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2406) (meaning t m 2982) (meaning t m 3379) (meaning t m 4348) (meaning t m 4450) (meaning t m 5021) source

theorem rule28119 (p2027 p2132 p2860 p4232 p5026 p5043 : Prop) (h : (¬ p2860) ∨ (¬ p5043) ∨ (¬ p2132) ∨ (¬ p5026) ∨ p2027 ∨ (¬ p4232)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4232) ∨ (¬ p5026) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial28119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5026)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory17375 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 9) (m.theta 5 6) (m.theta 5 9)
  exact rule28119 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 4232) (meaning t m 5026) (meaning t m 5043) source

theorem rule28120 (p1982 p2027 p2459 p2656 p2688 p2727 p2911 p3389 : Prop) (h : p2688 ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p3389)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial28120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory17376 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28120 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2911) (meaning t m 3389) source

theorem rule28121 (p1982 p2027 p2765 p2972 p3412 p3680 p3952 p4444 : Prop) (h : (¬ p3952) ∨ p2765 ∨ (¬ p2972) ∨ (¬ p1982) ∨ (¬ p3412) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p3680)) : (¬ p1982) ∨ (p2027) ∨ (p2765) ∨ (¬ p2972) ∨ (¬ p3412) ∨ (¬ p3680) ∨ (¬ p3952) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial28121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory17377 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28121 (meaning t m 1982) (meaning t m 2027) (meaning t m 2765) (meaning t m 2972) (meaning t m 3412) (meaning t m 3680) (meaning t m 3952) (meaning t m 4444) source

theorem rule28122 (p2027 p2210 p2881 p2891 p3055 p3876 p4278 p4666 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p2881) ∨ (¬ p4666) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p4278) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p2891)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory17378 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28122 (meaning t m 2027) (meaning t m 2210) (meaning t m 2881) (meaning t m 2891) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) (meaning t m 4666) (meaning t m 4736) source

theorem rule28123 (p2743 p3583 p4392 : Prop) (h : (¬ p2743) ∨ (¬ p4392) ∨ p3583) : (¬ p2743) ∨ (p3583) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial28123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (meaning t m 3583) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory17379 (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule28123 (meaning t m 2743) (meaning t m 3583) (meaning t m 4392) source

theorem rule28125 (p1987 p2027 p2737 p3551 p3588 p3959 p3982 p5558 : Prop) (h : (¬ p3959) ∨ (¬ p3588) ∨ (¬ p2737) ∨ (¬ p3551) ∨ p2027 ∨ p3982 ∨ (¬ p1987) ∨ (¬ p5558)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial28125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory17381 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10)
  exact rule28125 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) (meaning t m 3982) (meaning t m 5558) source

theorem rule28129 (p1992 p2027 p2608 p2911 p2914 p3548 p4366 : Prop) (h : (¬ p1992) ∨ (¬ p2608) ∨ (¬ p4366) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p2911) ∨ p2914) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial28129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory17385 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule28129 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2911) (meaning t m 2914) (meaning t m 3548) (meaning t m 4366) source

theorem rule28130 (p2027 p2210 p2247 p2744 p2891 p2911 p3347 p3551 p3741 p4110 p4257 p4558 p5197 : Prop) (h : (¬ p3347) ∨ (¬ p3551) ∨ (¬ p4257) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2247) ∨ (¬ p5197) ∨ (¬ p2911) ∨ (¬ p2744) ∨ (¬ p4558) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p3741)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3347) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4257) ∨ (¬ p4558) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial28130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory17386 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule28130 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2744) (meaning t m 2891) (meaning t m 2911) (meaning t m 3347) (meaning t m 3551) (meaning t m 3741) (meaning t m 4110) (meaning t m 4257) (meaning t m 4558) (meaning t m 5197) source

theorem rule28131 (p2027 p2138 p2331 p2363 p2668 p3690 p4244 p4669 p4786 : Prop) (h : (¬ p4244) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p2668) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial28131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory17387 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28131 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4786) source

theorem rule28132 (p2027 p2138 p2807 p3506 p3692 p3694 p3950 p4381 p4661 p4786 : Prop) (h : p2027 ∨ (¬ p4381) ∨ (¬ p3692) ∨ (¬ p2138) ∨ (¬ p4786) ∨ (¬ p3950) ∨ (¬ p4661) ∨ (¬ p3694) ∨ (¬ p2807) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial28132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4661)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory17388 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 3 9) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28132 (meaning t m 2027) (meaning t m 2138) (meaning t m 2807) (meaning t m 3506) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4381) (meaning t m 4661) (meaning t m 4786) source

theorem rule28133 (p2122 p2553 p4342 : Prop) (h : (¬ p4342) ∨ (¬ p2122) ∨ p2553) : (¬ p2122) ∨ (p2553) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial28133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (meaning t m 2553) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory17389 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule28133 (meaning t m 2122) (meaning t m 2553) (meaning t m 4342) source

theorem rule28135 (p2027 p2819 p3573 p3979 p4286 p5225 : Prop) (h : (¬ p5225) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p4286) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial28135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory17391 t (m.theta 2 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10)
  exact rule28135 (meaning t m 2027) (meaning t m 2819) (meaning t m 3573) (meaning t m 3979) (meaning t m 4286) (meaning t m 5225) source

theorem rule28140 (p2027 p2246 p2284 p2608 p2744 p2946 p3125 p3860 p4261 p4330 : Prop) (h : (¬ p2744) ∨ (¬ p4261) ∨ (¬ p2608) ∨ (¬ p3860) ∨ (¬ p2246) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p3125) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial28140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory17396 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule28140 (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3125) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) source

theorem rule28142 (p2982 p3212 p4031 : Prop) (h : (¬ p4031) ∨ (¬ p2982) ∨ p3212) : (¬ p2982) ∨ (p3212) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial28142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (meaning t m 3212) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory17398 (m.theta 0 5) (m.theta 4 5) (m.theta 5 9)
  exact rule28142 (meaning t m 2982) (meaning t m 3212) (meaning t m 4031) source

theorem rule28145 (p2230 p3389 p3741 : Prop) (h : (¬ p3741) ∨ (¬ p2230) ∨ p3389) : (¬ p2230) ∨ (p3389) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial28145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (meaning t m 3389) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory17401 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule28145 (meaning t m 2230) (meaning t m 3389) (meaning t m 3741) source

theorem rule28152 (p2027 p2230 p2982 p3365 p3572 p3680 p4391 p4419 p4831 : Prop) (h : (¬ p4419) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2230) ∨ (¬ p3680) ∨ (¬ p2982) ∨ (¬ p3572) ∨ (¬ p4831) ∨ (¬ p4391)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial28152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory17408 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule28152 (meaning t m 2027) (meaning t m 2230) (meaning t m 2982) (meaning t m 3365) (meaning t m 3572) (meaning t m 3680) (meaning t m 4391) (meaning t m 4419) (meaning t m 4831) source

theorem rule28154 (p2027 p2341 p2657 p3246 p3366 p3370 p3570 p3584 p3683 p4137 p4236 p4377 p4625 p4988 : Prop) (h : (¬ p3370) ∨ (¬ p2657) ∨ (¬ p3683) ∨ (¬ p3584) ∨ (¬ p4236) ∨ (¬ p3246) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p4377) ∨ (¬ p4137) ∨ (¬ p2341) ∨ (¬ p4988) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2657) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4625) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial28154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory17410 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule28154 (meaning t m 2027) (meaning t m 2341) (meaning t m 2657) (meaning t m 3246) (meaning t m 3366) (meaning t m 3370) (meaning t m 3570) (meaning t m 3584) (meaning t m 3683) (meaning t m 4137) (meaning t m 4236) (meaning t m 4377) (meaning t m 4625) (meaning t m 4988) source

theorem rule28158 (p1976 p2027 p2169 p2579 p3483 p3905 p4137 p4358 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4137) ∨ (¬ p3905) ∨ (¬ p2579) ∨ (¬ p3483) ∨ p2169) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p4137) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial28158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory17414 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule28158 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2579) (meaning t m 3483) (meaning t m 3905) (meaning t m 4137) (meaning t m 4358) source

theorem rule28159 (p2528 p2531 p3146 : Prop) (h : (¬ p3146) ∨ (¬ p2531) ∨ p2528) : (p2528) ∨ (¬ p2531) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial28159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2528) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory17415 (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule28159 (meaning t m 2528) (meaning t m 2531) (meaning t m 3146) source

theorem rule28160 (p2027 p3434 p3587 p3690 p3952 p4316 p4558 : Prop) (h : p2027 ∨ (¬ p4316) ∨ (¬ p3690) ∨ (¬ p4558) ∨ (¬ p3587) ∨ (¬ p3434) ∨ (¬ p3952)) : (p2027) ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory17416 t (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule28160 (meaning t m 2027) (meaning t m 3434) (meaning t m 3587) (meaning t m 3690) (meaning t m 3952) (meaning t m 4316) (meaning t m 4558) source

theorem rule28161 (p2027 p2191 p2220 p2891 p3646 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p2891) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2891) ∨ (¬ p3646) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory17417 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule28161 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2891) (meaning t m 3646) (meaning t m 4558) source

theorem rule28162 (p2027 p2459 p2717 p3857 p3961 p5258 : Prop) (h : (¬ p2717) ∨ (¬ p5258) ∨ (¬ p3961) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p5258) := by
  classical
  tauto

theorem initial28162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 5258)) := by
  have source := ElevenTheory.theory17418 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28162 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 3857) (meaning t m 3961) (meaning t m 5258) source

theorem rule28167 (p2027 p2383 p2586 p3016 p4256 p4432 : Prop) (h : (¬ p2586) ∨ (¬ p4256) ∨ (¬ p4432) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3016)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2586) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial28167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory17423 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule28167 (meaning t m 2027) (meaning t m 2383) (meaning t m 2586) (meaning t m 3016) (meaning t m 4256) (meaning t m 4432) source

theorem rule28173 (p1994 p2027 p2299 p2588 p3574 p3982 p5558 : Prop) (h : (¬ p3574) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p1994) ∨ p2027 ∨ p3982 ∨ (¬ p5558)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial28173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory17429 t (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule28173 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 3574) (meaning t m 3982) (meaning t m 5558) source

theorem rule28174 (p2027 p2253 p2299 p2780 p2946 p3256 p3692 p3822 p4237 p4736 p4902 : Prop) (h : p2027 ∨ (¬ p2780) ∨ (¬ p4902) ∨ (¬ p2253) ∨ (¬ p3822) ∨ (¬ p2299) ∨ (¬ p3692) ∨ (¬ p2946) ∨ (¬ p4237) ∨ (¬ p4736) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4237) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial28174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory17430 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28174 (meaning t m 2027) (meaning t m 2253) (meaning t m 2299) (meaning t m 2780) (meaning t m 2946) (meaning t m 3256) (meaning t m 3692) (meaning t m 3822) (meaning t m 4237) (meaning t m 4736) (meaning t m 4902) source

theorem rule28175 (p2027 p3051 p3125 p3946 p4198 p4558 : Prop) (h : (¬ p4198) ∨ (¬ p3125) ∨ (¬ p3051) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p3946)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory17431 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule28175 (meaning t m 2027) (meaning t m 3051) (meaning t m 3125) (meaning t m 3946) (meaning t m 4198) (meaning t m 4558) source

theorem rule28181 (p2088 p2459 p4403 : Prop) (h : (¬ p2459) ∨ (¬ p4403) ∨ p2088) : (p2088) ∨ (¬ p2459) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial28181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory17437 (m.theta 0 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28181 (meaning t m 2088) (meaning t m 2459) (meaning t m 4403) source

theorem rule28186 (p2027 p2104 p2352 p2459 p2651 p3016 p4133 p4340 p4786 : Prop) (h : (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p4786) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial28186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory17442 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28186 (meaning t m 2027) (meaning t m 2104) (meaning t m 2352) (meaning t m 2459) (meaning t m 2651) (meaning t m 3016) (meaning t m 4133) (meaning t m 4340) (meaning t m 4786) source

theorem rule28189 (p2027 p2476 p2518 p2608 p4108 p4376 : Prop) (h : (¬ p4108) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial28189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory17445 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 8)
  exact rule28189 (meaning t m 2027) (meaning t m 2476) (meaning t m 2518) (meaning t m 2608) (meaning t m 4108) (meaning t m 4376) source

theorem rule28192 (p1976 p2027 p2881 p2938 p3055 p3644 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p2881) ∨ (¬ p3055) ∨ p2938 ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3644)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial28192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory17448 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule28192 (meaning t m 1976) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) source

theorem rule28196 (p1982 p2363 p2668 p3008 p4973 : Prop) (h : (¬ p2668) ∨ (¬ p1982) ∨ (¬ p2363) ∨ p3008 ∨ p4973) : (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (p3008) ∨ (p4973) := by
  classical
  tauto

theorem initial28196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 3008) ∨ (meaning t m 4973) := by
  have source := ElevenTheory.theory17452 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule28196 (meaning t m 1982) (meaning t m 2363) (meaning t m 2668) (meaning t m 3008) (meaning t m 4973) source

theorem rule28198 (p1982 p2027 p2459 p2717 p2842 p3055 p3471 : Prop) (h : p2027 ∨ p2842 ∨ (¬ p3471) ∨ (¬ p3055) ∨ (¬ p2717) ∨ (¬ p2459) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial28198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory17454 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28198 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 2842) (meaning t m 3055) (meaning t m 3471) source

theorem rule28200 (p2685 p2742 p3027 : Prop) (h : (¬ p2742) ∨ (¬ p3027) ∨ p2685) : (p2685) ∨ (¬ p2742) ∨ (¬ p3027) := by
  classical
  tauto

theorem initial28200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) := by
  have source := ElevenTheory.theory17456 (m.theta 1 3) (m.theta 2 3) (m.theta 3 7)
  exact rule28200 (meaning t m 2685) (meaning t m 2742) (meaning t m 3027) source

theorem rule28202 (p1986 p2027 p2138 p2598 p2633 p3486 p3570 p4243 : Prop) (h : (¬ p2598) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4243) ∨ (¬ p2138) ∨ p2633 ∨ (¬ p3570)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial28202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory17458 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule28202 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2633) (meaning t m 3486) (meaning t m 3570) (meaning t m 4243) source

theorem rule28203 (p2027 p2191 p2619 p3051 p3370 p3758 p4558 : Prop) (h : (¬ p3758) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3758) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial28203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory17459 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule28203 (meaning t m 2027) (meaning t m 2191) (meaning t m 2619) (meaning t m 3051) (meaning t m 3370) (meaning t m 3758) (meaning t m 4558) source

theorem rule28205 (p2027 p2383 p3323 p3324 p3583 p3954 p4368 p4385 p5017 : Prop) (h : (¬ p2383) ∨ (¬ p3954) ∨ (¬ p3583) ∨ (¬ p5017) ∨ (¬ p4368) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4385) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4368) ∨ (¬ p4385) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial28205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory17461 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule28205 (meaning t m 2027) (meaning t m 2383) (meaning t m 3323) (meaning t m 3324) (meaning t m 3583) (meaning t m 3954) (meaning t m 4368) (meaning t m 4385) (meaning t m 5017) source

theorem rule28207 (p3256 p3609 p4967 : Prop) (h : (¬ p3256) ∨ (¬ p4967) ∨ p3609) : (¬ p3256) ∨ (p3609) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial28207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (meaning t m 3609) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory17463 (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule28207 (meaning t m 3256) (meaning t m 3609) (meaning t m 4967) source

theorem rule28208 (p3256 p4340 p4967 : Prop) (h : (¬ p3256) ∨ (¬ p4967) ∨ (¬ p4340)) : (¬ p3256) ∨ (¬ p4340) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial28208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory17464 (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule28208 (meaning t m 3256) (meaning t m 4340) (meaning t m 4967) source

theorem rule28209 (p2027 p2588 p2870 p3758 p3958 p4140 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p4140) ∨ (¬ p3958) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p3958) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial28209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory17465 t (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule28209 (meaning t m 2027) (meaning t m 2588) (meaning t m 2870) (meaning t m 3758) (meaning t m 3958) (meaning t m 4140) source

theorem rule28211 (p1982 p2027 p2132 p2619 p2622 p2743 p2753 p3146 : Prop) (h : (¬ p1982) ∨ p2622 ∨ (¬ p2753) ∨ (¬ p2619) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial28211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory17467 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule28211 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2622) (meaning t m 2743) (meaning t m 2753) (meaning t m 3146) source

theorem rule28214 (p3590 p3684 p3948 p4210 : Prop) (h : (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4210) ∨ (¬ p3590)) : (¬ p3590) ∨ (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial28214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory17470 (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5)
  exact rule28214 (meaning t m 3590) (meaning t m 3684) (meaning t m 3948) (meaning t m 4210) source

theorem rule28216 (p2027 p2104 p2248 p2363 p2881 p2901 p2946 p3873 p4340 p4503 : Prop) (h : (¬ p2881) ∨ (¬ p3873) ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p2104) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2363) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17472 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28216 (meaning t m 2027) (meaning t m 2104) (meaning t m 2248) (meaning t m 2363) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3873) (meaning t m 4340) (meaning t m 4503) source

theorem rule28217 (p1998 p2027 p2619 p2765 p3146 p3758 p4348 : Prop) (h : (¬ p3758) ∨ p2765 ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p2619)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3758) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial28217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory17473 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28217 (meaning t m 1998) (meaning t m 2027) (meaning t m 2619) (meaning t m 2765) (meaning t m 3146) (meaning t m 3758) (meaning t m 4348) source

theorem rule28218 (p2027 p2220 p3146 p3688 p3954 p4348 p4358 p4503 p4521 : Prop) (h : (¬ p4521) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4348) ∨ (¬ p2220) ∨ (¬ p4503) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial28218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory17474 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28218 (meaning t m 2027) (meaning t m 2220) (meaning t m 3146) (meaning t m 3688) (meaning t m 3954) (meaning t m 4348) (meaning t m 4358) (meaning t m 4503) (meaning t m 4521) source

theorem rule28219 (p1994 p2027 p2323 p2440 p2807 p2850 p3475 p3572 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p1994) ∨ (¬ p3475) ∨ (¬ p2440) ∨ (¬ p2850)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2440) ∨ (¬ p2807) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial28219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory17475 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule28219 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2440) (meaning t m 2807) (meaning t m 2850) (meaning t m 3475) (meaning t m 3572) source

theorem rule28223 (p1998 p2027 p2114 p2717 p2737 p3365 p3471 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p1998) ∨ (¬ p3471) ∨ (¬ p2717)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial28223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory17479 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule28223 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2717) (meaning t m 2737) (meaning t m 3365) (meaning t m 3471) source

theorem rule28225 (p1994 p2027 p2323 p2663 p3389 p3422 p3574 p3876 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p3574) ∨ (¬ p3876) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p1994) ∨ (¬ p3422)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial28225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory17481 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule28225 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2663) (meaning t m 3389) (meaning t m 3422) (meaning t m 3574) (meaning t m 3876) source

theorem rule28227 (p2027 p2264 p2363 p2534 p2579 p2685 p2696 p2753 p3347 p3573 p4503 p5216 : Prop) (h : (¬ p2579) ∨ (¬ p3347) ∨ (¬ p2753) ∨ (¬ p2534) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p3573) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4503) ∨ (¬ p5216) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3573) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial28227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory17483 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28227 (meaning t m 2027) (meaning t m 2264) (meaning t m 2363) (meaning t m 2534) (meaning t m 2579) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3573) (meaning t m 4503) (meaning t m 5216) source

theorem rule28228 (p3369 p4198 p5015 : Prop) (h : (¬ p3369) ∨ (¬ p4198) ∨ p5015) : (¬ p3369) ∨ (¬ p4198) ∨ (p5015) := by
  classical
  tauto

theorem initial28228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4198)) ∨ (meaning t m 5015) := by
  have source := ElevenTheory.theory17484 (m.theta 0 1) (m.theta 0 5) (m.theta 0 6)
  exact rule28228 (meaning t m 3369) (meaning t m 4198) (meaning t m 5015) source

theorem rule28229 (p1994 p2027 p2440 p2997 p3097 p3125 p3946 p4031 p4198 : Prop) (h : (¬ p4031) ∨ (¬ p2440) ∨ (¬ p3097) ∨ p2027 ∨ p2997 ∨ (¬ p4198) ∨ (¬ p3946) ∨ (¬ p1994) ∨ (¬ p3125)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial28229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory17485 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule28229 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3946) (meaning t m 4031) (meaning t m 4198) source

theorem rule28230 (p2027 p2299 p2579 p2588 p3347 p3449 p3544 p3631 p3954 p4668 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3347) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3544) ∨ (¬ p4668) ∨ (¬ p3954) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3544) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial28230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory17486 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28230 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 3347) (meaning t m 3449) (meaning t m 3544) (meaning t m 3631) (meaning t m 3954) (meaning t m 4668) (meaning t m 5216) source

theorem rule28243 (p2027 p2098 p2780 p3989 p4326 p4401 : Prop) (h : (¬ p2098) ∨ (¬ p4326) ∨ (¬ p2780) ∨ (¬ p4401) ∨ p2027 ∨ (¬ p3989)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4326) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial28243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory17499 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8)
  exact rule28243 (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 3989) (meaning t m 4326) (meaning t m 4401) source

theorem rule28244 (p1996 p2027 p2202 p2417 p2589 p3389 p3947 : Prop) (h : (¬ p2589) ∨ p2027 ∨ p2202 ∨ (¬ p2417) ∨ (¬ p3947) ∨ (¬ p3389) ∨ (¬ p1996)) : (¬ p1996) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial28244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory17500 t (m.theta 0 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule28244 (meaning t m 1996) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2589) (meaning t m 3389) (meaning t m 3947) source

theorem rule28247 (p2027 p2191 p2528 p3692 p4355 p4629 : Prop) (h : (¬ p4629) ∨ (¬ p3692) ∨ (¬ p4355) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial28247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory17503 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule28247 (meaning t m 2027) (meaning t m 2191) (meaning t m 2528) (meaning t m 3692) (meaning t m 4355) (meaning t m 4629) source

theorem rule28249 (p2027 p2136 p2247 p2744 p3366 p3399 p3692 p4075 p4120 p4444 p4826 : Prop) (h : (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p4826) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4120) ∨ (¬ p2136)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p4075) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial28249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory17505 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule28249 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3692) (meaning t m 4075) (meaning t m 4120) (meaning t m 4444) (meaning t m 4826) source

theorem rule28251 (p2027 p2241 p2579 p2588 p3506 p3842 p4260 p4831 p5193 : Prop) (h : p2027 ∨ (¬ p3506) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3842) ∨ (¬ p4831) ∨ (¬ p4260) ∨ (¬ p2588) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial28251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory17507 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule28251 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 2588) (meaning t m 3506) (meaning t m 3842) (meaning t m 4260) (meaning t m 4831) (meaning t m 5193) source

theorem rule28252 (p2027 p2246 p2608 p2744 p2807 p3256 p3591 p3918 p4044 p4348 p4358 p4503 : Prop) (h : (¬ p2744) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p4348) ∨ (¬ p2608) ∨ (¬ p4358) ∨ (¬ p4044) ∨ (¬ p3591) ∨ (¬ p3918)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial28252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory17508 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 7) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28252 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2807) (meaning t m 3256) (meaning t m 3591) (meaning t m 3918) (meaning t m 4044) (meaning t m 4348) (meaning t m 4358) (meaning t m 4503) source

theorem rule28253 (p2027 p2780 p2881 p2901 p2946 p3822 p4107 p4666 p4786 : Prop) (h : (¬ p3822) ∨ (¬ p2780) ∨ (¬ p4107) ∨ (¬ p2946) ∨ (¬ p4786) ∨ (¬ p2901) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial28253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory17509 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28253 (meaning t m 2027) (meaning t m 2780) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3822) (meaning t m 4107) (meaning t m 4666) (meaning t m 4786) source

theorem rule28255 (p2027 p2241 p2641 p2911 p3323 p3551 p4278 p4621 p5193 p5197 : Prop) (h : p2027 ∨ (¬ p4621) ∨ (¬ p5197) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p2641) ∨ (¬ p3551) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p5193) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial28255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory17511 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule28255 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2911) (meaning t m 3323) (meaning t m 3551) (meaning t m 4278) (meaning t m 4621) (meaning t m 5193) (meaning t m 5197) source

theorem rule28256 (p1998 p2027 p2202 p2563 p2881 p2901 p3952 : Prop) (h : (¬ p2901) ∨ (¬ p1998) ∨ p2202 ∨ (¬ p3952) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial28256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory17512 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule28256 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2881) (meaning t m 2901) (meaning t m 3952) source

end SunPrize.SMT
