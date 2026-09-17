import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory056
import SunPrize.Certificate.Theory057
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule32123 (p2253 p2807 p3032 p4366 : Prop) (h : (¬ p3032) ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p4366)) : (¬ p2253) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial32123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory21379 (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 7)
  exact rule32123 (meaning t m 2253) (meaning t m 2807) (meaning t m 3032) (meaning t m 4366) source

theorem rule32125 (p2003 p2027 p2187 p2313 p2553 p2765 p3956 : Prop) (h : (¬ p3956) ∨ p2765 ∨ (¬ p2003) ∨ (¬ p2187) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2313)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (p2765) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial32125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory21381 t (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule32125 (meaning t m 2003) (meaning t m 2027) (meaning t m 2187) (meaning t m 2313) (meaning t m 2553) (meaning t m 2765) (meaning t m 3956) source

theorem rule32126 (p3661 p3878 p4700 : Prop) (h : (¬ p3661) ∨ (¬ p4700) ∨ p3878) : (¬ p3661) ∨ (p3878) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial32126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3661)) ∨ (meaning t m 3878) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory21382 (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule32126 (meaning t m 3661) (meaning t m 3878) (meaning t m 4700) source

theorem rule32132 (p2341 p3821 p3945 : Prop) (h : (¬ p3945) ∨ (¬ p2341) ∨ (¬ p3821)) : (¬ p2341) ∨ (¬ p3821) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial32132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory21388 (m.theta 0 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32132 (meaning t m 2341) (meaning t m 3821) (meaning t m 3945) source

theorem rule32134 (p2027 p2248 p2928 p3286 p3452 p3506 p4278 p4444 p4669 : Prop) (h : (¬ p3452) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p4669) ∨ (¬ p3286) ∨ (¬ p4278) ∨ (¬ p3506) ∨ p2027 ∨ (¬ p4444)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21390 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32134 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 3286) (meaning t m 3452) (meaning t m 3506) (meaning t m 4278) (meaning t m 4444) (meaning t m 4669) source

theorem rule32135 (p1980 p2027 p2307 p2622 p2743 p2779 p2829 p3568 : Prop) (h : (¬ p1980) ∨ p2027 ∨ p2622 ∨ (¬ p2307) ∨ (¬ p2829) ∨ (¬ p2743) ∨ (¬ p3568) ∨ (¬ p2779)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2307) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial32135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory21391 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule32135 (meaning t m 1980) (meaning t m 2027) (meaning t m 2307) (meaning t m 2622) (meaning t m 2743) (meaning t m 2779) (meaning t m 2829) (meaning t m 3568) source

theorem rule32140 (p2027 p2459 p2534 p2608 p2619 p2839 p3540 p4186 p4902 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2619) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p3540) ∨ (¬ p2608) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3540) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial32140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory21396 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32140 (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 3540) (meaning t m 4186) (meaning t m 4902) (meaning t m 5193) source

theorem rule32143 (p1990 p2027 p2156 p2396 p2997 p3556 p3690 : Prop) (h : (¬ p3690) ∨ (¬ p2396) ∨ (¬ p2156) ∨ (¬ p3556) ∨ p2027 ∨ p2997 ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial32143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory21399 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule32143 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2396) (meaning t m 2997) (meaning t m 3556) (meaning t m 3690) source

theorem rule32150 (p3878 p4194 p4196 : Prop) (h : (¬ p4196) ∨ (¬ p4194) ∨ p3878) : (p3878) ∨ (¬ p4194) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial32150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3878) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory21406 (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule32150 (meaning t m 3878) (meaning t m 4194) (meaning t m 4196) source

theorem rule32154 (p1976 p2027 p2534 p2688 p2951 p2992 p3051 p3055 p3246 p3367 p3950 p4242 p5369 : Prop) (h : (¬ p3950) ∨ (¬ p2951) ∨ (¬ p2534) ∨ (¬ p5369) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4242) ∨ (¬ p1976) ∨ (¬ p3367) ∨ p2688 ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3367) ∨ (¬ p3950) ∨ (¬ p4242) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial32154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory21410 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule32154 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) (meaning t m 3055) (meaning t m 3246) (meaning t m 3367) (meaning t m 3950) (meaning t m 4242) (meaning t m 5369) source

theorem rule32155 (p2352 p2668 p4389 : Prop) (h : (¬ p2668) ∨ (¬ p4389) ∨ p2352) : (p2352) ∨ (¬ p2668) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial32155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory21411 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule32155 (meaning t m 2352) (meaning t m 2668) (meaning t m 4389) source

theorem rule32159 (p1984 p2027 p2247 p2528 p3498 p4118 p4360 : Prop) (h : (¬ p1984) ∨ (¬ p2247) ∨ p2027 ∨ p3498 ∨ (¬ p2528) ∨ (¬ p4118) ∨ (¬ p4360)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2528) ∨ (p3498) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial32159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory21415 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule32159 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2528) (meaning t m 3498) (meaning t m 4118) (meaning t m 4360) source

theorem rule32162 (p2027 p2137 p2156 p2187 p2748 p2839 p2996 p3365 p3553 p4133 p4734 : Prop) (h : (¬ p3365) ∨ (¬ p3553) ∨ (¬ p2996) ∨ (¬ p2839) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p4734) ∨ (¬ p2748)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial32162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory21418 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule32162 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2187) (meaning t m 2748) (meaning t m 2839) (meaning t m 2996) (meaning t m 3365) (meaning t m 3553) (meaning t m 4133) (meaning t m 4734) source

theorem rule32170 (p2027 p2459 p3266 p4322 p4335 p4902 : Prop) (h : p2027 ∨ (¬ p2459) ∨ (¬ p4335) ∨ (¬ p4902) ∨ (¬ p4322) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial32170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory21426 t (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule32170 (meaning t m 2027) (meaning t m 2459) (meaning t m 3266) (meaning t m 4322) (meaning t m 4335) (meaning t m 4902) source

theorem rule32178 (p1997 p2027 p2169 p2363 p2406 p2509 p2534 : Prop) (h : p2169 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2509)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534) := by
  classical
  tauto

theorem initial32178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) := by
  have source := ElevenTheory.theory21434 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32178 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2406) (meaning t m 2509) (meaning t m 2534) source

theorem rule32182 (p2850 p4449 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p4449) ∨ (¬ p2850)) : (¬ p2850) ∨ (¬ p4449) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial32182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4449)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory21438 (m.theta 2 4) (m.theta 4 5) (m.theta 4 9)
  exact rule32182 (meaning t m 2850) (meaning t m 4449) (meaning t m 5160) source

theorem rule32183 (p2383 p3319 p3990 p5016 : Prop) (h : (¬ p3990) ∨ (¬ p5016) ∨ (¬ p2383) ∨ p3319) : (¬ p2383) ∨ (p3319) ∨ (¬ p3990) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial32183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (meaning t m 3319) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory21439 (m.theta 0 6) (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule32183 (meaning t m 2383) (meaning t m 3319) (meaning t m 3990) (meaning t m 5016) source

theorem rule32186 (p2027 p2542 p2589 p2608 p3309 p3574 p3822 p4869 p5193 p5222 : Prop) (h : (¬ p3822) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p4869) ∨ (¬ p3309) ∨ (¬ p5222)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3822) ∨ (¬ p4869) ∨ (¬ p5193) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial32186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory21442 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule32186 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2608) (meaning t m 3309) (meaning t m 3574) (meaning t m 3822) (meaning t m 4869) (meaning t m 5193) (meaning t m 5222) source

theorem rule32187 (p2002 p2027 p2169 p3822 p3872 p3989 p4129 p4260 : Prop) (h : (¬ p3872) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p4260) ∨ (¬ p2002) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4129)) : (¬ p2002) ∨ (p2027) ∨ (p2169) ∨ (¬ p3822) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4129) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial32187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory21443 t (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule32187 (meaning t m 2002) (meaning t m 2027) (meaning t m 2169) (meaning t m 3822) (meaning t m 3872) (meaning t m 3989) (meaning t m 4129) (meaning t m 4260) source

theorem rule32192 (p2027 p2246 p2608 p2744 p2901 p2946 p3246 p3548 p4366 p4668 : Prop) (h : (¬ p2744) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2608) ∨ (¬ p3548) ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p2246) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial32192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory21448 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32192 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3548) (meaning t m 4366) (meaning t m 4668) source

theorem rule32201 (p2027 p2383 p2497 p2578 p3422 p3923 p5214 : Prop) (h : (¬ p5214) ∨ (¬ p2578) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p3422) ∨ (¬ p2497)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3923) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial32201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory21457 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule32201 (meaning t m 2027) (meaning t m 2383) (meaning t m 2497) (meaning t m 2578) (meaning t m 3422) (meaning t m 3923) (meaning t m 5214) source

theorem rule32203 (p2027 p2192 p2210 p3425 p3737 p4324 p4381 p4736 p5250 : Prop) (h : (¬ p4381) ∨ (¬ p3425) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p4324) ∨ (¬ p2210) ∨ (¬ p5250) ∨ (¬ p3737)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3425) ∨ (¬ p3737) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial32203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory21459 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule32203 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 3425) (meaning t m 3737) (meaning t m 4324) (meaning t m 4381) (meaning t m 4736) (meaning t m 5250) source

theorem rule32204 (p1988 p2027 p2409 p3073 p3266 p3449 p3452 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p3452) ∨ (¬ p1988) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2409) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial32204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory21460 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 8 9) (m.theta 9 10)
  exact rule32204 (meaning t m 1988) (meaning t m 2027) (meaning t m 2409) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 3452) source

theorem rule32206 (p2027 p3325 p3570 p3979 p4556 p5558 : Prop) (h : (¬ p3325) ∨ (¬ p3979) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p5558)) : (p2027) ∨ (¬ p3325) ∨ (¬ p3570) ∨ (¬ p3979) ∨ (¬ p4556) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21462 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule32206 (meaning t m 2027) (meaning t m 3325) (meaning t m 3570) (meaning t m 3979) (meaning t m 4556) (meaning t m 5558) source

theorem rule32208 (p2027 p2299 p2588 p3564 p4623 p4668 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p4623) ∨ (¬ p3564) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4623) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial32208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory21464 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule32208 (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 3564) (meaning t m 4623) (meaning t m 4668) source

theorem rule32212 (p2027 p2246 p2528 p2608 p2651 p2744 p3083 p3591 p4026 p4604 : Prop) (h : (¬ p3591) ∨ (¬ p3083) ∨ (¬ p2608) ∨ (¬ p2528) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p4026) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial32212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory21468 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule32212 (meaning t m 2027) (meaning t m 2246) (meaning t m 2528) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) source

theorem rule32214 (p2027 p2363 p3857 p3961 p4063 p4138 p5564 : Prop) (h : (¬ p4138) ∨ (¬ p5564) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p3857) ∨ (¬ p4063) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4063) ∨ (¬ p4138) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial32214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory21470 t (m.theta 0 7) (m.theta 0 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule32214 (meaning t m 2027) (meaning t m 2363) (meaning t m 3857) (meaning t m 3961) (meaning t m 4063) (meaning t m 4138) (meaning t m 5564) source

theorem rule32216 (p2027 p2156 p2373 p3588 p3659 p3954 p4110 p4133 p4441 p4521 : Prop) (h : (¬ p4133) ∨ (¬ p3954) ∨ (¬ p3659) ∨ (¬ p4441) ∨ (¬ p4521) ∨ (¬ p4110) ∨ (¬ p3588) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2373)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial32216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory21472 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule32216 (meaning t m 2027) (meaning t m 2156) (meaning t m 2373) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4110) (meaning t m 4133) (meaning t m 4441) (meaning t m 4521) source

theorem rule32219 (p2027 p2145 p2807 p3461 p3572 p3646 p3755 p4117 p4205 p4322 p5276 : Prop) (h : (¬ p4205) ∨ (¬ p4117) ∨ (¬ p3461) ∨ (¬ p4322) ∨ (¬ p5276) ∨ (¬ p3646) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p2145) ∨ (¬ p2807) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2807) ∨ (¬ p3461) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p5276) := by
  classical
  tauto

theorem initial32219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4205)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5276)) := by
  have source := ElevenTheory.theory21475 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule32219 (meaning t m 2027) (meaning t m 2145) (meaning t m 2807) (meaning t m 3461) (meaning t m 3572) (meaning t m 3646) (meaning t m 3755) (meaning t m 4117) (meaning t m 4205) (meaning t m 4322) (meaning t m 5276) source

theorem rule32220 (p1989 p2027 p2210 p2764 p3591 p3744 p3957 p4191 : Prop) (h : p2764 ∨ (¬ p3957) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p2210) ∨ (¬ p1989) ∨ (¬ p4191)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2764) ∨ (¬ p3591) ∨ (¬ p3744) ∨ (¬ p3957) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial32220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory21476 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule32220 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2764) (meaning t m 3591) (meaning t m 3744) (meaning t m 3957) (meaning t m 4191) source

theorem rule32225 (p2027 p2136 p2387 p2663 p2819 p3343 p3389 p3742 p3744 p4198 p4428 p4786 p5322 : Prop) (h : (¬ p2387) ∨ (¬ p4428) ∨ (¬ p3744) ∨ (¬ p2136) ∨ (¬ p5322) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2663) ∨ (¬ p3742) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p4786) ∨ (¬ p4198)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2387) ∨ (¬ p2663) ∨ (¬ p2819) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p4786) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial32225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory21481 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule32225 (meaning t m 2027) (meaning t m 2136) (meaning t m 2387) (meaning t m 2663) (meaning t m 2819) (meaning t m 3343) (meaning t m 3389) (meaning t m 3742) (meaning t m 3744) (meaning t m 4198) (meaning t m 4428) (meaning t m 4786) (meaning t m 5322) source

theorem rule32227 (p2027 p3737 p3989 p4503 p5558 p5584 : Prop) (h : (¬ p3989) ∨ (¬ p5584) ∨ (¬ p3737) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p5558)) : (p2027) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p5558) ∨ (¬ p5584) := by
  classical
  tauto

theorem initial32227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5558)) ∨ (¬ (meaning t m 5584)) := by
  have source := ElevenTheory.theory21483 t (m.theta 5 6) (m.theta 6 10) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule32227 (meaning t m 2027) (meaning t m 3737) (meaning t m 3989) (meaning t m 4503) (meaning t m 5558) (meaning t m 5584) source

theorem rule32229 (p2027 p2132 p2753 p2870 p3246 p3379 p3548 p4366 p4668 p5216 : Prop) (h : (¬ p3379) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3548) ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p2132) ∨ (¬ p3246) ∨ (¬ p4668) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21485 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32229 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3379) (meaning t m 3548) (meaning t m 4366) (meaning t m 4668) (meaning t m 5216) source

theorem rule32231 (p2027 p2657 p2727 p2749 p3361 p4242 p4964 : Prop) (h : (¬ p4964) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4242) ∨ (¬ p2749) ∨ (¬ p3361) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3361) ∨ (¬ p4242) ∨ (¬ p4964) := by
  classical
  tauto

theorem initial32231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4964)) := by
  have source := ElevenTheory.theory21487 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4)
  exact rule32231 (meaning t m 2027) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) (meaning t m 3361) (meaning t m 4242) (meaning t m 4964) source

theorem rule32232 (p2027 p2619 p3744 p3758 p4441 p4601 : Prop) (h : (¬ p4441) ∨ (¬ p3758) ∨ (¬ p2619) ∨ (¬ p4601) ∨ p2027 ∨ (¬ p3744)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4441) ∨ (¬ p4601) := by
  classical
  tauto

theorem initial32232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4601)) := by
  have source := ElevenTheory.theory21488 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9)
  exact rule32232 (meaning t m 2027) (meaning t m 2619) (meaning t m 3744) (meaning t m 3758) (meaning t m 4441) (meaning t m 4601) source

theorem rule32233 (p2533 p2619 p4385 : Prop) (h : (¬ p2619) ∨ (¬ p4385) ∨ (¬ p2533)) : (¬ p2533) ∨ (¬ p2619) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial32233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory21489 (m.theta 2 5) (m.theta 5 8) (m.theta 5 9)
  exact rule32233 (meaning t m 2533) (meaning t m 2619) (meaning t m 4385) source

theorem rule32235 (p1987 p2027 p2764 p2807 p3292 p3572 p5284 : Prop) (h : p2027 ∨ (¬ p2807) ∨ (¬ p3292) ∨ p2764 ∨ (¬ p1987) ∨ (¬ p5284) ∨ (¬ p3572)) : (¬ p1987) ∨ (p2027) ∨ (p2764) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3572) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial32235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory21491 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 9 10)
  exact rule32235 (meaning t m 1987) (meaning t m 2027) (meaning t m 2764) (meaning t m 2807) (meaning t m 3292) (meaning t m 3572) (meaning t m 5284) source

theorem rule32236 (p1977 p2027 p2331 p2766 p2811 p3877 p4154 p4347 p4769 : Prop) (h : (¬ p2811) ∨ (¬ p4769) ∨ (¬ p3877) ∨ (¬ p2331) ∨ (¬ p4347) ∨ (¬ p1977) ∨ (¬ p4154) ∨ p2766 ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2766) ∨ (¬ p2811) ∨ (¬ p3877) ∨ (¬ p4154) ∨ (¬ p4347) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial32236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory21492 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32236 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2766) (meaning t m 2811) (meaning t m 3877) (meaning t m 4154) (meaning t m 4347) (meaning t m 4769) source

theorem rule32242 (p2027 p2417 p3201 p3947 p4112 p4753 : Prop) (h : (¬ p4112) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p3201) ∨ (¬ p2417) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial32242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory21498 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule32242 (meaning t m 2027) (meaning t m 2417) (meaning t m 3201) (meaning t m 3947) (meaning t m 4112) (meaning t m 4753) source

theorem rule32248 (p1983 p2027 p2202 p2299 p2319 p2341 p2396 p2563 p3743 : Prop) (h : (¬ p1983) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p2299) ∨ (¬ p2319) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2341) ∨ (¬ p3743)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial32248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory21504 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32248 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2396) (meaning t m 2563) (meaning t m 3743) source

theorem rule32250 (p2027 p2255 p2651 p2928 p3016 p3402 p3920 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3920) ∨ (¬ p3402) ∨ (¬ p2651) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2928) ∨ (¬ p3016) ∨ (¬ p3402) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial32250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory21506 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule32250 (meaning t m 2027) (meaning t m 2255) (meaning t m 2651) (meaning t m 2928) (meaning t m 3016) (meaning t m 3402) (meaning t m 3920) source

theorem rule32252 (p2027 p2608 p3333 p3367 p3646 p3989 p4332 p4347 p4524 : Prop) (h : (¬ p4347) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p4332) ∨ (¬ p3367) ∨ (¬ p4524) ∨ (¬ p3333)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial32252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory21508 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule32252 (meaning t m 2027) (meaning t m 2608) (meaning t m 3333) (meaning t m 3367) (meaning t m 3646) (meaning t m 3989) (meaning t m 4332) (meaning t m 4347) (meaning t m 4524) source

theorem rule32257 (p1982 p2027 p2202 p2427 p2957 p3146 p3156 p3556 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p2957) ∨ (¬ p3156) ∨ (¬ p1982) ∨ p2202 ∨ (¬ p3146) ∨ (¬ p2427)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial32257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory21513 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule32257 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2957) (meaning t m 3146) (meaning t m 3156) (meaning t m 3556) source

theorem rule32263 (p2952 p3286 p4314 : Prop) (h : (¬ p3286) ∨ (¬ p2952) ∨ (¬ p4314)) : (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4314) := by
  classical
  tauto

theorem initial32263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4314)) := by
  have source := ElevenTheory.theory21519 (m.theta 0 3) (m.theta 3 5) (m.theta 3 9)
  exact rule32263 (meaning t m 2952) (meaning t m 3286) (meaning t m 4314) source

theorem rule32264 (p2027 p2440 p2774 p3055 p4343 p4390 p4717 : Prop) (h : p2027 ∨ (¬ p3055) ∨ (¬ p4390) ∨ (¬ p2440) ∨ (¬ p4717) ∨ (¬ p4343) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p4390) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial32264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory21520 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule32264 (meaning t m 2027) (meaning t m 2440) (meaning t m 2774) (meaning t m 3055) (meaning t m 4343) (meaning t m 4390) (meaning t m 4717) source

theorem rule32265 (p2144 p3820 p4984 : Prop) (h : (¬ p3820) ∨ (¬ p2144) ∨ p4984) : (¬ p2144) ∨ (¬ p3820) ∨ (p4984) := by
  classical
  tauto

theorem initial32265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3820)) ∨ (meaning t m 4984) := by
  have source := ElevenTheory.theory21521 (m.theta 0 2) (m.theta 0 5) (m.theta 0 7)
  exact rule32265 (meaning t m 2144) (meaning t m 3820) (meaning t m 4984) source

theorem rule32267 (p1998 p2027 p2528 p2997 p3063 p3097 p3957 p4348 p4432 : Prop) (h : (¬ p3063) ∨ p2027 ∨ (¬ p3957) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p1998) ∨ (¬ p4432) ∨ (¬ p2528) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2528) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3097) ∨ (¬ p3957) ∨ (¬ p4348) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial32267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory21523 t (m.theta 1 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32267 (meaning t m 1998) (meaning t m 2027) (meaning t m 2528) (meaning t m 2997) (meaning t m 3063) (meaning t m 3097) (meaning t m 3957) (meaning t m 4348) (meaning t m 4432) source

theorem rule32268 (p2027 p2177 p3297 p3506 p3960 p4322 p4402 p4461 p4556 : Prop) (h : (¬ p3960) ∨ (¬ p4461) ∨ p2027 ∨ (¬ p4402) ∨ (¬ p4556) ∨ (¬ p3297) ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3297) ∨ (¬ p3506) ∨ (¬ p3960) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4461) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial32268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4461)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory21524 t (m.theta 0 8) (m.theta 0 9) (m.theta 3 9) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 9 10)
  exact rule32268 (meaning t m 2027) (meaning t m 2177) (meaning t m 3297) (meaning t m 3506) (meaning t m 3960) (meaning t m 4322) (meaning t m 4402) (meaning t m 4461) (meaning t m 4556) source

theorem rule32270 (p2027 p2315 p3325 p3551 p3979 p5558 : Prop) (h : (¬ p3979) ∨ (¬ p3325) ∨ (¬ p5558) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2315)) : (p2027) ∨ (¬ p2315) ∨ (¬ p3325) ∨ (¬ p3551) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21526 t (m.theta 0 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule32270 (meaning t m 2027) (meaning t m 2315) (meaning t m 3325) (meaning t m 3551) (meaning t m 3979) (meaning t m 5558) source

theorem rule32271 (p1990 p2027 p2241 p2641 p2668 p2699 p3989 : Prop) (h : (¬ p1990) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ p2699 ∨ p2027 ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (p2699) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial32271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory21527 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule32271 (meaning t m 1990) (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2668) (meaning t m 2699) (meaning t m 3989) source

theorem rule32275 (p2027 p2619 p3582 p3584 p3880 p4715 : Prop) (h : (¬ p3880) ∨ (¬ p3582) ∨ (¬ p2619) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4715)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p3880) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial32275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory21531 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule32275 (meaning t m 2027) (meaning t m 2619) (meaning t m 3582) (meaning t m 3584) (meaning t m 3880) (meaning t m 4715) source

theorem rule32278 (p2027 p2441 p2870 p3516 p3691 p4278 p4885 : Prop) (h : (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p4885) ∨ (¬ p4278) ∨ (¬ p3691) ∨ p2027) : (p2027) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p4278) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial32278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory21534 t (m.theta 0 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule32278 (meaning t m 2027) (meaning t m 2441) (meaning t m 2870) (meaning t m 3516) (meaning t m 3691) (meaning t m 4278) (meaning t m 4885) source

theorem rule32280 (p3146 p3690 p3747 p4445 : Prop) (h : (¬ p4445) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p3690)) : (¬ p3146) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial32280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory21536 (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32280 (meaning t m 3146) (meaning t m 3690) (meaning t m 3747) (meaning t m 4445) source

theorem rule32281 (p1980 p2027 p2318 p2417 p2633 p3568 p3570 p3821 p4001 : Prop) (h : (¬ p3821) ∨ (¬ p4001) ∨ (¬ p2318) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p1980) ∨ p2633 ∨ (¬ p2417) ∨ (¬ p3570)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2318) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial32281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory21537 t (m.theta 0 7) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32281 (meaning t m 1980) (meaning t m 2027) (meaning t m 2318) (meaning t m 2417) (meaning t m 2633) (meaning t m 3568) (meaning t m 3570) (meaning t m 3821) (meaning t m 4001) source

theorem rule32282 (p1998 p2027 p2138 p2177 p2774 p3309 p3474 p3918 : Prop) (h : (¬ p1998) ∨ (¬ p2177) ∨ p3474 ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3918) ∨ (¬ p3309) ∨ (¬ p2774)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (p3474) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial32282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3309)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory21538 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule32282 (meaning t m 1998) (meaning t m 2027) (meaning t m 2138) (meaning t m 2177) (meaning t m 2774) (meaning t m 3309) (meaning t m 3474) (meaning t m 3918) source

theorem rule32283 (p1999 p2027 p2132 p2611 p2829 p3125 p3583 p4185 : Prop) (h : p2611 ∨ (¬ p1999) ∨ (¬ p3125) ∨ (¬ p4185) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p2132)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2829) ∨ (¬ p3125) ∨ (¬ p3583) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial32283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory21539 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule32283 (meaning t m 1999) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2829) (meaning t m 3125) (meaning t m 3583) (meaning t m 4185) source

theorem rule32285 (p2027 p2573 p3362 p3365 p3584 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p3365) ∨ (¬ p3584) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p2573)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3584) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial32285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory21541 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule32285 (meaning t m 2027) (meaning t m 2573) (meaning t m 3362) (meaning t m 3365) (meaning t m 3584) (meaning t m 4752) source

theorem rule32288 (p1998 p2027 p2284 p2388 p2881 p3051 p3646 : Prop) (h : (¬ p2881) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3051) ∨ p2388 ∨ (¬ p3646)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial32288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory21544 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule32288 (meaning t m 1998) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 2881) (meaning t m 3051) (meaning t m 3646) source

theorem rule32289 (p2027 p2210 p2254 p2657 p2881 p2891 p3574 p3956 p4503 : Prop) (h : (¬ p3956) ∨ (¬ p4503) ∨ (¬ p2657) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3574) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial32289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory21545 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32289 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2881) (meaning t m 2891) (meaning t m 3574) (meaning t m 3956) (meaning t m 4503) source

theorem rule32292 (p3692 p4132 p4348 : Prop) (h : (¬ p4132) ∨ (¬ p4348) ∨ p3692) : (p3692) ∨ (¬ p4132) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial32292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory21548 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32292 (meaning t m 3692) (meaning t m 4132) (meaning t m 4348) source

theorem rule32297 (p2027 p2177 p2247 p2553 p2573 p2608 p3519 p4041 p4360 p4376 : Prop) (h : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p4360) ∨ (¬ p4041) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4376) ∨ (¬ p2608) ∨ (¬ p2247) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial32297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory21553 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule32297 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2553) (meaning t m 2573) (meaning t m 2608) (meaning t m 3519) (meaning t m 4041) (meaning t m 4360) (meaning t m 4376) source

theorem rule32299 (p2088 p2475 p4340 p5373 : Prop) (h : (¬ p4340) ∨ (¬ p2475) ∨ (¬ p2088) ∨ (¬ p5373)) : (¬ p2088) ∨ (¬ p2475) ∨ (¬ p4340) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial32299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory21555 (m.theta 0 8) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule32299 (meaning t m 2088) (meaning t m 2475) (meaning t m 4340) (meaning t m 5373) source

theorem rule32300 (p2027 p2191 p2248 p2331 p3555 p3692 p3755 p4195 p5109 : Prop) (h : (¬ p2331) ∨ (¬ p2248) ∨ (¬ p5109) ∨ (¬ p3555) ∨ (¬ p2191) ∨ (¬ p3692) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p4195)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial32300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory21556 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9)
  exact rule32300 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2331) (meaning t m 3555) (meaning t m 3692) (meaning t m 3755) (meaning t m 4195) (meaning t m 5109) source

theorem rule32304 (p2027 p2254 p2363 p2608 p2707 p2717 p3172 p4118 p4503 : Prop) (h : (¬ p2707) ∨ (¬ p3172) ∨ (¬ p4503) ∨ (¬ p2608) ∨ (¬ p4118) ∨ (¬ p2717) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial32304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory21560 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32304 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3172) (meaning t m 4118) (meaning t m 4503) source

theorem rule32305 (p1987 p2027 p2098 p2737 p2780 p3586 p4242 : Prop) (h : p3586 ∨ (¬ p2098) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2780) ∨ (¬ p4242) ∨ (¬ p2737)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (p3586) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial32305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory21561 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8)
  exact rule32305 (meaning t m 1987) (meaning t m 2027) (meaning t m 2098) (meaning t m 2737) (meaning t m 2780) (meaning t m 3586) (meaning t m 4242) source

theorem rule32307 (p1986 p2027 p2406 p2545 p2579 p3016 p3347 p3684 : Prop) (h : (¬ p3347) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p3684) ∨ (¬ p1986) ∨ (¬ p2579) ∨ p2545 ∨ (¬ p3016)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2406) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3347) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial32307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory21563 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule32307 (meaning t m 1986) (meaning t m 2027) (meaning t m 2406) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) (meaning t m 3347) (meaning t m 3684) source

theorem rule32309 (p1983 p2027 p2210 p2699 p2972 p3680 p4381 : Prop) (h : p2699 ∨ (¬ p1983) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p3680)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial32309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory21565 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule32309 (meaning t m 1983) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2972) (meaning t m 3680) (meaning t m 4381) source

theorem rule32310 (p2027 p3506 p4107 p4361 p4425 p4451 p4661 : Prop) (h : (¬ p4361) ∨ (¬ p4107) ∨ (¬ p3506) ∨ p2027 ∨ (¬ p4661) ∨ (¬ p4451) ∨ (¬ p4425)) : (p2027) ∨ (¬ p3506) ∨ (¬ p4107) ∨ (¬ p4361) ∨ (¬ p4425) ∨ (¬ p4451) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial32310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory21566 t (m.theta 3 7) (m.theta 3 9) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule32310 (meaning t m 2027) (meaning t m 3506) (meaning t m 4107) (meaning t m 4361) (meaning t m 4425) (meaning t m 4451) (meaning t m 4661) source

theorem rule32315 (p2027 p2254 p2608 p2819 p2829 p2952 p3570 p4133 p4320 : Prop) (h : (¬ p2819) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4320) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial32315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory21571 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32315 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 2952) (meaning t m 3570) (meaning t m 4133) (meaning t m 4320) source

theorem rule32316 (p2027 p2254 p2952 p3093 p3319 p3461 p4320 p4831 p5660 : Prop) (h : (¬ p2254) ∨ (¬ p4831) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p5660) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3319) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p4320) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial32316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory21572 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule32316 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 4320) (meaning t m 4831) (meaning t m 5660) source

theorem rule32317 (p2006 p2027 p3128 p3156 p3694 p3744 p3952 : Prop) (h : (¬ p2006) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3694) ∨ (¬ p3156) ∨ (¬ p3952) ∨ p3128) : (¬ p2006) ∨ (p2027) ∨ (p3128) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p3744) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial32317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory21573 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 9)
  exact rule32317 (meaning t m 2006) (meaning t m 2027) (meaning t m 3128) (meaning t m 3156) (meaning t m 3694) (meaning t m 3744) (meaning t m 3952) source

theorem rule32322 (p2027 p2386 p2437 p3569 p3574 p4140 p4435 p5016 p5472 : Prop) (h : (¬ p4140) ∨ (¬ p3569) ∨ (¬ p5472) ∨ (¬ p2386) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3574) ∨ (¬ p5016) ∨ (¬ p4435)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2437) ∨ (¬ p3569) ∨ (¬ p3574) ∨ (¬ p4140) ∨ (¬ p4435) ∨ (¬ p5016) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial32322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory21578 t (m.theta 0 6) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7)
  exact rule32322 (meaning t m 2027) (meaning t m 2386) (meaning t m 2437) (meaning t m 3569) (meaning t m 3574) (meaning t m 4140) (meaning t m 4435) (meaning t m 5016) (meaning t m 5472) source

theorem rule32324 (p1990 p2027 p2545 p2797 p2810 p2963 p3093 p3097 p3309 p3366 p3452 p4236 p4376 : Prop) (h : (¬ p2963) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p4376) ∨ (¬ p2797) ∨ (¬ p3093) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p1990) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4236) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial32324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory21580 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule32324 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 2963) (meaning t m 3093) (meaning t m 3097) (meaning t m 3309) (meaning t m 3366) (meaning t m 3452) (meaning t m 4236) (meaning t m 4376) source

theorem rule32325 (p2027 p3055 p3146 p3366 p3449 p3555 p3584 p4137 p4377 p4446 p4604 : Prop) (h : (¬ p4377) ∨ (¬ p3584) ∨ (¬ p3055) ∨ (¬ p4446) ∨ (¬ p3555) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p4137) ∨ (¬ p3146) ∨ (¬ p3366)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial32325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory21581 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule32325 (meaning t m 2027) (meaning t m 3055) (meaning t m 3146) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3584) (meaning t m 4137) (meaning t m 4377) (meaning t m 4446) (meaning t m 4604) source

theorem rule32327 (p2667 p3292 p3987 p4421 : Prop) (h : (¬ p3987) ∨ (¬ p2667) ∨ (¬ p4421) ∨ (¬ p3292)) : (¬ p2667) ∨ (¬ p3292) ∨ (¬ p3987) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial32327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory21583 (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 3 9)
  exact rule32327 (meaning t m 2667) (meaning t m 3292) (meaning t m 3987) (meaning t m 4421) source

theorem rule32328 (p2027 p2246 p2331 p2363 p2608 p2668 p2744 p3817 p4366 p4669 : Prop) (h : p2027 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p4366) ∨ (¬ p2363) ∨ (¬ p2744) ∨ (¬ p3817) ∨ (¬ p2668) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21584 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32328 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2608) (meaning t m 2668) (meaning t m 2744) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule32330 (p1997 p2027 p2169 p3483 p3986 p4037 p4110 p4358 : Prop) (h : (¬ p4037) ∨ p2027 ∨ p2169 ∨ (¬ p4358) ∨ (¬ p3483) ∨ (¬ p3986) ∨ (¬ p1997) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p3483) ∨ (¬ p3986) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial32330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory21586 t (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule32330 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 3483) (meaning t m 3986) (meaning t m 4037) (meaning t m 4110) (meaning t m 4358) source

theorem rule32332 (p2027 p2417 p3553 p3579 p4403 p4443 p5118 p5590 : Prop) (h : (¬ p3579) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p5590) ∨ (¬ p5118) ∨ (¬ p4443) ∨ (¬ p3553) ∨ (¬ p4403)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3553) ∨ (¬ p3579) ∨ (¬ p4403) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial32332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory21588 t (m.theta 0 8) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule32332 (meaning t m 2027) (meaning t m 2417) (meaning t m 3553) (meaning t m 3579) (meaning t m 4403) (meaning t m 4443) (meaning t m 5118) (meaning t m 5590) source

theorem rule32334 (p2027 p3276 p4208 p4321 p4387 p4449 p4702 : Prop) (h : (¬ p4449) ∨ (¬ p4208) ∨ (¬ p4321) ∨ (¬ p4387) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p3276)) : (p2027) ∨ (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4321) ∨ (¬ p4387) ∨ (¬ p4449) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial32334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4449)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory21590 t (m.theta 1 9) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule32334 (meaning t m 2027) (meaning t m 3276) (meaning t m 4208) (meaning t m 4321) (meaning t m 4387) (meaning t m 4449) (meaning t m 4702) source

theorem rule32335 (p2027 p2449 p2534 p2685 p2696 p2753 p3379 p3860 p3950 p4370 p5216 : Prop) (h : (¬ p4370) ∨ (¬ p2534) ∨ (¬ p3950) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2685) ∨ (¬ p3860) ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4370) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21591 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32335 (meaning t m 2027) (meaning t m 2449) (meaning t m 2534) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3379) (meaning t m 3860) (meaning t m 3950) (meaning t m 4370) (meaning t m 5216) source

theorem rule32336 (p2027 p2248 p2363 p2663 p3083 p3389 p3683 p3860 p3876 p4261 p4596 : Prop) (h : (¬ p4261) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p3683) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p4596) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2663) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3683) ∨ (¬ p3860) ∨ (¬ p3876) ∨ (¬ p4261) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial32336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory21592 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 8) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32336 (meaning t m 2027) (meaning t m 2248) (meaning t m 2363) (meaning t m 2663) (meaning t m 3083) (meaning t m 3389) (meaning t m 3683) (meaning t m 3860) (meaning t m 3876) (meaning t m 4261) (meaning t m 4596) source

theorem rule32339 (p2027 p2341 p3553 p3572 p4104 p4790 : Prop) (h : (¬ p3572) ∨ (¬ p4790) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p4104) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4104) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial32339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory21595 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule32339 (meaning t m 2027) (meaning t m 2341) (meaning t m 3553) (meaning t m 3572) (meaning t m 4104) (meaning t m 4790) source

theorem rule32348 (p2027 p2132 p2187 p2753 p2860 p2927 p3379 p3644 p4133 p4366 p5216 : Prop) (h : p2027 ∨ (¬ p5216) ∨ (¬ p4133) ∨ (¬ p2860) ∨ (¬ p2753) ∨ (¬ p2132) ∨ (¬ p3379) ∨ (¬ p2187) ∨ (¬ p2927) ∨ (¬ p3644) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4366) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21604 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule32348 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2753) (meaning t m 2860) (meaning t m 2927) (meaning t m 3379) (meaning t m 3644) (meaning t m 4133) (meaning t m 4366) (meaning t m 5216) source

theorem rule32351 (p2027 p3073 p3857 p4113 p4317 p4358 p4871 : Prop) (h : (¬ p3857) ∨ (¬ p3073) ∨ (¬ p4317) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4113) ∨ (¬ p4871)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4317) ∨ (¬ p4358) ∨ (¬ p4871) := by
  classical
  tauto

theorem initial32351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4871)) := by
  have source := ElevenTheory.theory21607 t (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule32351 (meaning t m 2027) (meaning t m 3073) (meaning t m 3857) (meaning t m 4113) (meaning t m 4317) (meaning t m 4358) (meaning t m 4871) source

theorem rule32354 (p3773 p4233 p5387 : Prop) (h : (¬ p3773) ∨ (¬ p4233) ∨ p5387) : (¬ p3773) ∨ (¬ p4233) ∨ (p5387) := by
  classical
  tauto

theorem initial32354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4233)) ∨ (meaning t m 5387) := by
  have source := ElevenTheory.theory21610 (m.theta 0 9) (m.theta 2 9) (m.theta 9 10)
  exact rule32354 (meaning t m 3773) (meaning t m 4233) (meaning t m 5387) source

theorem rule32356 (p2027 p3654 p3987 p4037 p4195 p4790 : Prop) (h : (¬ p4790) ∨ (¬ p3987) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p3654)) : (p2027) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial32356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory21612 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9)
  exact rule32356 (meaning t m 2027) (meaning t m 3654) (meaning t m 3987) (meaning t m 4037) (meaning t m 4195) (meaning t m 4790) source

theorem rule32357 (p1981 p2027 p2114 p2187 p2829 p3483 p3744 : Prop) (h : (¬ p3744) ∨ (¬ p1981) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2829) ∨ p2114 ∨ (¬ p3483)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2187) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial32357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory21613 t (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule32357 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2187) (meaning t m 2829) (meaning t m 3483) (meaning t m 3744) source

theorem rule32359 (p1977 p2027 p2462 p2946 p3414 p3662 p3947 : Prop) (h : p2027 ∨ (¬ p3662) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p1977) ∨ p2462 ∨ (¬ p3947)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial32359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory21615 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule32359 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2946) (meaning t m 3414) (meaning t m 3662) (meaning t m 3947) source

theorem rule32360 (p2000 p2027 p3201 p3540 p3874 p3982 p4383 p5558 : Prop) (h : (¬ p3540) ∨ (¬ p2000) ∨ (¬ p3874) ∨ (¬ p3201) ∨ p2027 ∨ p3982 ∨ (¬ p5558) ∨ (¬ p4383)) : (¬ p2000) ∨ (p2027) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (p3982) ∨ (¬ p4383) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21616 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10)
  exact rule32360 (meaning t m 2000) (meaning t m 2027) (meaning t m 3201) (meaning t m 3540) (meaning t m 3874) (meaning t m 3982) (meaning t m 4383) (meaning t m 5558) source

theorem rule32364 (p2027 p2470 p2528 p3365 p3553 p3572 p3692 p4079 p4736 p4902 : Prop) (h : (¬ p3572) ∨ (¬ p4736) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4902) ∨ (¬ p4079) ∨ (¬ p2470) ∨ (¬ p3692) ∨ p2027) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3692) ∨ (¬ p4079) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial32364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory21620 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32364 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 3692) (meaning t m 4079) (meaning t m 4736) (meaning t m 4902) source

theorem rule32365 (p2027 p2241 p2630 p2748 p3032 p4366 p4650 : Prop) (h : (¬ p4366) ∨ (¬ p2748) ∨ (¬ p4650) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3032)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3032) ∨ (¬ p4366) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial32365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory21621 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule32365 (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2748) (meaning t m 3032) (meaning t m 4366) (meaning t m 4650) source

theorem rule32371 (p2027 p2307 p2578 p3791 p3956 p4138 p5564 : Prop) (h : p2027 ∨ (¬ p4138) ∨ (¬ p2578) ∨ (¬ p5564) ∨ (¬ p2307) ∨ (¬ p3791) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3791) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial32371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory21627 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule32371 (meaning t m 2027) (meaning t m 2307) (meaning t m 2578) (meaning t m 3791) (meaning t m 3956) (meaning t m 4138) (meaning t m 5564) source

theorem rule32372 (p2341 p2717 p3577 : Prop) (h : (¬ p3577) ∨ (¬ p2341) ∨ p2717) : (¬ p2341) ∨ (p2717) ∨ (¬ p3577) := by
  classical
  tauto

theorem initial32372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (meaning t m 2717) ∨ (¬ (meaning t m 3577)) := by
  have source := ElevenTheory.theory21628 (m.theta 0 7) (m.theta 2 7) (m.theta 7 8)
  exact rule32372 (meaning t m 2341) (meaning t m 2717) (meaning t m 3577) source

theorem rule32378 (p2027 p2387 p3204 p3399 p3954 p4075 p4347 p4444 p4826 p4870 : Prop) (h : (¬ p3954) ∨ (¬ p3399) ∨ (¬ p4870) ∨ (¬ p4444) ∨ (¬ p4075) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4826) ∨ (¬ p3204)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3204) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial32378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory21634 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule32378 (meaning t m 2027) (meaning t m 2387) (meaning t m 3204) (meaning t m 3399) (meaning t m 3954) (meaning t m 4075) (meaning t m 4347) (meaning t m 4444) (meaning t m 4826) (meaning t m 4870) source

theorem rule32383 (p1984 p2027 p2169 p2247 p2363 p4118 p4154 p4196 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p4154) ∨ p2169 ∨ (¬ p1984) ∨ (¬ p2363) ∨ (¬ p4196) ∨ (¬ p4118)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4154) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial32383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory21639 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32383 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2247) (meaning t m 2363) (meaning t m 4118) (meaning t m 4154) (meaning t m 4196) source

theorem rule32391 (p1998 p2027 p2765 p2901 p3146 p3747 p3952 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3146) ∨ (¬ p3747) ∨ p2765 ∨ (¬ p2901)) : (¬ p1998) ∨ (p2027) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p3952) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial32391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory21647 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32391 (meaning t m 1998) (meaning t m 2027) (meaning t m 2765) (meaning t m 2901) (meaning t m 3146) (meaning t m 3747) (meaning t m 3952) (meaning t m 4348) source

theorem rule32405 (p1984 p2027 p2462 p2761 p3555 p4322 p4363 : Prop) (h : (¬ p1984) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p2761) ∨ p2462 ∨ (¬ p4322) ∨ (¬ p4363)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3555) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial32405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory21661 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule32405 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3555) (meaning t m 4322) (meaning t m 4363) source

theorem rule32406 (p2027 p2138 p2248 p2331 p2363 p2668 p3690 p3873 p4244 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p2331) ∨ (¬ p4244) ∨ (¬ p2363) ∨ (¬ p2248) ∨ (¬ p3873) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p3873) ∨ (¬ p4244) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21662 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32406 (meaning t m 2027) (meaning t m 2138) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3690) (meaning t m 3873) (meaning t m 4244) (meaning t m 4669) source

theorem rule32407 (p1975 p2027 p2114 p2274 p2819 p2829 p3989 : Prop) (h : (¬ p1975) ∨ p2114 ∨ (¬ p2819) ∨ (¬ p2274) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2274) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial32407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory21663 t (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule32407 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2274) (meaning t m 2819) (meaning t m 2829) (meaning t m 3989) source

theorem rule32410 (p2027 p2396 p3506 p4119 p4322 p4335 p4556 p4656 : Prop) (h : (¬ p2396) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p4656) ∨ (¬ p4322) ∨ (¬ p4119) ∨ (¬ p4335) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3506) ∨ (¬ p4119) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4556) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial32410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory21666 t (m.theta 3 9) (m.theta 5 7) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule32410 (meaning t m 2027) (meaning t m 2396) (meaning t m 3506) (meaning t m 4119) (meaning t m 4322) (meaning t m 4335) (meaning t m 4556) (meaning t m 4656) source

theorem rule32411 (p1988 p2027 p2437 p2545 p2761 p3355 p3540 p4451 : Prop) (h : (¬ p3355) ∨ (¬ p3540) ∨ p2545 ∨ (¬ p2437) ∨ (¬ p4451) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2761) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial32411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory21667 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule32411 (meaning t m 1988) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2761) (meaning t m 3355) (meaning t m 3540) (meaning t m 4451) source

theorem rule32413 (p2010 p2027 p2707 p2717 p3622 p3644 p4379 : Prop) (h : p2027 ∨ (¬ p3644) ∨ (¬ p2010) ∨ (¬ p4379) ∨ (¬ p2717) ∨ p3622 ∨ (¬ p2707)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (p3622) ∨ (¬ p3644) ∨ (¬ p4379) := by
  classical
  tauto

theorem initial32413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 3622) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4379)) := by
  have source := ElevenTheory.theory21669 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 4 7) (m.theta 7 8)
  exact rule32413 (meaning t m 2010) (meaning t m 2027) (meaning t m 2707) (meaning t m 2717) (meaning t m 3622) (meaning t m 3644) (meaning t m 4379) source

theorem rule32414 (p1984 p2027 p2247 p2842 p2860 p3582 p3662 p3952 : Prop) (h : (¬ p3662) ∨ (¬ p1984) ∨ (¬ p3582) ∨ (¬ p2247) ∨ (¬ p3952) ∨ p2842 ∨ p2027 ∨ (¬ p2860)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2842) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial32414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory21670 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 4) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule32414 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2842) (meaning t m 2860) (meaning t m 3582) (meaning t m 3662) (meaning t m 3952) source

theorem rule32417 (p1986 p2027 p3146 p3684 p3697 p3857 p3982 p4031 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p3697) ∨ p2027 ∨ (¬ p4031) ∨ p3982 ∨ (¬ p3684) ∨ (¬ p1986) ∨ (¬ p3146) ∨ (¬ p3857)) : (¬ p1986) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3684) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (p3982) ∨ (¬ p4031) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial32417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory21673 t (m.theta 0 5) (m.theta 0 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule32417 (meaning t m 1986) (meaning t m 2027) (meaning t m 3146) (meaning t m 3684) (meaning t m 3697) (meaning t m 3857) (meaning t m 3982) (meaning t m 4031) (meaning t m 5568) source

theorem rule32418 (p2027 p2132 p2187 p2459 p2534 p2860 p3540 p4133 p4186 p4729 : Prop) (h : (¬ p4133) ∨ (¬ p2860) ∨ (¬ p2187) ∨ (¬ p4729) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2860) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial32418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory21674 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32418 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2459) (meaning t m 2534) (meaning t m 2860) (meaning t m 3540) (meaning t m 4133) (meaning t m 4186) (meaning t m 4729) source

theorem rule32420 (p2027 p2246 p2417 p2437 p2651 p2744 p2780 p3366 p3950 p4347 p4358 : Prop) (h : (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2437) ∨ (¬ p3950) ∨ (¬ p3366) ∨ (¬ p2780) ∨ (¬ p2744) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4358)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial32420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory21676 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32420 (meaning t m 2027) (meaning t m 2246) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 2780) (meaning t m 3366) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) source

theorem rule32422 (p2027 p2252 p2295 p2313 p2518 p2750 p3324 p3379 p3954 p3983 p4596 : Prop) (h : (¬ p4596) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2295) ∨ (¬ p3983) ∨ (¬ p2518) ∨ (¬ p3324) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p3983) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial32422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory21678 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule32422 (meaning t m 2027) (meaning t m 2252) (meaning t m 2295) (meaning t m 2313) (meaning t m 2518) (meaning t m 2750) (meaning t m 3324) (meaning t m 3379) (meaning t m 3954) (meaning t m 3983) (meaning t m 4596) source

theorem rule32427 (p1997 p2027 p2699 p2850 p3093 p3309 p3822 p5220 : Prop) (h : p2699 ∨ (¬ p1997) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3309) ∨ (¬ p5220) ∨ (¬ p3093)) : (¬ p1997) ∨ (p2027) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial32427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory21683 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 6 7)
  exact rule32427 (meaning t m 1997) (meaning t m 2027) (meaning t m 2699) (meaning t m 2850) (meaning t m 3093) (meaning t m 3309) (meaning t m 3822) (meaning t m 5220) source

theorem rule32432 (p2027 p2786 p3055 p3204 p4053 p4329 p4749 p4841 : Prop) (h : (¬ p2786) ∨ p2027 ∨ (¬ p4841) ∨ (¬ p3204) ∨ (¬ p4329) ∨ (¬ p4053) ∨ (¬ p3055) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3204) ∨ (¬ p4053) ∨ (¬ p4329) ∨ (¬ p4749) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial32432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory21688 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 10)
  exact rule32432 (meaning t m 2027) (meaning t m 2786) (meaning t m 3055) (meaning t m 3204) (meaning t m 4053) (meaning t m 4329) (meaning t m 4749) (meaning t m 4841) source

theorem rule32435 (p2027 p3232 p3670 p3684 p4321 p4354 p4953 p5344 : Prop) (h : (¬ p4953) ∨ (¬ p5344) ∨ (¬ p3232) ∨ p2027 ∨ (¬ p4354) ∨ (¬ p4321) ∨ (¬ p3684) ∨ (¬ p3670)) : (p2027) ∨ (¬ p3232) ∨ (¬ p3670) ∨ (¬ p3684) ∨ (¬ p4321) ∨ (¬ p4354) ∨ (¬ p4953) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial32435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4354)) ∨ (¬ (meaning t m 4953)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory21691 t (m.theta 1 9) (m.theta 2 4) (m.theta 2 8) (m.theta 2 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule32435 (meaning t m 2027) (meaning t m 3232) (meaning t m 3670) (meaning t m 3684) (meaning t m 4321) (meaning t m 4354) (meaning t m 4953) (meaning t m 5344) source

theorem rule32436 (p1981 p2027 p2202 p2440 p2528 p3083 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p3083)) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial32436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory21692 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32436 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2528) (meaning t m 3083) (meaning t m 4347) source

theorem rule32437 (p2027 p2497 p2922 p3660 p3888 p4435 p4646 : Prop) (h : (¬ p2497) ∨ (¬ p2922) ∨ (¬ p3660) ∨ p2027 ∨ (¬ p4435) ∨ (¬ p3888) ∨ (¬ p4646)) : (p2027) ∨ (¬ p2497) ∨ (¬ p2922) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial32437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory21693 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule32437 (meaning t m 2027) (meaning t m 2497) (meaning t m 2922) (meaning t m 3660) (meaning t m 3888) (meaning t m 4435) (meaning t m 4646) source

theorem rule32440 (p2027 p3256 p3692 p4119 p4140 p4341 p5472 p5717 : Prop) (h : (¬ p3256) ∨ (¬ p4119) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p5472) ∨ (¬ p4341) ∨ (¬ p5717) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p4341) ∨ (¬ p5472) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial32440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 5472)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory21696 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 10) (m.theta 6 7) (m.theta 8 9)
  exact rule32440 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 4119) (meaning t m 4140) (meaning t m 4341) (meaning t m 5472) (meaning t m 5717) source

theorem rule32443 (p2027 p2534 p2928 p3609 p4186 p4354 p5214 : Prop) (h : (¬ p3609) ∨ (¬ p4354) ∨ p2027 ∨ (¬ p5214) ∨ (¬ p4186) ∨ (¬ p2534) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2928) ∨ (¬ p3609) ∨ (¬ p4186) ∨ (¬ p4354) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial32443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4354)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory21699 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule32443 (meaning t m 2027) (meaning t m 2534) (meaning t m 2928) (meaning t m 3609) (meaning t m 4186) (meaning t m 4354) (meaning t m 5214) source

theorem rule32444 (p1988 p2027 p2774 p2842 p3055 p3461 p3483 : Prop) (h : (¬ p3483) ∨ (¬ p2774) ∨ (¬ p3055) ∨ p2842 ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2774) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3483) := by
  classical
  tauto

theorem initial32444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) := by
  have source := ElevenTheory.theory21700 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 9) (m.theta 9 10)
  exact rule32444 (meaning t m 1988) (meaning t m 2027) (meaning t m 2774) (meaning t m 2842) (meaning t m 3055) (meaning t m 3461) (meaning t m 3483) source

theorem rule32451 (p2027 p3093 p3555 p3758 p4516 p4878 : Prop) (h : (¬ p3758) ∨ p2027 ∨ (¬ p4878) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4516)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3758) ∨ (¬ p4516) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial32451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory21707 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6)
  exact rule32451 (meaning t m 2027) (meaning t m 3093) (meaning t m 3555) (meaning t m 3758) (meaning t m 4516) (meaning t m 4878) source

theorem rule32457 (p2707 p3585 p3686 : Prop) (h : (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3686)) : (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial32457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory21713 (m.theta 1 2) (m.theta 2 4) (m.theta 2 7)
  exact rule32457 (meaning t m 2707) (meaning t m 3585) (meaning t m 3686) source

theorem rule32458 (p2027 p2685 p3516 p4035 p4656 p4854 : Prop) (h : (¬ p2685) ∨ p2027 ∨ (¬ p4656) ∨ (¬ p3516) ∨ (¬ p4854) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3516) ∨ (¬ p4035) ∨ (¬ p4656) ∨ (¬ p4854) := by
  classical
  tauto

theorem initial32458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4656)) ∨ (¬ (meaning t m 4854)) := by
  have source := ElevenTheory.theory21714 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9)
  exact rule32458 (meaning t m 2027) (meaning t m 2685) (meaning t m 3516) (meaning t m 4035) (meaning t m 4656) (meaning t m 4854) source

theorem rule32459 (p2027 p2241 p2727 p3266 p3343 p4120 p4322 p4332 p4335 p4524 : Prop) (h : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p4120) ∨ (¬ p4332) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p4524) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial32459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory21715 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32459 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3266) (meaning t m 3343) (meaning t m 4120) (meaning t m 4322) (meaning t m 4332) (meaning t m 4335) (meaning t m 4524) source

theorem rule32464 (p2027 p2387 p2778 p2819 p2829 p4734 : Prop) (h : (¬ p2778) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2819) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial32464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory21720 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8)
  exact rule32464 (meaning t m 2027) (meaning t m 2387) (meaning t m 2778) (meaning t m 2819) (meaning t m 2829) (meaning t m 4734) source

theorem rule32465 (p1984 p2027 p2114 p2247 p2829 p3461 p3483 p3662 p4208 p4444 p5059 : Prop) (h : (¬ p3483) ∨ (¬ p2829) ∨ p2027 ∨ p2114 ∨ (¬ p3461) ∨ (¬ p2247) ∨ (¬ p4208) ∨ (¬ p1984) ∨ (¬ p3662) ∨ (¬ p5059) ∨ (¬ p4444)) : (¬ p1984) ∨ (p2027) ∨ (p2114) ∨ (¬ p2247) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4444) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial32465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory21721 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32465 (meaning t m 1984) (meaning t m 2027) (meaning t m 2114) (meaning t m 2247) (meaning t m 2829) (meaning t m 3461) (meaning t m 3483) (meaning t m 3662) (meaning t m 4208) (meaning t m 4444) (meaning t m 5059) source

theorem rule32470 (p2027 p2264 p2311 p2995 p3551 p3758 p4356 p4906 : Prop) (h : (¬ p2311) ∨ (¬ p4906) ∨ (¬ p4356) ∨ (¬ p3551) ∨ (¬ p2995) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2311) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p3758) ∨ (¬ p4356) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial32470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory21726 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 7 8)
  exact rule32470 (meaning t m 2027) (meaning t m 2264) (meaning t m 2311) (meaning t m 2995) (meaning t m 3551) (meaning t m 3758) (meaning t m 4356) (meaning t m 4906) source

theorem rule32472 (p2006 p2027 p2284 p2766 p3497 p3692 p3758 : Prop) (h : (¬ p3692) ∨ (¬ p3497) ∨ p2766 ∨ (¬ p2006) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2284)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2284) ∨ (p2766) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial32472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory21728 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule32472 (meaning t m 2006) (meaning t m 2027) (meaning t m 2284) (meaning t m 2766) (meaning t m 3497) (meaning t m 3692) (meaning t m 3758) source

theorem rule32474 (p1983 p2027 p2177 p2274 p2765 p3548 p3631 : Prop) (h : (¬ p1983) ∨ (¬ p3631) ∨ (¬ p2274) ∨ p2765 ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2177)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3548) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial32474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory21730 t (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32474 (meaning t m 1983) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2765) (meaning t m 3548) (meaning t m 3631) source

theorem rule32475 (p1983 p2027 p2274 p2312 p2341 p2765 p3548 p3631 : Prop) (h : (¬ p1983) ∨ (¬ p3631) ∨ (¬ p2274) ∨ p2765 ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p2312)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (p2765) ∨ (¬ p3548) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial32475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory21731 t (m.theta 0 7) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32475 (meaning t m 1983) (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 2341) (meaning t m 2765) (meaning t m 3548) (meaning t m 3631) source

theorem rule32477 (p2027 p2470 p2528 p3453 p4261 p5194 : Prop) (h : (¬ p4261) ∨ (¬ p5194) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3453)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial32477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory21733 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule32477 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3453) (meaning t m 4261) (meaning t m 5194) source

theorem rule32479 (p2299 p3570 p4140 : Prop) (h : (¬ p3570) ∨ (¬ p4140) ∨ p2299) : (p2299) ∨ (¬ p3570) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial32479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2299) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory21735 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule32479 (meaning t m 2299) (meaning t m 3570) (meaning t m 4140) source

theorem rule32486 (p2027 p2192 p3486 p3569 p3646 p3741 p4533 : Prop) (h : (¬ p2192) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4533) ∨ (¬ p3741)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p3646) ∨ (¬ p3741) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial32486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory21742 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule32486 (meaning t m 2027) (meaning t m 2192) (meaning t m 3486) (meaning t m 3569) (meaning t m 3646) (meaning t m 3741) (meaning t m 4533) source

theorem rule32488 (p2027 p2619 p3073 p3949 p4385 p4498 : Prop) (h : (¬ p4498) ∨ (¬ p3073) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3949)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3073) ∨ (¬ p3949) ∨ (¬ p4385) ∨ (¬ p4498) := by
  classical
  tauto

theorem initial32488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4498)) := by
  have source := ElevenTheory.theory21744 t (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule32488 (meaning t m 2027) (meaning t m 2619) (meaning t m 3073) (meaning t m 3949) (meaning t m 4385) (meaning t m 4498) source

theorem rule32491 (p2027 p2440 p2641 p3984 p4111 p4717 : Prop) (h : p2027 ∨ (¬ p4717) ∨ (¬ p2440) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2641) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial32491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory21747 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule32491 (meaning t m 2027) (meaning t m 2440) (meaning t m 2641) (meaning t m 3984) (meaning t m 4111) (meaning t m 4717) source

theorem rule32497 (p2027 p2743 p2891 p3371 p4244 p5052 : Prop) (h : (¬ p5052) ∨ (¬ p4244) ∨ (¬ p3371) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p2743)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial32497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory21753 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule32497 (meaning t m 2027) (meaning t m 2743) (meaning t m 2891) (meaning t m 3371) (meaning t m 4244) (meaning t m 5052) source

theorem rule32498 (p1992 p2027 p2499 p2608 p3008 p3222 p3346 p4108 : Prop) (h : (¬ p3346) ∨ (¬ p1992) ∨ (¬ p4108) ∨ p3008 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2499) ∨ (¬ p3222)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2608) ∨ (p3008) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial32498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory21754 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9)
  exact rule32498 (meaning t m 1992) (meaning t m 2027) (meaning t m 2499) (meaning t m 2608) (meaning t m 3008) (meaning t m 3222) (meaning t m 3346) (meaning t m 4108) source

theorem rule32510 (p2341 p2911 p4279 : Prop) (h : (¬ p2911) ∨ (¬ p4279) ∨ p2341) : (p2341) ∨ (¬ p2911) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial32510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2341) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory21766 (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule32510 (meaning t m 2341) (meaning t m 2911) (meaning t m 4279) source

theorem rule32512 (p2027 p2331 p2427 p3506 p3556 p3904 p4117 p4191 p4368 p4421 p4729 p4948 : Prop) (h : (¬ p3904) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p4729) ∨ (¬ p4368) ∨ p2027 ∨ (¬ p4421) ∨ (¬ p4948) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2427) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4368) ∨ (¬ p4421) ∨ (¬ p4729) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial32512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory21768 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule32512 (meaning t m 2027) (meaning t m 2331) (meaning t m 2427) (meaning t m 3506) (meaning t m 3556) (meaning t m 3904) (meaning t m 4117) (meaning t m 4191) (meaning t m 4368) (meaning t m 4421) (meaning t m 4729) (meaning t m 4948) source

theorem rule32513 (p2027 p2252 p2750 p2952 p3073 p3449 p3690 p3954 p4320 p4669 : Prop) (h : p2027 ∨ (¬ p3073) ∨ (¬ p2952) ∨ (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p2252) ∨ (¬ p3954) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21769 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule32513 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3073) (meaning t m 3449) (meaning t m 3690) (meaning t m 3954) (meaning t m 4320) (meaning t m 4669) source

theorem rule32514 (p1982 p2027 p2518 p2528 p2901 p3246 p3379 p3497 p3578 p3821 p5210 : Prop) (h : (¬ p3379) ∨ p3578 ∨ (¬ p3497) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2528) ∨ (¬ p3821) ∨ (¬ p2518) ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p5210)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (p3578) ∨ (¬ p3821) ∨ (¬ p5210) := by
  classical
  tauto

theorem initial32514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5210)) := by
  have source := ElevenTheory.theory21770 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32514 (meaning t m 1982) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2901) (meaning t m 3246) (meaning t m 3379) (meaning t m 3497) (meaning t m 3578) (meaning t m 3821) (meaning t m 5210) source

theorem rule32517 (p2619 p3698 p3880 : Prop) (h : (¬ p3698) ∨ (¬ p2619) ∨ (¬ p3880)) : (¬ p2619) ∨ (¬ p3698) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial32517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory21773 (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule32517 (meaning t m 2619) (meaning t m 3698) (meaning t m 3880) source

theorem rule32522 (p2027 p2252 p2750 p2952 p3707 p3830 p3954 p4320 p4831 p5660 : Prop) (h : (¬ p5660) ∨ (¬ p3954) ∨ (¬ p4831) ∨ (¬ p4320) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3707)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial32522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory21778 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule32522 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 4320) (meaning t m 4831) (meaning t m 5660) source

theorem rule32523 (p2027 p2254 p2363 p2952 p3063 p3093 p3690 p4320 p4669 : Prop) (h : (¬ p4669) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p3063) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p3093) ∨ (¬ p4320) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21779 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32523 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3690) (meaning t m 4320) (meaning t m 4669) source

theorem rule32528 (p2001 p2027 p2873 p3449 p3555 p4181 p5568 : Prop) (h : (¬ p5568) ∨ p2873 ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2001) ∨ (¬ p4181)) : (¬ p2001) ∨ (p2027) ∨ (p2873) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4181) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial32528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory21784 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 8) (m.theta 8 10)
  exact rule32528 (meaning t m 2001) (meaning t m 2027) (meaning t m 2873) (meaning t m 3449) (meaning t m 3555) (meaning t m 4181) (meaning t m 5568) source

theorem rule32533 (p2027 p2307 p2781 p2911 p3365 p3921 p3941 p4035 p5119 p5284 : Prop) (h : (¬ p2781) ∨ (¬ p3921) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p2911) ∨ (¬ p2307) ∨ (¬ p5284) ∨ (¬ p3365) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3921) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial32533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory21789 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 9) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule32533 (meaning t m 2027) (meaning t m 2307) (meaning t m 2781) (meaning t m 2911) (meaning t m 3365) (meaning t m 3921) (meaning t m 3941) (meaning t m 4035) (meaning t m 5119) (meaning t m 5284) source

theorem rule32536 (p2027 p2248 p2264 p2807 p3583 p3644 p3954 p4244 p4277 : Prop) (h : (¬ p4244) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4277) ∨ (¬ p3644) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p2807) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3583) ∨ (¬ p3644) ∨ (¬ p3954) ∨ (¬ p4244) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial32536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory21792 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule32536 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2807) (meaning t m 3583) (meaning t m 3644) (meaning t m 3954) (meaning t m 4244) (meaning t m 4277) source

theorem rule32539 (p1996 p2027 p2202 p2922 p3238 p3516 p3575 p3947 : Prop) (h : (¬ p1996) ∨ p2202 ∨ (¬ p3238) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p2922) ∨ (¬ p3575)) : (¬ p1996) ∨ (p2027) ∨ (p2202) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial32539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory21795 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule32539 (meaning t m 1996) (meaning t m 2027) (meaning t m 2202) (meaning t m 2922) (meaning t m 3238) (meaning t m 3516) (meaning t m 3575) (meaning t m 3947) source

theorem rule32544 (p2027 p2138 p2449 p2761 p2807 p3694 p4786 p5123 p5568 : Prop) (h : p2027 ∨ (¬ p4786) ∨ (¬ p3694) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p5123) ∨ (¬ p2138) ∨ (¬ p2761) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial32544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory21800 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32544 (meaning t m 2027) (meaning t m 2138) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3694) (meaning t m 4786) (meaning t m 5123) (meaning t m 5568) source

theorem rule32545 (p2027 p3055 p3366 p3399 p3527 p3555 p3876 p4278 p4377 p4666 : Prop) (h : (¬ p3876) ∨ (¬ p3055) ∨ (¬ p3555) ∨ (¬ p4278) ∨ (¬ p3399) ∨ (¬ p4666) ∨ (¬ p4377) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3527)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial32545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory21801 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32545 (meaning t m 2027) (meaning t m 3055) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3555) (meaning t m 3876) (meaning t m 4278) (meaning t m 4377) (meaning t m 4666) source

theorem rule32548 (p1977 p2027 p2765 p3005 p3952 p4315 p4360 : Prop) (h : p2765 ∨ (¬ p3952) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p4360) ∨ (¬ p3005)) : (¬ p1977) ∨ (p2027) ∨ (p2765) ∨ (¬ p3005) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial32548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory21804 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule32548 (meaning t m 1977) (meaning t m 2027) (meaning t m 2765) (meaning t m 3005) (meaning t m 3952) (meaning t m 4315) (meaning t m 4360) source

theorem rule32551 (p1990 p2027 p2132 p2254 p2563 p2766 p3105 p3414 p3553 p3589 p4348 p4948 : Prop) (h : (¬ p1990) ∨ (¬ p2563) ∨ p2766 ∨ (¬ p4948) ∨ (¬ p3414) ∨ (¬ p4348) ∨ (¬ p2254) ∨ (¬ p2132) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3105)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2254) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p3105) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3589) ∨ (¬ p4348) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial32551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory21807 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule32551 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2254) (meaning t m 2563) (meaning t m 2766) (meaning t m 3105) (meaning t m 3414) (meaning t m 3553) (meaning t m 3589) (meaning t m 4348) (meaning t m 4948) source

theorem rule32555 (p2027 p2241 p2589 p3189 p3347 p3570 p3954 p4235 p4550 p5216 : Prop) (h : (¬ p3954) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4550) ∨ (¬ p3570) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3347) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4235) ∨ (¬ p4550) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21811 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule32555 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3189) (meaning t m 3347) (meaning t m 3570) (meaning t m 3954) (meaning t m 4235) (meaning t m 4550) (meaning t m 5216) source

theorem rule32558 (p2027 p2248 p3166 p3256 p3583 p3694 p3954 p4348 p4905 : Prop) (h : (¬ p3954) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4905) ∨ (¬ p3166) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial32558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory21814 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32558 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3583) (meaning t m 3694) (meaning t m 3954) (meaning t m 4348) (meaning t m 4905) source

theorem rule32559 (p2027 p3323 p3744 p4320 p4336 p4555 : Prop) (h : (¬ p3744) ∨ (¬ p3323) ∨ (¬ p4336) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p4320)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p4320) ∨ (¬ p4336) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial32559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory21815 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule32559 (meaning t m 2027) (meaning t m 3323) (meaning t m 3744) (meaning t m 4320) (meaning t m 4336) (meaning t m 4555) source

theorem rule32563 (p1979 p2027 p2797 p3073 p3441 p3877 p4118 p4153 : Prop) (h : (¬ p1979) ∨ (¬ p2797) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4153) ∨ (¬ p3877) ∨ p3441 ∨ (¬ p4118)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2797) ∨ (¬ p3073) ∨ (p3441) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial32563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3073)) ∨ (meaning t m 3441) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory21819 t (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule32563 (meaning t m 1979) (meaning t m 2027) (meaning t m 2797) (meaning t m 3073) (meaning t m 3441) (meaning t m 3877) (meaning t m 4118) (meaning t m 4153) source

theorem rule32564 (p2027 p2264 p2298 p3548 p3914 p4024 p4105 p5477 : Prop) (h : (¬ p3914) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p3548) ∨ (¬ p2264) ∨ (¬ p2298) ∨ p2027 ∨ (¬ p5477)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2298) ∨ (¬ p3548) ∨ (¬ p3914) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p5477) := by
  classical
  tauto

theorem initial32564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 5477)) := by
  have source := ElevenTheory.theory21820 t (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 3 7) (m.theta 6 10) (m.theta 6 7) (m.theta 7 8)
  exact rule32564 (meaning t m 2027) (meaning t m 2264) (meaning t m 2298) (meaning t m 3548) (meaning t m 3914) (meaning t m 4024) (meaning t m 4105) (meaning t m 5477) source

theorem rule32572 (p2027 p2493 p2579 p2655 p3361 p3541 p3583 p5049 : Prop) (h : (¬ p3361) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p5049) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3541)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial32572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory21828 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 4 6)
  exact rule32572 (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2655) (meaning t m 3361) (meaning t m 3541) (meaning t m 3583) (meaning t m 5049) source

theorem rule32573 (p1982 p2027 p2409 p2518 p3146 p4149 p5568 : Prop) (h : p2409 ∨ (¬ p5568) ∨ (¬ p3146) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p4149)) : (¬ p1982) ∨ (p2027) ∨ (p2409) ∨ (¬ p2518) ∨ (¬ p3146) ∨ (¬ p4149) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial32573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory21829 t (m.theta 1 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule32573 (meaning t m 1982) (meaning t m 2027) (meaning t m 2409) (meaning t m 2518) (meaning t m 3146) (meaning t m 4149) (meaning t m 5568) source

theorem rule32574 (p2027 p2249 p3038 p3414 p3631 p3947 : Prop) (h : (¬ p3038) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p3631) ∨ (¬ p3947) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p3038) ∨ (¬ p3414) ∨ (¬ p3631) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial32574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory21830 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule32574 (meaning t m 2027) (meaning t m 2249) (meaning t m 3038) (meaning t m 3414) (meaning t m 3631) (meaning t m 3947) source

theorem rule32578 (p1982 p2027 p2098 p2114 p2737 p3256 p3365 p4967 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p3256) ∨ (¬ p1982) ∨ (¬ p3365) ∨ (¬ p4967) ∨ (¬ p2098) ∨ (¬ p2737)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial32578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory21834 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule32578 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 2737) (meaning t m 3256) (meaning t m 3365) (meaning t m 4967) source

theorem rule32579 (p2027 p2088 p2657 p3178 p4118 p5011 : Prop) (h : (¬ p3178) ∨ (¬ p2657) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p5011) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2657) ∨ (¬ p3178) ∨ (¬ p4118) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial32579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory21835 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule32579 (meaning t m 2027) (meaning t m 2088) (meaning t m 2657) (meaning t m 3178) (meaning t m 4118) (meaning t m 5011) source

theorem rule32587 (p3584 p3742 p3920 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3920) ∨ (¬ p3742) ∨ p3584) : (p3584) ∨ (¬ p3742) ∨ (¬ p3920) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial32587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3584) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory21843 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule32587 (meaning t m 3584) (meaning t m 3742) (meaning t m 3920) (meaning t m 4343) source

theorem rule32588 (p3742 p3876 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3742) ∨ p3876) : (¬ p3742) ∨ (p3876) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial32588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3742)) ∨ (meaning t m 3876) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory21844 (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule32588 (meaning t m 3742) (meaning t m 3876) (meaning t m 4343) source

theorem rule32589 (p3201 p3742 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3742) ∨ (¬ p3201)) : (¬ p3201) ∨ (¬ p3742) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial32589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory21845 (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule32589 (meaning t m 3201) (meaning t m 3742) (meaning t m 4343) source

theorem rule32590 (p1998 p2027 p2114 p2177 p2319 p2779 p2829 p3516 p4107 : Prop) (h : (¬ p4107) ∨ p2114 ∨ (¬ p2319) ∨ (¬ p1998) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2779) ∨ (¬ p3516)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2319) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3516) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial32590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory21846 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32590 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2319) (meaning t m 2779) (meaning t m 2829) (meaning t m 3516) (meaning t m 4107) source

theorem rule32591 (p2027 p2191 p2619 p2737 p4874 p5049 : Prop) (h : (¬ p2737) ∨ (¬ p4874) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p2737) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial32591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory21847 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule32591 (meaning t m 2027) (meaning t m 2191) (meaning t m 2619) (meaning t m 2737) (meaning t m 4874) (meaning t m 5049) source

theorem rule32592 (p2210 p3830 p4942 : Prop) (h : (¬ p4942) ∨ (¬ p2210) ∨ p3830) : (¬ p2210) ∨ (p3830) ∨ (¬ p4942) := by
  classical
  tauto

theorem initial32592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3830) ∨ (¬ (meaning t m 4942)) := by
  have source := ElevenTheory.theory21848 (m.theta 0 1) (m.theta 1 5) (m.theta 1 9)
  exact rule32592 (meaning t m 2210) (meaning t m 3830) (meaning t m 4942) source

theorem rule32595 (p1987 p2027 p2202 p2373 p2727 p2810 p4312 p4360 : Prop) (h : (¬ p2810) ∨ (¬ p2727) ∨ p2202 ∨ (¬ p1987) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4312) ∨ (¬ p4360)) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p4312) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial32595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory21851 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule32595 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 2727) (meaning t m 2810) (meaning t m 4312) (meaning t m 4360) source

theorem rule32599 (p2027 p2952 p3286 p3952 p4039 p5046 : Prop) (h : (¬ p2952) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p5046) ∨ (¬ p4039) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p3952) ∨ (¬ p4039) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial32599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory21855 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9)
  exact rule32599 (meaning t m 2027) (meaning t m 2952) (meaning t m 3286) (meaning t m 3952) (meaning t m 4039) (meaning t m 5046) source

theorem rule32600 (p2027 p3189 p3662 p3880 p4311 p4705 : Prop) (h : (¬ p3189) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p4311) ∨ (¬ p3880)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3880) ∨ (¬ p4311) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial32600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory21856 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule32600 (meaning t m 2027) (meaning t m 3189) (meaning t m 3662) (meaning t m 3880) (meaning t m 4311) (meaning t m 4705) source

theorem rule32601 (p2742 p3189 p3877 : Prop) (h : (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3877)) : (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial32601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory21857 (m.theta 1 3) (m.theta 2 3) (m.theta 3 8)
  exact rule32601 (meaning t m 2742) (meaning t m 3189) (meaning t m 3877) source

theorem rule32604 (p2027 p2331 p3323 p3461 p3556 p3570 p3904 p4117 p4729 p5123 p5558 : Prop) (h : (¬ p3556) ∨ (¬ p4729) ∨ (¬ p4117) ∨ (¬ p3461) ∨ (¬ p5123) ∨ (¬ p3323) ∨ (¬ p2331) ∨ (¬ p3570) ∨ (¬ p3904) ∨ p2027 ∨ (¬ p5558)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21860 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule32604 (meaning t m 2027) (meaning t m 2331) (meaning t m 3323) (meaning t m 3461) (meaning t m 3556) (meaning t m 3570) (meaning t m 3904) (meaning t m 4117) (meaning t m 4729) (meaning t m 5123) (meaning t m 5558) source

theorem rule32606 (p2027 p2177 p2315 p3961 p4009 p4548 p5590 : Prop) (h : (¬ p2315) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p4009) ∨ (¬ p4548) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3961) ∨ (¬ p4009) ∨ (¬ p4548) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial32606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory21862 t (m.theta 0 7) (m.theta 0 8) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule32606 (meaning t m 2027) (meaning t m 2177) (meaning t m 2315) (meaning t m 3961) (meaning t m 4009) (meaning t m 4548) (meaning t m 5590) source

theorem rule32611 (p1988 p2027 p2518 p2528 p2699 p3266 p3379 : Prop) (h : (¬ p3379) ∨ p2699 ∨ (¬ p3266) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2518) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p3266) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial32611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory21867 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule32611 (meaning t m 1988) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2699) (meaning t m 3266) (meaning t m 3379) source

theorem rule32615 (p1998 p2027 p2247 p2688 p3073 p3449 p4348 : Prop) (h : (¬ p3449) ∨ p2688 ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3073)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial32615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory21871 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32615 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3073) (meaning t m 3449) (meaning t m 4348) source

theorem rule32616 (p2027 p2230 p2440 p2531 p3083 p3688 p3954 p4358 p4433 p5190 : Prop) (h : (¬ p2531) ∨ (¬ p4358) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3688) ∨ (¬ p4433) ∨ (¬ p5190) ∨ (¬ p3083) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial32616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory21872 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule32616 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2531) (meaning t m 3083) (meaning t m 3688) (meaning t m 3954) (meaning t m 4358) (meaning t m 4433) (meaning t m 5190) source

theorem rule32617 (p2027 p3366 p3425 p3449 p3452 p4181 p4324 p4376 p4381 p5119 : Prop) (h : (¬ p4324) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4181) ∨ (¬ p3452) ∨ (¬ p4381) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p5119)) : (p2027) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4324) ∨ (¬ p4376) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial32617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory21873 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32617 (meaning t m 2027) (meaning t m 3366) (meaning t m 3425) (meaning t m 3449) (meaning t m 3452) (meaning t m 4181) (meaning t m 4324) (meaning t m 4376) (meaning t m 4381) (meaning t m 5119) source

theorem rule32623 (p2027 p2187 p2248 p2284 p2459 p2946 p3860 p4133 p4261 : Prop) (h : (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2946)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2946) ∨ (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial32623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory21879 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32623 (meaning t m 2027) (meaning t m 2187) (meaning t m 2248) (meaning t m 2284) (meaning t m 2459) (meaning t m 2946) (meaning t m 3860) (meaning t m 4133) (meaning t m 4261) source

theorem rule32624 (p2027 p2253 p2331 p3055 p3189 p3644 p3876 p4133 p4154 p4417 p4736 : Prop) (h : (¬ p4417) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p4736) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p2331) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4154) ∨ (¬ p4417) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial32624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory21880 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32624 (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 3055) (meaning t m 3189) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4154) (meaning t m 4417) (meaning t m 4736) source

theorem rule32628 (p2027 p2247 p2744 p3073 p3366 p3449 p3680 p4232 p5059 p5387 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p4232) ∨ (¬ p3449) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3073) ∨ (¬ p3680) ∨ (¬ p5059) ∨ (¬ p5387)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3680) ∨ (¬ p4232) ∨ (¬ p5059) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial32628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory21884 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32628 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3680) (meaning t m 4232) (meaning t m 5059) (meaning t m 5387) source

theorem rule32630 (p2027 p2470 p2528 p3588 p3659 p3954 p4133 p4347 p5190 : Prop) (h : (¬ p3954) ∨ (¬ p3588) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p2470) ∨ (¬ p5190) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p2528)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial32630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory21886 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32630 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4133) (meaning t m 4347) (meaning t m 5190) source

theorem rule32632 (p2027 p2166 p2928 p3948 p4031 p4120 p4644 : Prop) (h : p2027 ∨ (¬ p4031) ∨ (¬ p4644) ∨ (¬ p3948) ∨ (¬ p2928) ∨ (¬ p2166) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2928) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial32632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory21888 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8)
  exact rule32632 (meaning t m 2027) (meaning t m 2166) (meaning t m 2928) (meaning t m 3948) (meaning t m 4031) (meaning t m 4120) (meaning t m 4644) source

theorem rule32635 (p2027 p2143 p2696 p2742 p3189 p3256 p3556 p3583 p3690 p4669 p4737 : Prop) (h : (¬ p2696) ∨ (¬ p3556) ∨ (¬ p4737) ∨ (¬ p2742) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3189) ∨ (¬ p2143)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial32635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory21891 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule32635 (meaning t m 2027) (meaning t m 2143) (meaning t m 2696) (meaning t m 2742) (meaning t m 3189) (meaning t m 3256) (meaning t m 3556) (meaning t m 3583) (meaning t m 3690) (meaning t m 4669) (meaning t m 4737) source

theorem rule32638 (p2027 p2088 p2475 p2518 p4340 p5217 p5368 : Prop) (h : p2027 ∨ (¬ p5217) ∨ (¬ p2475) ∨ (¬ p5368) ∨ (¬ p2518) ∨ (¬ p2088) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p4340) ∨ (¬ p5217) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial32638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5217)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory21894 t (m.theta 0 8) (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule32638 (meaning t m 2027) (meaning t m 2088) (meaning t m 2475) (meaning t m 2518) (meaning t m 4340) (meaning t m 5217) (meaning t m 5368) source

theorem rule32639 (p2027 p2528 p2819 p3438 p3917 p4384 p5152 : Prop) (h : (¬ p5152) ∨ (¬ p2819) ∨ (¬ p3438) ∨ (¬ p3917) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p4384)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2819) ∨ (¬ p3438) ∨ (¬ p3917) ∨ (¬ p4384) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial32639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory21895 t (m.theta 1 9) (m.theta 2 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule32639 (meaning t m 2027) (meaning t m 2528) (meaning t m 2819) (meaning t m 3438) (meaning t m 3917) (meaning t m 4384) (meaning t m 5152) source

theorem rule32643 (p2027 p2579 p2630 p2655 p3016 p4787 : Prop) (h : (¬ p3016) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p2579) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial32643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory21899 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule32643 (meaning t m 2027) (meaning t m 2579) (meaning t m 2630) (meaning t m 2655) (meaning t m 3016) (meaning t m 4787) source

theorem rule32648 (p2027 p2298 p2797 p2963 p3399 p3527 p3570 p3877 p4044 p4236 p4556 p4736 : Prop) (h : (¬ p3570) ∨ (¬ p2797) ∨ (¬ p4236) ∨ (¬ p4044) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p2298) ∨ (¬ p3527) ∨ (¬ p4736) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3877) ∨ (¬ p4044) ∨ (¬ p4236) ∨ (¬ p4556) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial32648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory21904 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule32648 (meaning t m 2027) (meaning t m 2298) (meaning t m 2797) (meaning t m 2963) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) (meaning t m 3877) (meaning t m 4044) (meaning t m 4236) (meaning t m 4556) (meaning t m 4736) source

theorem rule32649 (p2027 p2166 p2255 p2946 p2996 p3412 p3821 p3969 p4155 p4381 p5119 : Prop) (h : (¬ p2166) ∨ (¬ p2996) ∨ (¬ p3412) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p2946) ∨ (¬ p2255) ∨ (¬ p5119) ∨ (¬ p3821) ∨ (¬ p4381) ∨ (¬ p4155)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3412) ∨ (¬ p3821) ∨ (¬ p3969) ∨ (¬ p4155) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial32649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory21905 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32649 (meaning t m 2027) (meaning t m 2166) (meaning t m 2255) (meaning t m 2946) (meaning t m 2996) (meaning t m 3412) (meaning t m 3821) (meaning t m 3969) (meaning t m 4155) (meaning t m 4381) (meaning t m 5119) source

theorem rule32652 (p1985 p2027 p2860 p3051 p3578 p3646 p3694 : Prop) (h : (¬ p3694) ∨ (¬ p3051) ∨ p2027 ∨ p3578 ∨ (¬ p1985) ∨ (¬ p3646) ∨ (¬ p2860)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2860) ∨ (¬ p3051) ∨ (p3578) ∨ (¬ p3646) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial32652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory21908 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule32652 (meaning t m 1985) (meaning t m 2027) (meaning t m 2860) (meaning t m 3051) (meaning t m 3578) (meaning t m 3646) (meaning t m 3694) source

theorem rule32654 (p2737 p3537 p4373 : Prop) (h : (¬ p4373) ∨ (¬ p2737) ∨ p3537) : (¬ p2737) ∨ (p3537) ∨ (¬ p4373) := by
  classical
  tauto

theorem initial32654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (meaning t m 3537) ∨ (¬ (meaning t m 4373)) := by
  have source := ElevenTheory.theory21910 (m.theta 1 2) (m.theta 2 3) (m.theta 2 8)
  exact rule32654 (meaning t m 2737) (meaning t m 3537) (meaning t m 4373) source

theorem rule32663 (p1984 p2027 p2138 p2192 p2938 p3486 p3758 p3873 : Prop) (h : p2938 ∨ (¬ p3486) ∨ p2027 ∨ (¬ p3873) ∨ (¬ p2192) ∨ (¬ p1984) ∨ (¬ p3758) ∨ (¬ p2138)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2192) ∨ (p2938) ∨ (¬ p3486) ∨ (¬ p3758) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial32663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory21919 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule32663 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2192) (meaning t m 2938) (meaning t m 3486) (meaning t m 3758) (meaning t m 3873) source

theorem rule32664 (p2027 p2312 p2668 p3516 p3947 p4067 p4405 : Prop) (h : p2027 ∨ (¬ p2312) ∨ (¬ p4405) ∨ (¬ p2668) ∨ (¬ p4067) ∨ (¬ p3947) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2668) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial32664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory21920 t (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule32664 (meaning t m 2027) (meaning t m 2312) (meaning t m 2668) (meaning t m 3516) (meaning t m 3947) (meaning t m 4067) (meaning t m 4405) source

theorem rule32665 (p1997 p2027 p2323 p2542 p2727 p3166 p4360 : Prop) (h : (¬ p1997) ∨ (¬ p2727) ∨ p2027 ∨ p2323 ∨ (¬ p2542) ∨ (¬ p3166) ∨ (¬ p4360)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial32665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory21921 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule32665 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2542) (meaning t m 2727) (meaning t m 3166) (meaning t m 4360) source

theorem rule32669 (p1977 p2027 p2765 p2850 p2881 p3238 p3402 p3659 p3686 p3872 : Prop) (h : (¬ p2850) ∨ (¬ p3686) ∨ (¬ p3402) ∨ p2765 ∨ p2027 ∨ (¬ p3238) ∨ (¬ p1977) ∨ (¬ p3872) ∨ (¬ p2881) ∨ (¬ p3659)) : (¬ p1977) ∨ (p2027) ∨ (p2765) ∨ (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial32669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory21925 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule32669 (meaning t m 1977) (meaning t m 2027) (meaning t m 2765) (meaning t m 2850) (meaning t m 2881) (meaning t m 3238) (meaning t m 3402) (meaning t m 3659) (meaning t m 3686) (meaning t m 3872) source

theorem rule32671 (p2027 p3146 p3548 p3747 p4348 p4911 : Prop) (h : (¬ p4911) ∨ (¬ p4348) ∨ (¬ p3146) ∨ (¬ p3747) ∨ p2027 ∨ (¬ p3548)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3548) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4911) := by
  classical
  tauto

theorem initial32671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4911)) := by
  have source := ElevenTheory.theory21927 t (m.theta 1 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32671 (meaning t m 2027) (meaning t m 3146) (meaning t m 3548) (meaning t m 3747) (meaning t m 4348) (meaning t m 4911) source

theorem rule32673 (p2027 p2589 p2662 p2850 p3475 p4195 p4972 : Prop) (h : (¬ p3475) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2589) ∨ (¬ p4195) ∨ (¬ p2662) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p4195) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial32673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory21929 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule32673 (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2850) (meaning t m 3475) (meaning t m 4195) (meaning t m 4972) source

theorem rule32678 (p2027 p2717 p3969 p4132 p4324 p4445 p5122 : Prop) (h : (¬ p4324) ∨ (¬ p3969) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p4445) ∨ (¬ p4132)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p4324) ∨ (¬ p4445) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial32678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory21934 t (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule32678 (meaning t m 2027) (meaning t m 2717) (meaning t m 3969) (meaning t m 4132) (meaning t m 4324) (meaning t m 4445) (meaning t m 5122) source

theorem rule32681 (p2027 p2427 p3073 p3093 p3556 p3880 p4134 p4317 p4347 p4524 : Prop) (h : p2027 ∨ (¬ p4524) ∨ (¬ p4317) ∨ (¬ p4347) ∨ (¬ p4134) ∨ (¬ p3073) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p3093) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3073) ∨ (¬ p3093) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4317) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial32681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory21937 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 6) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32681 (meaning t m 2027) (meaning t m 2427) (meaning t m 3073) (meaning t m 3093) (meaning t m 3556) (meaning t m 3880) (meaning t m 4134) (meaning t m 4317) (meaning t m 4347) (meaning t m 4524) source

theorem rule32683 (p1998 p2027 p2938 p3156 p3969 p4320 p5558 : Prop) (h : (¬ p1998) ∨ (¬ p5558) ∨ (¬ p3156) ∨ p2938 ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3969)) : (¬ p1998) ∨ (p2027) ∨ (p2938) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4320) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21939 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule32683 (meaning t m 1998) (meaning t m 2027) (meaning t m 2938) (meaning t m 3156) (meaning t m 3969) (meaning t m 4320) (meaning t m 5558) source

theorem rule32686 (p2027 p2598 p2743 p2911 p2922 p3572 p3590 p3947 p4666 p4737 : Prop) (h : (¬ p2911) ∨ (¬ p2743) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3572) ∨ (¬ p3590) ∨ (¬ p2922) ∨ (¬ p2598) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3572) ∨ (¬ p3590) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial32686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory21942 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32686 (meaning t m 2027) (meaning t m 2598) (meaning t m 2743) (meaning t m 2911) (meaning t m 2922) (meaning t m 3572) (meaning t m 3590) (meaning t m 3947) (meaning t m 4666) (meaning t m 4737) source

theorem rule32691 (p2027 p2098 p2952 p3266 p3609 p4320 p4789 p4831 p5660 : Prop) (h : (¬ p2098) ∨ (¬ p4320) ∨ (¬ p2952) ∨ (¬ p4831) ∨ (¬ p3609) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p4320) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial32691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory21947 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule32691 (meaning t m 2027) (meaning t m 2098) (meaning t m 2952) (meaning t m 3266) (meaning t m 3609) (meaning t m 4320) (meaning t m 4789) (meaning t m 4831) (meaning t m 5660) source

theorem rule32692 (p2027 p3660 p3888 p4235 p4393 p4555 : Prop) (h : (¬ p4235) ∨ (¬ p3888) ∨ (¬ p4393) ∨ p2027 ∨ (¬ p3660) ∨ (¬ p4555)) : (p2027) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4235) ∨ (¬ p4393) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial32692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory21948 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10)
  exact rule32692 (meaning t m 2027) (meaning t m 3660) (meaning t m 3888) (meaning t m 4235) (meaning t m 4393) (meaning t m 4555) source

theorem rule32693 (p2027 p2246 p2542 p2608 p2651 p2744 p2982 p3817 p4366 p4395 : Prop) (h : (¬ p2744) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2982) ∨ (¬ p4366) ∨ (¬ p4395) ∨ (¬ p3817) ∨ (¬ p2608) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2982) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial32693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory21949 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 9)
  exact rule32693 (meaning t m 2027) (meaning t m 2246) (meaning t m 2542) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 2982) (meaning t m 3817) (meaning t m 4366) (meaning t m 4395) source

theorem rule32695 (p2396 p3246 p4140 : Prop) (h : (¬ p2396) ∨ (¬ p4140) ∨ p3246) : (¬ p2396) ∨ (p3246) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial32695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (meaning t m 3246) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory21951 (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule32695 (meaning t m 2396) (meaning t m 3246) (meaning t m 4140) source

end SunPrize.SMT
