import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory039
import SunPrize.Certificate.Theory040
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule23890 (p1990 p2027 p2387 p2563 p2766 p2778 p3051 p4019 p4118 p4235 p4399 p4419 p4963 p5580 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p5580) ∨ (¬ p4118) ∨ (¬ p1990) ∨ (¬ p4419) ∨ (¬ p4399) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p3051) ∨ (¬ p4963) ∨ (¬ p4019) ∨ (¬ p2778) ∨ (¬ p2387)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p2778) ∨ (¬ p3051) ∨ (¬ p4019) ∨ (¬ p4118) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4419) ∨ (¬ p4963) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4963)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13146 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 0 6) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23890 (meaning t m 1990) (meaning t m 2027) (meaning t m 2387) (meaning t m 2563) (meaning t m 2766) (meaning t m 2778) (meaning t m 3051) (meaning t m 4019) (meaning t m 4118) (meaning t m 4235) (meaning t m 4399) (meaning t m 4419) (meaning t m 4963) (meaning t m 5580) source

theorem rule23892 (p2020 p2027 p2373 p2766 p3051 p3365 p3877 p3941 p4042 p4118 p4235 p4399 p4419 : Prop) (h : (¬ p4419) ∨ (¬ p2373) ∨ (¬ p3941) ∨ (¬ p4042) ∨ (¬ p2020) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p3051) ∨ p2766 ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p3877)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2373) ∨ (p2766) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3941) ∨ (¬ p4042) ∨ (¬ p4118) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial23892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory13148 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23892 (meaning t m 2020) (meaning t m 2027) (meaning t m 2373) (meaning t m 2766) (meaning t m 3051) (meaning t m 3365) (meaning t m 3877) (meaning t m 3941) (meaning t m 4042) (meaning t m 4118) (meaning t m 4235) (meaning t m 4399) (meaning t m 4419) source

theorem rule23893 (p2027 p3051 p3346 p4235 p4399 p4949 : Prop) (h : (¬ p4399) ∨ (¬ p4235) ∨ (¬ p3051) ∨ (¬ p4949) ∨ p2027 ∨ (¬ p3346)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3346) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial23893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory13149 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7)
  exact rule23893 (meaning t m 2027) (meaning t m 3051) (meaning t m 3346) (meaning t m 4235) (meaning t m 4399) (meaning t m 4949) source

theorem rule23897 (p2027 p2396 p2553 p2573 p3266 p3292 p3950 p4236 p4419 p5284 : Prop) (h : (¬ p4419) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p5284) ∨ (¬ p3292) ∨ (¬ p3266) ∨ (¬ p4236)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory13153 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23897 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3266) (meaning t m 3292) (meaning t m 3950) (meaning t m 4236) (meaning t m 4419) (meaning t m 5284) source

theorem rule23898 (p2027 p2191 p2518 p2528 p2608 p3555 p4134 p4347 p4376 : Prop) (h : (¬ p2518) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p2528) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial23898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory13154 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23898 (meaning t m 2027) (meaning t m 2191) (meaning t m 2518) (meaning t m 2528) (meaning t m 2608) (meaning t m 3555) (meaning t m 4134) (meaning t m 4347) (meaning t m 4376) source

theorem rule23900 (p2027 p2563 p3051 p4120 p4235 p4507 : Prop) (h : (¬ p4235) ∨ (¬ p4507) ∨ (¬ p3051) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4120)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory13156 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule23900 (meaning t m 2027) (meaning t m 2563) (meaning t m 3051) (meaning t m 4120) (meaning t m 4235) (meaning t m 4507) source

theorem rule23901 (p2027 p2241 p2417 p2598 p2750 p2753 p3032 p3201 p3553 p4366 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3032) ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p4366) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3201) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13157 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23901 (meaning t m 2027) (meaning t m 2241) (meaning t m 2417) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3032) (meaning t m 3201) (meaning t m 3553) (meaning t m 4366) (meaning t m 4668) source

theorem rule23902 (p2027 p2132 p2245 p2870 p3027 p3414 p3662 p4235 p4705 p4733 : Prop) (h : (¬ p4235) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p3027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2245) ∨ (¬ p4705) ∨ (¬ p3662) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2870) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4235) ∨ (¬ p4705) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4705)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13158 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule23902 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2870) (meaning t m 3027) (meaning t m 3414) (meaning t m 3662) (meaning t m 4235) (meaning t m 4705) (meaning t m 4733) source

theorem rule23903 (p1990 p2027 p2476 p2563 p3051 p3498 p4235 p4399 : Prop) (h : (¬ p3051) ∨ (¬ p4399) ∨ (¬ p1990) ∨ p2027 ∨ p3498 ∨ (¬ p4235) ∨ (¬ p2563) ∨ (¬ p2476)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (p3498) ∨ (¬ p4235) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial23903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory13159 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7)
  exact rule23903 (meaning t m 1990) (meaning t m 2027) (meaning t m 2476) (meaning t m 2563) (meaning t m 3051) (meaning t m 3498) (meaning t m 4235) (meaning t m 4399) source

theorem rule23904 (p2027 p2144 p2156 p3055 p3758 p4392 p4749 : Prop) (h : (¬ p3055) ∨ (¬ p2144) ∨ (¬ p4749) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4392) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3055) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial23904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory13160 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule23904 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 3055) (meaning t m 3758) (meaning t m 4392) (meaning t m 4749) source

theorem rule23907 (p2027 p2563 p2901 p3497 p4235 p4507 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4507) ∨ (¬ p2901) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4235) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory13163 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule23907 (meaning t m 2027) (meaning t m 2563) (meaning t m 2901) (meaning t m 3497) (meaning t m 4235) (meaning t m 4507) source

theorem rule23908 (p2027 p2252 p2598 p2750 p2753 p2963 p3201 p3324 p3868 p5560 p5580 : Prop) (h : (¬ p2963) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3201) ∨ (¬ p5580) ∨ (¬ p2252) ∨ (¬ p5560) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p3868) ∨ (¬ p5560) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 5560)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13164 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 10)
  exact rule23908 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3201) (meaning t m 3324) (meaning t m 3868) (meaning t m 5560) (meaning t m 5580) source

theorem rule23913 (p2027 p2373 p4042 p4235 p5559 p5660 : Prop) (h : (¬ p2373) ∨ (¬ p5559) ∨ (¬ p4042) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2373) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p5559) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial23913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 5559)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory13169 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8)
  exact rule23913 (meaning t m 2027) (meaning t m 2373) (meaning t m 4042) (meaning t m 4235) (meaning t m 5559) (meaning t m 5660) source

theorem rule23914 (p2027 p2254 p2922 p2963 p3379 p3868 p4037 p4191 p4826 : Prop) (h : (¬ p3868) ∨ (¬ p2922) ∨ (¬ p4826) ∨ (¬ p3379) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13170 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule23914 (meaning t m 2027) (meaning t m 2254) (meaning t m 2922) (meaning t m 2963) (meaning t m 3379) (meaning t m 3868) (meaning t m 4037) (meaning t m 4191) (meaning t m 4826) source

theorem rule23915 (p1988 p2027 p2233 p2761 p2982 p3051 p4135 p4235 p4399 : Prop) (h : p2233 ∨ (¬ p3051) ∨ (¬ p4399) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p4135) ∨ (¬ p1988) ∨ (¬ p2982)) : (¬ p1988) ∨ (p2027) ∨ (p2233) ∨ (¬ p2761) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial23915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory13171 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23915 (meaning t m 1988) (meaning t m 2027) (meaning t m 2233) (meaning t m 2761) (meaning t m 2982) (meaning t m 3051) (meaning t m 4135) (meaning t m 4235) (meaning t m 4399) source

theorem rule23916 (p2190 p2563 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p2563) ∨ (¬ p2190)) : (¬ p2190) ∨ (¬ p2563) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial23916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory13172 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule23916 (meaning t m 2190) (meaning t m 2563) (meaning t m 3880) source

theorem rule23917 (p3051 p3389 p4001 p4399 : Prop) (h : (¬ p3051) ∨ (¬ p4399) ∨ (¬ p4001) ∨ p3389) : (¬ p3051) ∨ (p3389) ∨ (¬ p4001) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial23917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (meaning t m 3389) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory13173 (m.theta 0 4) (m.theta 0 5) (m.theta 4 7) (m.theta 5 7)
  exact rule23917 (meaning t m 3051) (meaning t m 3389) (meaning t m 4001) (meaning t m 4399) source

theorem rule23920 (p2027 p2963 p2982 p3051 p3324 p3366 p3519 p4235 p4236 p4347 p4376 p4399 p4450 : Prop) (h : (¬ p4376) ∨ (¬ p4236) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3324) ∨ (¬ p3051) ∨ (¬ p3519) ∨ (¬ p4235) ∨ (¬ p4399) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4235) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial23920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory13176 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23920 (meaning t m 2027) (meaning t m 2963) (meaning t m 2982) (meaning t m 3051) (meaning t m 3324) (meaning t m 3366) (meaning t m 3519) (meaning t m 4235) (meaning t m 4236) (meaning t m 4347) (meaning t m 4376) (meaning t m 4399) (meaning t m 4450) source

theorem rule23921 (p2027 p2598 p2753 p2911 p3093 p3201 p4366 p4442 p4870 p5559 : Prop) (h : (¬ p4442) ∨ (¬ p4366) ∨ (¬ p3093) ∨ (¬ p2753) ∨ (¬ p5559) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4870) ∨ (¬ p2598) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4870) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial23921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory13177 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8)
  exact rule23921 (meaning t m 2027) (meaning t m 2598) (meaning t m 2753) (meaning t m 2911) (meaning t m 3093) (meaning t m 3201) (meaning t m 4366) (meaning t m 4442) (meaning t m 4870) (meaning t m 5559) source

theorem rule23922 (p2027 p2780 p3222 p3276 p3379 p4358 p4736 p5123 p5580 : Prop) (h : (¬ p4736) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p5580) ∨ (¬ p2780) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13178 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23922 (meaning t m 2027) (meaning t m 2780) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 4358) (meaning t m 4736) (meaning t m 5123) (meaning t m 5580) source

theorem rule23925 (p2027 p2459 p2696 p2911 p3366 p3389 p3759 p4242 p4749 p5118 p5612 : Prop) (h : (¬ p2696) ∨ p3366 ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p5612) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4242) ∨ (¬ p5118) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2696) ∨ (¬ p2911) ∨ (p3366) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4242) ∨ (¬ p4749) ∨ (¬ p5118) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial23925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory13181 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23925 (meaning t m 2027) (meaning t m 2459) (meaning t m 2696) (meaning t m 2911) (meaning t m 3366) (meaning t m 3389) (meaning t m 3759) (meaning t m 4242) (meaning t m 4749) (meaning t m 5118) (meaning t m 5612) source

theorem rule23926 (p2027 p2104 p2459 p2911 p3051 p3366 p3954 p4001 p4521 p5118 p5612 : Prop) (h : (¬ p3954) ∨ (¬ p4521) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4001) ∨ (¬ p2911) ∨ (¬ p2104) ∨ (¬ p3366) ∨ (¬ p5118) ∨ (¬ p2459) ∨ (¬ p5612)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p3366) ∨ (¬ p3954) ∨ (¬ p4001) ∨ (¬ p4521) ∨ (¬ p5118) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial23926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory13182 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 8) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23926 (meaning t m 2027) (meaning t m 2104) (meaning t m 2459) (meaning t m 2911) (meaning t m 3051) (meaning t m 3366) (meaning t m 3954) (meaning t m 4001) (meaning t m 4521) (meaning t m 5118) (meaning t m 5612) source

theorem rule23928 (p2027 p2132 p2743 p2881 p2891 p3361 p3414 p3947 p4418 p4666 p4737 : Prop) (h : (¬ p3414) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p4666) ∨ (¬ p3361) ∨ (¬ p3947) ∨ (¬ p2132) ∨ (¬ p4418) ∨ (¬ p2891) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4418) ∨ (¬ p4666) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory13184 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23928 (meaning t m 2027) (meaning t m 2132) (meaning t m 2743) (meaning t m 2881) (meaning t m 2891) (meaning t m 3361) (meaning t m 3414) (meaning t m 3947) (meaning t m 4418) (meaning t m 4666) (meaning t m 4737) source

theorem rule23929 (p2027 p2156 p2295 p3556 p4275 p4560 : Prop) (h : (¬ p4560) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2156) ∨ (¬ p4275)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2295) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13185 t (m.theta 0 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule23929 (meaning t m 2027) (meaning t m 2156) (meaning t m 2295) (meaning t m 3556) (meaning t m 4275) (meaning t m 4560) source

theorem rule23930 (p2027 p2177 p3483 p3659 p3689 p4624 : Prop) (h : (¬ p3689) ∨ (¬ p2177) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3483) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13186 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule23930 (meaning t m 2027) (meaning t m 2177) (meaning t m 3483) (meaning t m 3659) (meaning t m 3689) (meaning t m 4624) source

theorem rule23931 (p2027 p2470 p2630 p2656 p2963 p4037 p4149 p4191 p4787 p5119 : Prop) (h : (¬ p4787) ∨ (¬ p2963) ∨ (¬ p2470) ∨ (¬ p4191) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4787) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial23931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13187 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23931 (meaning t m 2027) (meaning t m 2470) (meaning t m 2630) (meaning t m 2656) (meaning t m 2963) (meaning t m 4037) (meaning t m 4149) (meaning t m 4191) (meaning t m 4787) (meaning t m 5119) source

theorem rule23932 (p2027 p2470 p2528 p2630 p2656 p2963 p3659 p3689 p4328 p4787 p5118 p5558 : Prop) (h : (¬ p2630) ∨ (¬ p5558) ∨ (¬ p4787) ∨ (¬ p2963) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p4328) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3689) ∨ (¬ p2470) ∨ (¬ p5118)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4328) ∨ (¬ p4787) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13188 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23932 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2630) (meaning t m 2656) (meaning t m 2963) (meaning t m 3659) (meaning t m 3689) (meaning t m 4328) (meaning t m 4787) (meaning t m 5118) (meaning t m 5558) source

theorem rule23933 (p2307 p3567 p3568 : Prop) (h : (¬ p3567) ∨ (¬ p3568) ∨ (¬ p2307)) : (¬ p2307) ∨ (¬ p3567) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial23933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory13189 (m.theta 0 6) (m.theta 3 6) (m.theta 6 7)
  exact rule23933 (meaning t m 2307) (meaning t m 3567) (meaning t m 3568) source

theorem rule23934 (p2313 p3567 p3568 : Prop) (h : (¬ p3567) ∨ (¬ p3568) ∨ p2313) : (p2313) ∨ (¬ p3567) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial23934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2313) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory13190 (m.theta 0 6) (m.theta 3 6) (m.theta 6 7)
  exact rule23934 (meaning t m 2313) (meaning t m 3567) (meaning t m 3568) source

theorem rule23935 (p2027 p2156 p2891 p3957 p4235 p4512 p4539 : Prop) (h : (¬ p4539) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2891) ∨ (¬ p3957) ∨ (¬ p2156) ∨ (¬ p4512)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3957) ∨ (¬ p4235) ∨ (¬ p4512) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13191 t (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule23935 (meaning t m 2027) (meaning t m 2156) (meaning t m 2891) (meaning t m 3957) (meaning t m 4235) (meaning t m 4512) (meaning t m 4539) source

theorem rule23936 (p2027 p2146 p2220 p2839 p4242 p4740 : Prop) (h : (¬ p2839) ∨ (¬ p2220) ∨ (¬ p4242) ∨ (¬ p2146) ∨ (¬ p4740) ∨ p2027) : (p2027) ∨ (¬ p2146) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p4242) ∨ (¬ p4740) := by
  classical
  tauto

theorem initial23936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4740)) := by
  have source := ElevenTheory.theory13192 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8)
  exact rule23936 (meaning t m 2027) (meaning t m 2146) (meaning t m 2220) (meaning t m 2839) (meaning t m 4242) (meaning t m 4740) source

theorem rule23943 (p2027 p2630 p2656 p3276 p3355 p3414 p3553 p4787 p5123 p5558 : Prop) (h : (¬ p3553) ∨ (¬ p3355) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p5123) ∨ (¬ p5558) ∨ (¬ p3414) ∨ (¬ p2656) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4787) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13199 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23943 (meaning t m 2027) (meaning t m 2630) (meaning t m 2656) (meaning t m 3276) (meaning t m 3355) (meaning t m 3414) (meaning t m 3553) (meaning t m 4787) (meaning t m 5123) (meaning t m 5558) source

theorem rule23944 (p2027 p2299 p2417 p2598 p3201 p3549 p3591 p4668 p4733 : Prop) (h : (¬ p2299) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4668) ∨ (¬ p3549) ∨ (¬ p4733) ∨ (¬ p2417) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13200 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23944 (meaning t m 2027) (meaning t m 2299) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3549) (meaning t m 3591) (meaning t m 4668) (meaning t m 4733) source

theorem rule23945 (p2027 p2247 p2553 p2598 p3324 p3422 p4154 p4501 p4733 : Prop) (h : (¬ p2247) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p4501) ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p3422) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p3324) ∨ (¬ p3422) ∨ (¬ p4154) ∨ (¬ p4501) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13201 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23945 (meaning t m 2027) (meaning t m 2247) (meaning t m 2553) (meaning t m 2598) (meaning t m 3324) (meaning t m 3422) (meaning t m 4154) (meaning t m 4501) (meaning t m 4733) source

theorem rule23946 (p2027 p2470 p2528 p3266 p3588 p3954 p4391 p4777 p4831 p5190 : Prop) (h : (¬ p3954) ∨ (¬ p4391) ∨ (¬ p3588) ∨ (¬ p4777) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p5190) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4391) ∨ (¬ p4777) ∨ (¬ p4831) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13202 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 7) (m.theta 4 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23946 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3266) (meaning t m 3588) (meaning t m 3954) (meaning t m 4391) (meaning t m 4777) (meaning t m 4831) (meaning t m 5190) source

theorem rule23955 (p1991 p2027 p2545 p2810 p2870 p2952 p4313 p4320 : Prop) (h : (¬ p2870) ∨ p2027 ∨ (¬ p4313) ∨ (¬ p2952) ∨ (¬ p4320) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p1991)) : (¬ p1991) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p2870) ∨ (¬ p2952) ∨ (¬ p4313) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial23955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory13211 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule23955 (meaning t m 1991) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 2870) (meaning t m 2952) (meaning t m 4313) (meaning t m 4320) source

theorem rule23957 (p2027 p2891 p3654 p3743 p4026 p4512 p4558 : Prop) (h : (¬ p3743) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p3654) ∨ (¬ p4558)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13213 t (m.theta 0 6) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule23957 (meaning t m 2027) (meaning t m 2891) (meaning t m 3654) (meaning t m 3743) (meaning t m 4026) (meaning t m 4512) (meaning t m 4558) source

theorem rule23958 (p2027 p2427 p2542 p3054 p4244 p4750 : Prop) (h : (¬ p2542) ∨ (¬ p3054) ∨ (¬ p4244) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p3054) ∨ (¬ p4244) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13214 t (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23958 (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 3054) (meaning t m 4244) (meaning t m 4750) source

theorem rule23959 (p2027 p2363 p2743 p2774 p2952 p3063 p3361 p3918 p4208 p4737 p5059 : Prop) (h : p2027 ∨ (¬ p4208) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p2363) ∨ (¬ p3918) ∨ (¬ p3063) ∨ (¬ p4737) ∨ (¬ p5059)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3361) ∨ (¬ p3918) ∨ (¬ p4208) ∨ (¬ p4737) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial23959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory13215 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23959 (meaning t m 2027) (meaning t m 2363) (meaning t m 2743) (meaning t m 2774) (meaning t m 2952) (meaning t m 3063) (meaning t m 3361) (meaning t m 3918) (meaning t m 4208) (meaning t m 4737) (meaning t m 5059) source

theorem rule23962 (p2027 p2598 p2741 p2928 p3201 p3402 p4737 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p2741) ∨ (¬ p2928) ∨ (¬ p3402) ∨ (¬ p4737)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2741) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p3402) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory13218 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule23962 (meaning t m 2027) (meaning t m 2598) (meaning t m 2741) (meaning t m 2928) (meaning t m 3201) (meaning t m 3402) (meaning t m 4737) source

theorem rule23964 (p2027 p2144 p2383 p2962 p3688 p4358 p4737 : Prop) (h : (¬ p2383) ∨ (¬ p4358) ∨ (¬ p2144) ∨ (¬ p4737) ∨ (¬ p2962) ∨ p2027 ∨ (¬ p3688)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3688) ∨ (¬ p4358) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory13220 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8)
  exact rule23964 (meaning t m 2027) (meaning t m 2144) (meaning t m 2383) (meaning t m 2962) (meaning t m 3688) (meaning t m 4358) (meaning t m 4737) source

theorem rule23965 (p2027 p2132 p2860 p3125 p3266 p3346 p4330 p4425 p4729 : Prop) (h : (¬ p3125) ∨ (¬ p3346) ∨ (¬ p3266) ∨ (¬ p4729) ∨ (¬ p2132) ∨ (¬ p4330) ∨ (¬ p2860) ∨ (¬ p4425) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4330) ∨ (¬ p4425) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory13221 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23965 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3125) (meaning t m 3266) (meaning t m 3346) (meaning t m 4330) (meaning t m 4425) (meaning t m 4729) source

theorem rule23966 (p2027 p2088 p2860 p3696 p4340 p4359 p4507 : Prop) (h : (¬ p2088) ∨ (¬ p2860) ∨ (¬ p4507) ∨ (¬ p3696) ∨ (¬ p4359) ∨ p2027 ∨ (¬ p4340)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2860) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory13222 t (m.theta 0 8) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule23966 (meaning t m 2027) (meaning t m 2088) (meaning t m 2860) (meaning t m 3696) (meaning t m 4340) (meaning t m 4359) (meaning t m 4507) source

theorem rule23967 (p2027 p2122 p2383 p3097 p4358 p4489 : Prop) (h : p2027 ∨ (¬ p4358) ∨ (¬ p2383) ∨ (¬ p3097) ∨ (¬ p4489) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2383) ∨ (¬ p3097) ∨ (¬ p4358) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial23967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory13223 t (m.theta 0 6) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23967 (meaning t m 2027) (meaning t m 2122) (meaning t m 2383) (meaning t m 3097) (meaning t m 4358) (meaning t m 4489) source

theorem rule23968 (p2027 p2144 p2156 p2619 p2657 p3644 p3742 p3758 p4789 p4902 : Prop) (h : (¬ p2144) ∨ (¬ p3758) ∨ (¬ p4789) ∨ (¬ p2156) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p4902) ∨ (¬ p2657) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3758) ∨ (¬ p4789) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13224 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule23968 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2619) (meaning t m 2657) (meaning t m 3644) (meaning t m 3742) (meaning t m 3758) (meaning t m 4789) (meaning t m 4902) source

theorem rule23970 (p2027 p3256 p3989 p4341 p4347 p4560 : Prop) (h : p2027 ∨ (¬ p4560) ∨ (¬ p4347) ∨ (¬ p4341) ∨ (¬ p3989) ∨ (¬ p3256)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3989) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13226 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule23970 (meaning t m 2027) (meaning t m 3256) (meaning t m 3989) (meaning t m 4341) (meaning t m 4347) (meaning t m 4560) source

theorem rule23971 (p3097 p3744 p4025 : Prop) (h : (¬ p3097) ∨ (¬ p4025) ∨ p3744) : (¬ p3097) ∨ (p3744) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial23971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (meaning t m 3744) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory13227 (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule23971 (meaning t m 3097) (meaning t m 3744) (meaning t m 4025) source

theorem rule23972 (p2027 p2144 p2156 p2190 p2437 p3146 p3540 p4133 p4256 p4347 p4383 p4729 : Prop) (h : (¬ p4347) ∨ (¬ p2190) ∨ (¬ p4729) ∨ (¬ p3146) ∨ (¬ p2156) ∨ (¬ p2144) ∨ (¬ p2437) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4383) ∨ p2027 ∨ (¬ p4256)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2437) ∨ (¬ p3146) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4383) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory13228 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23972 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2190) (meaning t m 2437) (meaning t m 3146) (meaning t m 3540) (meaning t m 4133) (meaning t m 4256) (meaning t m 4347) (meaning t m 4383) (meaning t m 4729) source

theorem rule23973 (p2027 p2191 p2241 p2750 p2753 p2774 p3555 p3609 p4134 p4347 p4861 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2241) ∨ (¬ p2774) ∨ (¬ p4861) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3555) ∨ (¬ p3609) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial23973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory13229 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 2 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23973 (meaning t m 2027) (meaning t m 2191) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3555) (meaning t m 3609) (meaning t m 4134) (meaning t m 4347) (meaning t m 4861) source

theorem rule23974 (p2027 p2891 p3369 p3371 p3379 p3556 p5216 : Prop) (h : (¬ p3371) ∨ (¬ p3369) ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3556)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13230 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7)
  exact rule23974 (meaning t m 2027) (meaning t m 2891) (meaning t m 3369) (meaning t m 3371) (meaning t m 3379) (meaning t m 3556) (meaning t m 5216) source

theorem rule23976 (p2027 p3555 p3830 p4173 p4387 p5046 : Prop) (h : (¬ p4173) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p3830) ∨ (¬ p4387)) : (p2027) ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4173) ∨ (¬ p4387) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory13232 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 5 6) (m.theta 5 9)
  exact rule23976 (meaning t m 2027) (meaning t m 3555) (meaning t m 3830) (meaning t m 4173) (meaning t m 4387) (meaning t m 5046) source

theorem rule23980 (p2027 p2122 p2177 p2542 p2829 p3238 p4256 p4438 p5216 : Prop) (h : p2027 ∨ (¬ p4438) ∨ (¬ p2542) ∨ (¬ p5216) ∨ (¬ p3238) ∨ (¬ p2122) ∨ (¬ p4256) ∨ (¬ p2177) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2542) ∨ (¬ p2829) ∨ (¬ p3238) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13236 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23980 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2542) (meaning t m 2829) (meaning t m 3238) (meaning t m 4256) (meaning t m 4438) (meaning t m 5216) source

theorem rule23981 (p2027 p2542 p2982 p3096 p3574 p5046 : Prop) (h : (¬ p5046) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2982) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory13237 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule23981 (meaning t m 2027) (meaning t m 2542) (meaning t m 2982) (meaning t m 3096) (meaning t m 3574) (meaning t m 5046) source

theorem rule23982 (p2027 p2122 p2881 p4138 p4358 p4559 : Prop) (h : (¬ p2122) ∨ (¬ p4358) ∨ (¬ p4559) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial23982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory13238 t (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23982 (meaning t m 2027) (meaning t m 2122) (meaning t m 2881) (meaning t m 4138) (meaning t m 4358) (meaning t m 4559) source

theorem rule23983 (p2027 p2589 p3093 p3309 p3347 p3954 p3989 p4110 p4501 p5216 : Prop) (h : p2027 ∨ (¬ p5216) ∨ (¬ p3954) ∨ (¬ p4501) ∨ (¬ p3989) ∨ (¬ p2589) ∨ (¬ p3309) ∨ (¬ p4110) ∨ (¬ p3347) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13239 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23983 (meaning t m 2027) (meaning t m 2589) (meaning t m 3093) (meaning t m 3309) (meaning t m 3347) (meaning t m 3954) (meaning t m 3989) (meaning t m 4110) (meaning t m 4501) (meaning t m 5216) source

theorem rule23984 (p2027 p2459 p2542 p2589 p2717 p3359 p3471 p4697 p4729 : Prop) (h : (¬ p2542) ∨ (¬ p3359) ∨ (¬ p2717) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2459) ∨ (¬ p4729) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p3359) ∨ (¬ p3471) ∨ (¬ p4697) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory13240 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23984 (meaning t m 2027) (meaning t m 2459) (meaning t m 2542) (meaning t m 2589) (meaning t m 2717) (meaning t m 3359) (meaning t m 3471) (meaning t m 4697) (meaning t m 4729) source

theorem rule23985 (p2027 p3483 p4345 p4358 p5118 p5580 : Prop) (h : (¬ p4358) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p4345) ∨ (¬ p5580) ∨ (¬ p3483)) : (p2027) ∨ (¬ p3483) ∨ (¬ p4345) ∨ (¬ p4358) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13241 t (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule23985 (meaning t m 2027) (meaning t m 3483) (meaning t m 4345) (meaning t m 4358) (meaning t m 5118) (meaning t m 5580) source

theorem rule23986 (p4381 p4425 p4636 : Prop) (h : (¬ p4381) ∨ (¬ p4636) ∨ p4425) : (¬ p4381) ∨ (p4425) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial23986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4381)) ∨ (meaning t m 4425) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory13242 (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23986 (meaning t m 4381) (meaning t m 4425) (meaning t m 4636) source

theorem rule23987 (p2027 p2088 p2578 p2870 p3096 p4114 p4261 p4359 p4558 p5315 : Prop) (h : (¬ p2578) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4359) ∨ (¬ p4558) ∨ (¬ p4261) ∨ (¬ p5315) ∨ (¬ p4114) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2578) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4359) ∨ (¬ p4558) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial23987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory13243 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 8) (m.theta 2 5) (m.theta 2 8) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule23987 (meaning t m 2027) (meaning t m 2088) (meaning t m 2578) (meaning t m 2870) (meaning t m 3096) (meaning t m 4114) (meaning t m 4261) (meaning t m 4359) (meaning t m 4558) (meaning t m 5315) source

theorem rule23988 (p2027 p2252 p2657 p2750 p2753 p2774 p3461 p3483 p3742 p4831 p5503 : Prop) (h : (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p4831) ∨ (¬ p3483) ∨ (¬ p2774) ∨ (¬ p5503) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p2657) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial23988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory13244 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule23988 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3461) (meaning t m 3483) (meaning t m 3742) (meaning t m 4831) (meaning t m 5503) source

theorem rule23991 (p2027 p2743 p2963 p3361 p3471 p3527 p3568 p3570 p4424 p4556 p4737 : Prop) (h : (¬ p4424) ∨ (¬ p2743) ∨ (¬ p3527) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2963) ∨ (¬ p4737) ∨ (¬ p3568) ∨ (¬ p4556) ∨ (¬ p3361)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4424) ∨ (¬ p4556) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory13247 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23991 (meaning t m 2027) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 3471) (meaning t m 3527) (meaning t m 3568) (meaning t m 3570) (meaning t m 4424) (meaning t m 4556) (meaning t m 4737) source

theorem rule23993 (p2995 p4156 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p4156) ∨ p2995) : (p2995) ∨ (¬ p4156) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial23993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2995) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory13249 (m.theta 3 5) (m.theta 3 6) (m.theta 3 7)
  exact rule23993 (meaning t m 2995) (meaning t m 4156) (meaning t m 4336) source

theorem rule23996 (p2027 p2668 p3019 p3584 p3956 p4750 : Prop) (h : (¬ p2668) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p3019) ∨ (¬ p3956) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13252 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule23996 (meaning t m 2027) (meaning t m 2668) (meaning t m 3019) (meaning t m 3584) (meaning t m 3956) (meaning t m 4750) source

theorem rule23998 (p2027 p2839 p3584 p3585 p3695 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p3695) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2839) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory13254 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6)
  exact rule23998 (meaning t m 2027) (meaning t m 2839) (meaning t m 3584) (meaning t m 3585) (meaning t m 3695) (meaning t m 4715) source

theorem rule23999 (p2027 p2132 p2780 p2870 p4428 p4558 : Prop) (h : (¬ p4428) ∨ (¬ p2870) ∨ (¬ p2780) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2870) ∨ (¬ p4428) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13255 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7)
  exact rule23999 (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 2870) (meaning t m 4428) (meaning t m 4558) source

theorem rule24001 (p2027 p2252 p2383 p2657 p2750 p2753 p2786 p3266 p3609 p3742 p4831 p4857 p5503 : Prop) (h : p2027 ∨ (¬ p4831) ∨ (¬ p5503) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3742) ∨ (¬ p2786) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p4857) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p4857) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial24001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 4857)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory13257 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24001 (meaning t m 2027) (meaning t m 2252) (meaning t m 2383) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 3266) (meaning t m 3609) (meaning t m 3742) (meaning t m 4831) (meaning t m 4857) (meaning t m 5503) source

theorem rule24002 (p2027 p2252 p2363 p2657 p2750 p2753 p2774 p2819 p4256 p4286 p5118 : Prop) (h : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4286) ∨ (¬ p2753) ∨ (¬ p2819) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p5118) ∨ (¬ p2657) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial24002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory13258 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24002 (meaning t m 2027) (meaning t m 2252) (meaning t m 2363) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 4256) (meaning t m 4286) (meaning t m 5118) source

theorem rule24003 (p2027 p2146 p2383 p2962 p3758 p3989 : Prop) (h : (¬ p3758) ∨ (¬ p2146) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2383) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3758) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial24003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory13259 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule24003 (meaning t m 2027) (meaning t m 2146) (meaning t m 2383) (meaning t m 2962) (meaning t m 3758) (meaning t m 3989) source

theorem rule24008 (p2027 p2156 p2870 p2911 p3548 p3758 p4366 p4521 p4647 : Prop) (h : (¬ p3548) ∨ (¬ p2911) ∨ (¬ p4366) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4521) ∨ (¬ p3758) ∨ (¬ p2156) ∨ (¬ p4647)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2870) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3758) ∨ (¬ p4366) ∨ (¬ p4521) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial24008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory13264 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule24008 (meaning t m 2027) (meaning t m 2156) (meaning t m 2870) (meaning t m 2911) (meaning t m 3548) (meaning t m 3758) (meaning t m 4366) (meaning t m 4521) (meaning t m 4647) source

theorem rule24016 (p2027 p3555 p3830 p4385 p4387 p4878 : Prop) (h : (¬ p4387) ∨ (¬ p4878) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3555) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4385) ∨ (¬ p4387) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial24016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory13272 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 2 5) (m.theta 5 9)
  exact rule24016 (meaning t m 2027) (meaning t m 3555) (meaning t m 3830) (meaning t m 4385) (meaning t m 4387) (meaning t m 4878) source

theorem rule24017 (p2027 p2299 p2396 p2911 p3690 p4647 : Prop) (h : p2027 ∨ (¬ p2911) ∨ (¬ p2396) ∨ (¬ p4647) ∨ (¬ p2299) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2911) ∨ (¬ p3690) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial24017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory13273 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24017 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2911) (meaning t m 3690) (meaning t m 4647) source

theorem rule24020 (p2027 p2122 p2254 p2608 p2829 p2952 p3952 p3989 p4501 : Prop) (h : (¬ p3952) ∨ (¬ p2952) ∨ (¬ p3989) ∨ (¬ p2122) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2254) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13276 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24020 (meaning t m 2027) (meaning t m 2122) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 2952) (meaning t m 3952) (meaning t m 3989) (meaning t m 4501) source

theorem rule24021 (p2027 p2589 p3389 p3486 p3569 p4243 p4882 : Prop) (h : (¬ p3569) ∨ (¬ p4243) ∨ (¬ p3389) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4882)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4243) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial24021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory13277 t (m.theta 0 4) (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule24021 (meaning t m 2027) (meaning t m 2589) (meaning t m 3389) (meaning t m 3486) (meaning t m 3569) (meaning t m 4243) (meaning t m 4882) source

theorem rule24023 (p2027 p2210 p2252 p2299 p2619 p2750 p2963 p3568 p3954 p4243 p4902 : Prop) (h : (¬ p3954) ∨ (¬ p4243) ∨ (¬ p3568) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2963) ∨ (¬ p4902) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13279 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule24023 (meaning t m 2027) (meaning t m 2210) (meaning t m 2252) (meaning t m 2299) (meaning t m 2619) (meaning t m 2750) (meaning t m 2963) (meaning t m 3568) (meaning t m 3954) (meaning t m 4243) (meaning t m 4902) source

theorem rule24024 (p2027 p2156 p2427 p3556 p3758 p4882 : Prop) (h : (¬ p2156) ∨ (¬ p4882) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial24024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory13280 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24024 (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 3556) (meaning t m 3758) (meaning t m 4882) source

theorem rule24025 (p2027 p2476 p3083 p3399 p3631 p3742 p4107 p4712 p5193 : Prop) (h : (¬ p3083) ∨ (¬ p3399) ∨ (¬ p5193) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p3742) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4712) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13281 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9)
  exact rule24025 (meaning t m 2027) (meaning t m 2476) (meaning t m 3083) (meaning t m 3399) (meaning t m 3631) (meaning t m 3742) (meaning t m 4107) (meaning t m 4712) (meaning t m 5193) source

theorem rule24026 (p2027 p2839 p2870 p3688 p4428 p4558 : Prop) (h : (¬ p2839) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p4428) ∨ (¬ p3688) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13282 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7)
  exact rule24026 (meaning t m 2027) (meaning t m 2839) (meaning t m 2870) (meaning t m 3688) (meaning t m 4428) (meaning t m 4558) source

theorem rule24028 (p2027 p2449 p2995 p3690 p3952 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13284 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule24028 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3690) (meaning t m 3952) (meaning t m 4558) source

theorem rule24029 (p2027 p2911 p3570 p3741 p4110 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p4110) ∨ (¬ p3741) ∨ (¬ p3570) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13285 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule24029 (meaning t m 2027) (meaning t m 2911) (meaning t m 3570) (meaning t m 3741) (meaning t m 4110) (meaning t m 4558) source

theorem rule24031 (p2027 p2254 p2952 p3222 p3276 p3379 p4320 p4831 p5660 : Prop) (h : (¬ p3276) ∨ (¬ p3222) ∨ (¬ p2952) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4831) ∨ (¬ p4320) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4320) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial24031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory13287 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24031 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 4320) (meaning t m 4831) (meaning t m 5660) source

theorem rule24032 (p2608 p3399 p3687 : Prop) (h : (¬ p3687) ∨ (¬ p2608) ∨ p3399) : (¬ p2608) ∨ (p3399) ∨ (¬ p3687) := by
  classical
  tauto

theorem initial24032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (meaning t m 3399) ∨ (¬ (meaning t m 3687)) := by
  have source := ElevenTheory.theory13288 (m.theta 0 1) (m.theta 1 2) (m.theta 1 7)
  exact rule24032 (meaning t m 2608) (meaning t m 3399) (meaning t m 3687) source

theorem rule24034 (p3822 p3955 p3956 p4390 : Prop) (h : (¬ p4390) ∨ (¬ p3955) ∨ (¬ p3822) ∨ p3956) : (¬ p3822) ∨ (¬ p3955) ∨ (p3956) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial24034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) ∨ (meaning t m 3956) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory13290 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24034 (meaning t m 3822) (meaning t m 3955) (meaning t m 3956) (meaning t m 4390) source

theorem rule24035 (p2352 p3822 p3955 p4390 : Prop) (h : (¬ p4390) ∨ (¬ p3955) ∨ (¬ p3822) ∨ (¬ p2352)) : (¬ p2352) ∨ (¬ p3822) ∨ (¬ p3955) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial24035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory13291 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24035 (meaning t m 2352) (meaning t m 3822) (meaning t m 3955) (meaning t m 4390) source

theorem rule24036 (p2027 p2254 p2493 p2553 p2952 p3379 p3952 p3989 p4501 : Prop) (h : (¬ p3379) ∨ (¬ p2553) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p4501) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13292 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24036 (meaning t m 2027) (meaning t m 2254) (meaning t m 2493) (meaning t m 2553) (meaning t m 2952) (meaning t m 3379) (meaning t m 3952) (meaning t m 3989) (meaning t m 4501) source

theorem rule24038 (p2027 p2427 p3136 p3745 p4195 p4241 p4558 : Prop) (h : (¬ p4241) ∨ (¬ p4195) ∨ (¬ p3136) ∨ (¬ p2427) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p4558)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4241) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13294 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24038 (meaning t m 2027) (meaning t m 2427) (meaning t m 3136) (meaning t m 3745) (meaning t m 4195) (meaning t m 4241) (meaning t m 4558) source

theorem rule24039 (p2027 p2295 p2313 p2797 p3983 p4787 : Prop) (h : (¬ p3983) ∨ (¬ p2295) ∨ (¬ p4787) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p2313)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2797) ∨ (¬ p3983) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial24039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13295 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule24039 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2797) (meaning t m 3983) (meaning t m 4787) source

theorem rule24041 (p2027 p2352 p2493 p3365 p3379 p3553 p3572 p4133 p4736 : Prop) (h : (¬ p3572) ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2493)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13297 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8)
  exact rule24041 (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 3365) (meaning t m 3379) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4736) source

theorem rule24042 (p1985 p2427 p3498 p4608 : Prop) (h : p3498 ∨ (¬ p2427) ∨ p4608 ∨ (¬ p1985)) : (¬ p1985) ∨ (¬ p2427) ∨ (p3498) ∨ (p4608) := by
  classical
  tauto

theorem initial24042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 3498) ∨ (meaning t m 4608) := by
  have source := ElevenTheory.theory13298 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 7)
  exact rule24042 (meaning t m 1985) (meaning t m 2427) (meaning t m 3498) (meaning t m 4608) source

theorem rule24043 (p1998 p2027 p2177 p2499 p2573 p2699 p2922 p4079 p4710 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2499) ∨ (¬ p4079) ∨ (¬ p2177) ∨ (¬ p2573) ∨ (¬ p4710) ∨ (¬ p2922) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (p2699) ∨ (¬ p2922) ∨ (¬ p4079) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial24043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory13299 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24043 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2499) (meaning t m 2573) (meaning t m 2699) (meaning t m 2922) (meaning t m 4079) (meaning t m 4710) source

theorem rule24044 (p2027 p2470 p2630 p2656 p2952 p3692 p3694 p3979 p4157 p4787 p5051 p5122 : Prop) (h : (¬ p5051) ∨ (¬ p3694) ∨ (¬ p2656) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2470) ∨ (¬ p4787) ∨ (¬ p2630) ∨ (¬ p3979) ∨ (¬ p5122) ∨ (¬ p4157)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2952) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p4157) ∨ (¬ p4787) ∨ (¬ p5051) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial24044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5051)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory13300 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24044 (meaning t m 2027) (meaning t m 2470) (meaning t m 2630) (meaning t m 2656) (meaning t m 2952) (meaning t m 3692) (meaning t m 3694) (meaning t m 3979) (meaning t m 4157) (meaning t m 4787) (meaning t m 5051) (meaning t m 5122) source

theorem rule24046 (p2027 p2657 p3422 p3475 p3574 p4787 : Prop) (h : (¬ p4787) ∨ (¬ p2657) ∨ (¬ p3475) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p3422)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial24046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13302 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule24046 (meaning t m 2027) (meaning t m 2657) (meaning t m 3422) (meaning t m 3475) (meaning t m 3574) (meaning t m 4787) source

theorem rule24050 (p2027 p2252 p2748 p2963 p3055 p3324 p3366 p3537 p3609 p4749 p5118 p5580 : Prop) (h : (¬ p3609) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p4749) ∨ (¬ p2252) ∨ (¬ p3537) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p2963) ∨ (¬ p2748) ∨ (¬ p5580) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3055) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4749) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial24050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13306 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24050 (meaning t m 2027) (meaning t m 2252) (meaning t m 2748) (meaning t m 2963) (meaning t m 3055) (meaning t m 3324) (meaning t m 3366) (meaning t m 3537) (meaning t m 3609) (meaning t m 4749) (meaning t m 5118) (meaning t m 5580) source

theorem rule24052 (p2027 p2254 p2264 p2493 p3379 p3551 p3564 p3947 p4621 p4849 : Prop) (h : p2027 ∨ (¬ p4849) ∨ (¬ p2254) ∨ (¬ p2264) ∨ (¬ p4621) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3379) ∨ (¬ p2493) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2264) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3947) ∨ (¬ p4621) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial24052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory13308 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule24052 (meaning t m 2027) (meaning t m 2254) (meaning t m 2264) (meaning t m 2493) (meaning t m 3379) (meaning t m 3551) (meaning t m 3564) (meaning t m 3947) (meaning t m 4621) (meaning t m 4849) source

theorem rule24055 (p2027 p2819 p3569 p3644 p3822 p4170 p4403 p4556 : Prop) (h : (¬ p4403) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3569) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4556) ∨ (¬ p4170)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3569) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4403) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial24055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory13311 t (m.theta 0 8) (m.theta 2 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule24055 (meaning t m 2027) (meaning t m 2819) (meaning t m 3569) (meaning t m 3644) (meaning t m 3822) (meaning t m 4170) (meaning t m 4403) (meaning t m 4556) source

theorem rule24057 (p2027 p2870 p2952 p3475 p3582 p4320 p4787 : Prop) (h : (¬ p3475) ∨ (¬ p3582) ∨ (¬ p2870) ∨ (¬ p4787) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2952) ∨ (¬ p3475) ∨ (¬ p3582) ∨ (¬ p4320) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial24057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13313 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule24057 (meaning t m 2027) (meaning t m 2870) (meaning t m 2952) (meaning t m 3475) (meaning t m 3582) (meaning t m 4320) (meaning t m 4787) source

theorem rule24063 (p2743 p3588 p4357 : Prop) (h : (¬ p4357) ∨ (¬ p2743) ∨ p3588) : (¬ p2743) ∨ (p3588) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial24063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (meaning t m 3588) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory13319 (m.theta 1 2) (m.theta 2 3) (m.theta 2 7)
  exact rule24063 (meaning t m 2743) (meaning t m 3588) (meaning t m 4357) source

theorem rule24065 (p2027 p2774 p2810 p3365 p4328 p4975 : Prop) (h : (¬ p2810) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4975) ∨ (¬ p4328) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4328) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial24065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory13321 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6)
  exact rule24065 (meaning t m 2027) (meaning t m 2774) (meaning t m 2810) (meaning t m 3365) (meaning t m 4328) (meaning t m 4975) source

theorem rule24067 (p2027 p2668 p2829 p4242 p4843 p4857 : Prop) (h : (¬ p2829) ∨ p2027 ∨ (¬ p4857) ∨ (¬ p4843) ∨ (¬ p2668) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4843) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial24067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4843)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory13323 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8)
  exact rule24067 (meaning t m 2027) (meaning t m 2668) (meaning t m 2829) (meaning t m 4242) (meaning t m 4843) (meaning t m 4857) source

theorem rule24068 (p2027 p2264 p2311 p2995 p3551 p4208 p4356 p5043 : Prop) (h : (¬ p2311) ∨ (¬ p4208) ∨ (¬ p4356) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p5043)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2311) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p4208) ∨ (¬ p4356) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial24068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory13324 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8)
  exact rule24068 (meaning t m 2027) (meaning t m 2264) (meaning t m 2311) (meaning t m 2995) (meaning t m 3551) (meaning t m 4208) (meaning t m 4356) (meaning t m 5043) source

theorem rule24069 (p2027 p2252 p2717 p2748 p2963 p3055 p3471 p3568 p4107 p4666 p4749 : Prop) (h : (¬ p4749) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p4666) ∨ (¬ p3055) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2717) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial24069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory13325 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24069 (meaning t m 2027) (meaning t m 2252) (meaning t m 2717) (meaning t m 2748) (meaning t m 2963) (meaning t m 3055) (meaning t m 3471) (meaning t m 3568) (meaning t m 4107) (meaning t m 4666) (meaning t m 4749) source

theorem rule24071 (p2027 p2563 p3237 p3680 p4425 p5043 : Prop) (h : (¬ p5043) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3237) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial24071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory13327 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule24071 (meaning t m 2027) (meaning t m 2563) (meaning t m 3237) (meaning t m 3680) (meaning t m 4425) (meaning t m 5043) source

theorem rule24072 (p2027 p2254 p2299 p2373 p2406 p2963 p3379 p3568 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2406) ∨ (¬ p2373) ∨ (¬ p2963) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3568)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13328 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule24072 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2373) (meaning t m 2406) (meaning t m 2963) (meaning t m 3379) (meaning t m 3568) (meaning t m 4902) source

theorem rule24073 (p2027 p2254 p2406 p2982 p3379 p3414 p3553 p4348 p4450 : Prop) (h : (¬ p3553) ∨ (¬ p3414) ∨ (¬ p4348) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p4450) ∨ (¬ p2406) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial24073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory13329 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24073 (meaning t m 2027) (meaning t m 2254) (meaning t m 2406) (meaning t m 2982) (meaning t m 3379) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) (meaning t m 4450) source

theorem rule24074 (p4037 p4118 p4171 p4341 : Prop) (h : (¬ p4171) ∨ (¬ p4341) ∨ (¬ p4037) ∨ p4118) : (¬ p4037) ∨ (p4118) ∨ (¬ p4171) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial24074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4037)) ∨ (meaning t m 4118) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory13330 (m.theta 3 6) (m.theta 3 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24074 (meaning t m 4037) (meaning t m 4118) (meaning t m 4171) (meaning t m 4341) source

theorem rule24076 (p2027 p2542 p2619 p3693 p4256 p4885 : Prop) (h : (¬ p3693) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2542) ∨ (¬ p2619) ∨ (¬ p4885)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2619) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial24076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory13332 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule24076 (meaning t m 2027) (meaning t m 2542) (meaning t m 2619) (meaning t m 3693) (meaning t m 4256) (meaning t m 4885) source

theorem rule24077 (p2027 p2138 p3366 p3399 p3452 p3570 p3631 p4244 p4376 p4668 : Prop) (h : (¬ p4244) ∨ (¬ p3631) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p3399) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p4244) ∨ (¬ p4376) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13333 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24077 (meaning t m 2027) (meaning t m 2138) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3570) (meaning t m 3631) (meaning t m 4244) (meaning t m 4376) (meaning t m 4668) source

theorem rule24078 (p2027 p3093 p3309 p3860 p4501 p4993 : Prop) (h : (¬ p3309) ∨ (¬ p4501) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p4993) ∨ (¬ p3093)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3860) ∨ (¬ p4501) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial24078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory13334 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 6 7) (m.theta 6 8)
  exact rule24078 (meaning t m 2027) (meaning t m 3093) (meaning t m 3309) (meaning t m 3860) (meaning t m 4501) (meaning t m 4993) source

theorem rule24079 (p2027 p2534 p3246 p3570 p4420 p4443 : Prop) (h : (¬ p4420) ∨ (¬ p3570) ∨ (¬ p2534) ∨ (¬ p4443) ∨ p2027 ∨ (¬ p3246)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4420) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial24079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory13335 t (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24079 (meaning t m 2027) (meaning t m 2534) (meaning t m 3246) (meaning t m 3570) (meaning t m 4420) (meaning t m 4443) source

theorem rule24080 (p2027 p2383 p2781 p3365 p3564 p3572 p3947 p3956 p4621 : Prop) (h : (¬ p3572) ∨ (¬ p3365) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2781) ∨ (¬ p3947) ∨ (¬ p3564) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p3956) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial24080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory13336 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule24080 (meaning t m 2027) (meaning t m 2383) (meaning t m 2781) (meaning t m 3365) (meaning t m 3564) (meaning t m 3572) (meaning t m 3947) (meaning t m 3956) (meaning t m 4621) source

theorem rule24081 (p2027 p3365 p3366 p3399 p3452 p3553 p3572 p3631 p4376 p4668 : Prop) (h : (¬ p4376) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3452) ∨ (¬ p3399) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3366) ∨ (¬ p3631)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3631) ∨ (¬ p4376) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13337 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24081 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3553) (meaning t m 3572) (meaning t m 3631) (meaning t m 4376) (meaning t m 4668) source

theorem rule24082 (p2027 p2449 p2685 p3877 p4548 p4668 : Prop) (h : (¬ p3877) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p4548) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p3877) ∨ (¬ p4548) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13338 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 7 9)
  exact rule24082 (meaning t m 2027) (meaning t m 2449) (meaning t m 2685) (meaning t m 3877) (meaning t m 4548) (meaning t m 4668) source

theorem rule24084 (p2027 p3572 p3755 p4107 p4361 p4660 : Prop) (h : (¬ p3572) ∨ (¬ p4660) ∨ p2027 ∨ (¬ p4361) ∨ (¬ p4107) ∨ (¬ p3755)) : (p2027) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4361) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial24084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory13340 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 7 9)
  exact rule24084 (meaning t m 2027) (meaning t m 3572) (meaning t m 3755) (meaning t m 4107) (meaning t m 4361) (meaning t m 4660) source

theorem rule24085 (p2027 p2138 p2352 p2363 p2573 p3366 p3519 p3694 p4376 p5118 p5568 : Prop) (h : (¬ p2138) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p5568) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p5118) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3694) ∨ (¬ p4376) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13341 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24085 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3366) (meaning t m 3519) (meaning t m 3694) (meaning t m 4376) (meaning t m 5118) (meaning t m 5568) source

theorem rule24086 (p2027 p2191 p2248 p2264 p2459 p2807 p3555 p5118 p5568 : Prop) (h : (¬ p2248) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p5568) ∨ (¬ p2807) ∨ (¬ p3555) ∨ (¬ p2264) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3555) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13342 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24086 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3555) (meaning t m 5118) (meaning t m 5568) source

theorem rule24087 (p2027 p2440 p2891 p3556 p3948 p4031 p4814 : Prop) (h : (¬ p4031) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3556) ∨ (¬ p3948) ∨ (¬ p2891) ∨ (¬ p4814)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial24087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory13343 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule24087 (meaning t m 2027) (meaning t m 2440) (meaning t m 2891) (meaning t m 3556) (meaning t m 3948) (meaning t m 4031) (meaning t m 4814) source

theorem rule24089 (p2299 p3945 p4107 : Prop) (h : (¬ p3945) ∨ (¬ p4107) ∨ p2299) : (p2299) ∨ (¬ p3945) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial24089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2299) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory13345 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24089 (meaning t m 2299) (meaning t m 3945) (meaning t m 4107) source

theorem rule24091 (p2027 p2307 p2786 p3055 p3822 p4749 p4841 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p3055) ∨ (¬ p4749) ∨ (¬ p4841) ∨ (¬ p3822) ∨ (¬ p2786)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3822) ∨ (¬ p4749) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial24091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory13347 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule24091 (meaning t m 2027) (meaning t m 2307) (meaning t m 2786) (meaning t m 3055) (meaning t m 3822) (meaning t m 4749) (meaning t m 4841) source

theorem rule24093 (p2027 p2579 p2662 p3422 p3475 p4315 p4701 : Prop) (h : p2027 ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p2579) ∨ (¬ p4315) ∨ (¬ p2662) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p4315) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13349 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule24093 (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 3422) (meaning t m 3475) (meaning t m 4315) (meaning t m 4701) source

theorem rule24094 (p2027 p2662 p3201 p3475 p3540 p4315 p4701 : Prop) (h : p2027 ∨ (¬ p3475) ∨ (¬ p4315) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p4701) ∨ (¬ p2662)) : (p2027) ∨ (¬ p2662) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p3540) ∨ (¬ p4315) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13350 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule24094 (meaning t m 2027) (meaning t m 2662) (meaning t m 3201) (meaning t m 3475) (meaning t m 3540) (meaning t m 4315) (meaning t m 4701) source

theorem rule24099 (p2027 p2210 p2528 p2881 p2891 p3055 p4340 p4438 p4736 p5368 : Prop) (h : (¬ p5368) ∨ (¬ p4340) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p4438) ∨ (¬ p2881) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p4340) ∨ (¬ p4438) ∨ (¬ p4736) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial24099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory13355 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule24099 (meaning t m 2027) (meaning t m 2210) (meaning t m 2528) (meaning t m 2881) (meaning t m 2891) (meaning t m 3055) (meaning t m 4340) (meaning t m 4438) (meaning t m 4736) (meaning t m 5368) source

theorem rule24100 (p2027 p2459 p3055 p3399 p3527 p3584 p4137 p4604 p4736 : Prop) (h : (¬ p3055) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3399) ∨ (¬ p2459) ∨ (¬ p3584) ∨ (¬ p4736) ∨ (¬ p4137) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13356 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24100 (meaning t m 2027) (meaning t m 2459) (meaning t m 3055) (meaning t m 3399) (meaning t m 3527) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4736) source

theorem rule24101 (p2027 p2528 p2542 p4340 p4355 p4750 p5368 : Prop) (h : (¬ p4355) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2542) ∨ (¬ p4750) ∨ (¬ p2528) ∨ (¬ p5368)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2542) ∨ (¬ p4340) ∨ (¬ p4355) ∨ (¬ p4750) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial24101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory13357 t (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule24101 (meaning t m 2027) (meaning t m 2528) (meaning t m 2542) (meaning t m 4340) (meaning t m 4355) (meaning t m 4750) (meaning t m 5368) source

theorem rule24102 (p2027 p2459 p2476 p2534 p2608 p2619 p2839 p4902 p5193 : Prop) (h : (¬ p2476) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p2619) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4902) ∨ (¬ p2608) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13358 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24102 (meaning t m 2027) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 4902) (meaning t m 5193) source

theorem rule24105 (p2027 p2252 p2952 p3027 p3879 p4110 p4333 p4558 : Prop) (h : (¬ p4110) ∨ (¬ p2952) ∨ (¬ p2252) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3879) ∨ (¬ p4333)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3879) ∨ (¬ p4110) ∨ (¬ p4333) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13361 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24105 (meaning t m 2027) (meaning t m 2252) (meaning t m 2952) (meaning t m 3027) (meaning t m 3879) (meaning t m 4110) (meaning t m 4333) (meaning t m 4558) source

theorem rule24106 (p2027 p2696 p2742 p3189 p3346 p3363 p3585 p4009 p4425 p4737 p5119 : Prop) (h : (¬ p3189) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p4737) ∨ (¬ p4009) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3363)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4009) ∨ (¬ p4425) ∨ (¬ p4737) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial24106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13362 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 9) (m.theta 8 10) (m.theta 9 10)
  exact rule24106 (meaning t m 2027) (meaning t m 2696) (meaning t m 2742) (meaning t m 3189) (meaning t m 3346) (meaning t m 3363) (meaning t m 3585) (meaning t m 4009) (meaning t m 4425) (meaning t m 4737) (meaning t m 5119) source

theorem rule24109 (p2027 p2630 p2951 p3212 p4385 p4392 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p4392) ∨ (¬ p2951) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13365 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9)
  exact rule24109 (meaning t m 2027) (meaning t m 2630) (meaning t m 2951) (meaning t m 3212) (meaning t m 4385) (meaning t m 4392) (meaning t m 4701) source

theorem rule24110 (p2027 p2284 p2727 p3368 p4173 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p3368) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2727) ∨ (¬ p3368) ∨ (¬ p4173) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13366 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule24110 (meaning t m 2027) (meaning t m 2284) (meaning t m 2727) (meaning t m 3368) (meaning t m 4173) (meaning t m 4701) source

theorem rule24112 (p2027 p2727 p2807 p2952 p2996 p4701 : Prop) (h : (¬ p2952) ∨ (¬ p4701) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2996) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13368 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule24112 (meaning t m 2027) (meaning t m 2727) (meaning t m 2807) (meaning t m 2952) (meaning t m 2996) (meaning t m 4701) source

theorem rule24114 (p2027 p2138 p2598 p2922 p3590 p3698 p4646 : Prop) (h : (¬ p2138) ∨ (¬ p3698) ∨ (¬ p4646) ∨ (¬ p3590) ∨ (¬ p2922) ∨ (¬ p2598) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3698) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial24114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory13370 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule24114 (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2922) (meaning t m 3590) (meaning t m 3698) (meaning t m 4646) source

theorem rule24117 (p2027 p2146 p2192 p3051 p3486 p3758 : Prop) (h : (¬ p2192) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2146) ∨ (¬ p3486) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2192) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial24117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory13373 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24117 (meaning t m 2027) (meaning t m 2146) (meaning t m 2192) (meaning t m 3051) (meaning t m 3486) (meaning t m 3758) source

theorem rule24118 (p2027 p2579 p2608 p2707 p2717 p3016 p4256 p4438 p5193 : Prop) (h : (¬ p2717) ∨ (¬ p5193) ∨ (¬ p2608) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2707) ∨ (¬ p2579) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13374 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8)
  exact rule24118 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3016) (meaning t m 4256) (meaning t m 4438) (meaning t m 5193) source

theorem rule24119 (p2027 p2192 p2427 p3486 p3758 p4882 : Prop) (h : (¬ p3758) ∨ (¬ p4882) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2427) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p3758) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial24119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory13375 t (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24119 (meaning t m 2027) (meaning t m 2192) (meaning t m 2427) (meaning t m 3486) (meaning t m 3758) (meaning t m 4882) source

theorem rule24121 (p2027 p2177 p2230 p2922 p3238 p3425 p3659 p4079 p4276 p4736 : Prop) (h : (¬ p4079) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2177) ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p4736) ∨ (¬ p3659) ∨ (¬ p4276) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4079) ∨ (¬ p4276) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13377 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24121 (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 2922) (meaning t m 3238) (meaning t m 3425) (meaning t m 3659) (meaning t m 4079) (meaning t m 4276) (meaning t m 4736) source

theorem rule24122 (p2027 p2122 p2313 p2577 p2662 p4315 p4426 p4701 : Prop) (h : (¬ p2122) ∨ (¬ p4701) ∨ (¬ p2662) ∨ (¬ p4426) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p2577) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p4315) ∨ (¬ p4426) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13378 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 7)
  exact rule24122 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2577) (meaning t m 2662) (meaning t m 4315) (meaning t m 4426) (meaning t m 4701) source

theorem rule24123 (p2027 p2241 p2641 p3055 p3323 p3876 p4278 p4621 p4736 : Prop) (h : (¬ p4736) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p4278) ∨ (¬ p3055) ∨ (¬ p4621) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13379 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9)
  exact rule24123 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3055) (meaning t m 3323) (meaning t m 3876) (meaning t m 4278) (meaning t m 4621) (meaning t m 4736) source

theorem rule24125 (p2027 p2459 p3156 p3949 p4208 p4902 : Prop) (h : (¬ p3949) ∨ (¬ p3156) ∨ (¬ p2459) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p4208)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4208) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13381 t (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24125 (meaning t m 2027) (meaning t m 2459) (meaning t m 3156) (meaning t m 3949) (meaning t m 4208) (meaning t m 4902) source

theorem rule24128 (p2027 p2532 p3105 p3694 p4134 p4347 : Prop) (h : (¬ p4134) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3105) ∨ (¬ p2532) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4134) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial24128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory13384 t (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24128 (meaning t m 2027) (meaning t m 2532) (meaning t m 3105) (meaning t m 3694) (meaning t m 4134) (meaning t m 4347) source

theorem rule24134 (p1983 p2027 p2938 p3105 p3461 p4244 p4381 p5045 : Prop) (h : (¬ p3461) ∨ (¬ p5045) ∨ (¬ p4381) ∨ (¬ p1983) ∨ p2938 ∨ p2027 ∨ (¬ p3105) ∨ (¬ p4244)) : (¬ p1983) ∨ (p2027) ∨ (p2938) ∨ (¬ p3105) ∨ (¬ p3461) ∨ (¬ p4244) ∨ (¬ p4381) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial24134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory13390 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24134 (meaning t m 1983) (meaning t m 2027) (meaning t m 2938) (meaning t m 3105) (meaning t m 3461) (meaning t m 4244) (meaning t m 4381) (meaning t m 5045) source

theorem rule24137 (p2027 p2946 p3055 p3146 p3156 p3874 p4286 p4786 p5118 : Prop) (h : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p5118)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4786) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial24137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory13393 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24137 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3146) (meaning t m 3156) (meaning t m 3874) (meaning t m 4286) (meaning t m 4786) (meaning t m 5118) source

theorem rule24139 (p2027 p2248 p2373 p2542 p2651 p3588 p3659 p3954 p4902 : Prop) (h : (¬ p3588) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p2651) ∨ (¬ p2542) ∨ (¬ p2248) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13395 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule24139 (meaning t m 2027) (meaning t m 2248) (meaning t m 2373) (meaning t m 2542) (meaning t m 2651) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4902) source

theorem rule24141 (p3961 p4416 p5206 : Prop) (h : (¬ p5206) ∨ (¬ p3961) ∨ p4416) : (¬ p3961) ∨ (p4416) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial24141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3961)) ∨ (meaning t m 4416) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory13397 (m.theta 0 1) (m.theta 0 7) (m.theta 0 8)
  exact rule24141 (meaning t m 3961) (meaning t m 4416) (meaning t m 5206) source

theorem rule24142 (p2027 p2166 p2284 p3497 p4363 p5043 : Prop) (h : (¬ p5043) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2284) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p4363) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial24142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory13398 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 5 9)
  exact rule24142 (meaning t m 2027) (meaning t m 2166) (meaning t m 2284) (meaning t m 3497) (meaning t m 4363) (meaning t m 5043) source

theorem rule24145 (p2027 p2230 p2274 p2563 p2608 p3519 p3591 p3923 p4376 p4501 : Prop) (h : (¬ p4376) ∨ (¬ p3519) ∨ (¬ p2563) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p2230) ∨ (¬ p4501)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13401 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24145 (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 2608) (meaning t m 3519) (meaning t m 3591) (meaning t m 3923) (meaning t m 4376) (meaning t m 4501) source

theorem rule24146 (p2573 p2928 p3519 p3920 : Prop) (h : (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3920) ∨ (¬ p2928)) : (¬ p2573) ∨ (¬ p2928) ∨ (¬ p3519) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial24146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory13402 (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7)
  exact rule24146 (meaning t m 2573) (meaning t m 2928) (meaning t m 3519) (meaning t m 3920) source

theorem rule24148 (p2027 p2406 p2573 p2589 p3574 p4814 : Prop) (h : (¬ p2573) ∨ (¬ p2406) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4814) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial24148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory13404 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule24148 (meaning t m 2027) (meaning t m 2406) (meaning t m 2573) (meaning t m 2589) (meaning t m 3574) (meaning t m 4814) source

theorem rule24149 (p2531 p4420 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p2531) ∨ p4420) : (¬ p2531) ∨ (p4420) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2531)) ∨ (meaning t m 4420) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13405 t (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule24149 (meaning t m 2531) (meaning t m 4420) (meaning t m 4902) source

theorem rule24152 (p2318 p4712 p5199 : Prop) (h : (¬ p2318) ∨ (¬ p4712) ∨ p5199) : (¬ p2318) ∨ (¬ p4712) ∨ (p5199) := by
  classical
  tauto

theorem initial24152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 4712)) ∨ (meaning t m 5199) := by
  have source := ElevenTheory.theory13408 t (m.theta 0 7) (m.theta 4 7) (m.theta 6 7)
  exact rule24152 (meaning t m 2318) (meaning t m 4712) (meaning t m 5199) source

theorem rule24155 (p2027 p2532 p3115 p3497 p5118 p5568 : Prop) (h : (¬ p3497) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13411 t (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10) (m.theta 8 9)
  exact rule24155 (meaning t m 2027) (meaning t m 2532) (meaning t m 3115) (meaning t m 3497) (meaning t m 5118) (meaning t m 5568) source

theorem rule24156 (p2027 p2911 p4019 p4119 p4647 p4800 p5568 : Prop) (h : (¬ p4119) ∨ (¬ p2911) ∨ (¬ p4800) ∨ (¬ p4019) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p4647)) : (p2027) ∨ (¬ p2911) ∨ (¬ p4019) ∨ (¬ p4119) ∨ (¬ p4647) ∨ (¬ p4800) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13412 t (m.theta 2 8) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule24156 (meaning t m 2027) (meaning t m 2911) (meaning t m 4019) (meaning t m 4119) (meaning t m 4647) (meaning t m 4800) (meaning t m 5568) source

theorem rule24157 (p2027 p2104 p2156 p2459 p2958 p3156 p3952 p4340 p4786 p4902 : Prop) (h : (¬ p3952) ∨ (¬ p3156) ∨ (¬ p4786) ∨ (¬ p4902) ∨ (¬ p2958) ∨ (¬ p2459) ∨ (¬ p2156) ∨ (¬ p2104) ∨ (¬ p4340) ∨ p2027) : (p2027) ∨ (¬ p2104) ∨ (¬ p2156) ∨ (¬ p2459) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4340) ∨ (¬ p4786) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13413 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24157 (meaning t m 2027) (meaning t m 2104) (meaning t m 2156) (meaning t m 2459) (meaning t m 2958) (meaning t m 3156) (meaning t m 3952) (meaning t m 4340) (meaning t m 4786) (meaning t m 4902) source

theorem rule24159 (p2027 p2685 p3486 p4066 p4283 p4315 p4957 : Prop) (h : (¬ p3486) ∨ (¬ p4283) ∨ (¬ p2685) ∨ (¬ p4957) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p4315)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3486) ∨ (¬ p4066) ∨ (¬ p4283) ∨ (¬ p4315) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial24159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory13415 t (m.theta 0 7) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule24159 (meaning t m 2027) (meaning t m 2685) (meaning t m 3486) (meaning t m 4066) (meaning t m 4283) (meaning t m 4315) (meaning t m 4957) source

theorem rule24160 (p2027 p2318 p2685 p3097 p4066 p4195 p4560 : Prop) (h : (¬ p4560) ∨ (¬ p2318) ∨ (¬ p4066) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2685) ∨ (¬ p3097) ∨ (¬ p4066) ∨ (¬ p4195) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial24160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13416 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule24160 (meaning t m 2027) (meaning t m 2318) (meaning t m 2685) (meaning t m 3097) (meaning t m 4066) (meaning t m 4195) (meaning t m 4560) source

theorem rule24161 (p2027 p2139 p2156 p2373 p3365 p3553 p3572 p4110 p4902 : Prop) (h : (¬ p2139) ∨ (¬ p4110) ∨ (¬ p2156) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3553) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4110) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13417 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule24161 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2373) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4110) (meaning t m 4902) source

theorem rule24162 (p2027 p2230 p2563 p2761 p3125 p3292 p4236 p4419 p4621 p5284 : Prop) (h : (¬ p4236) ∨ (¬ p5284) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p4621) ∨ (¬ p4419) ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2761) ∨ (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4621) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial24162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory13418 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24162 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 2761) (meaning t m 3125) (meaning t m 3292) (meaning t m 4236) (meaning t m 4419) (meaning t m 4621) (meaning t m 5284) source

theorem rule24164 (p2027 p2230 p2373 p3146 p3425 p3659 p4419 p5118 p5558 : Prop) (h : (¬ p3425) ∨ (¬ p2373) ∨ (¬ p5118) ∨ (¬ p3146) ∨ (¬ p2230) ∨ (¬ p4419) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4419) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial24164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13420 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24164 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3425) (meaning t m 3659) (meaning t m 4419) (meaning t m 5118) (meaning t m 5558) source

theorem rule24165 (p2027 p3291 p3744 p3755 p4038 p4195 p4560 : Prop) (h : (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p3291) ∨ p2027 ∨ (¬ p4038) ∨ (¬ p4560)) : (p2027) ∨ (¬ p3291) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4038) ∨ (¬ p4195) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial24165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3291)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4038)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13421 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9)
  exact rule24165 (meaning t m 2027) (meaning t m 3291) (meaning t m 3744) (meaning t m 3755) (meaning t m 4038) (meaning t m 4195) (meaning t m 4560) source

theorem rule24166 (p2027 p2383 p2781 p3125 p3365 p3572 p3947 p3989 p4621 : Prop) (h : (¬ p3125) ∨ (¬ p2781) ∨ (¬ p2383) ∨ (¬ p3365) ∨ (¬ p3989) ∨ (¬ p4621) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p3989) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial24166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory13422 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule24166 (meaning t m 2027) (meaning t m 2383) (meaning t m 2781) (meaning t m 3125) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 3989) (meaning t m 4621) source

theorem rule24167 (p2027 p2230 p2427 p2608 p3246 p3519 p3553 p4366 p4376 p4424 p4668 p4777 : Prop) (h : (¬ p4376) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p4424) ∨ (¬ p3246) ∨ (¬ p4668) ∨ (¬ p2608) ∨ (¬ p4366) ∨ (¬ p4777) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4424) ∨ (¬ p4668) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial24167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory13423 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24167 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2608) (meaning t m 3246) (meaning t m 3519) (meaning t m 3553) (meaning t m 4366) (meaning t m 4376) (meaning t m 4424) (meaning t m 4668) (meaning t m 4777) source

theorem rule24168 (p3125 p3654 p4356 : Prop) (h : (¬ p4356) ∨ (¬ p3125) ∨ p3654) : (¬ p3125) ∨ (p3654) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial24168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (meaning t m 3654) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory13424 (m.theta 0 6) (m.theta 5 6) (m.theta 6 9)
  exact rule24168 (meaning t m 3125) (meaning t m 3654) (meaning t m 4356) source

theorem rule24173 (p2027 p2608 p2737 p3555 p4418 p5049 : Prop) (h : (¬ p2737) ∨ (¬ p4418) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2608) ∨ (¬ p5049)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3555) ∨ (¬ p4418) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial24173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory13429 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5)
  exact rule24173 (meaning t m 2027) (meaning t m 2608) (meaning t m 2737) (meaning t m 3555) (meaning t m 4418) (meaning t m 5049) source

theorem rule24174 (p2027 p2657 p3146 p3366 p3449 p3555 p3584 p3683 p4137 p4236 p4377 p4446 p4604 : Prop) (h : (¬ p3366) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p3146) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p4137) ∨ (¬ p3555) ∨ (¬ p4446) ∨ (¬ p4377) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p3449)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial24174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory13430 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24174 (meaning t m 2027) (meaning t m 2657) (meaning t m 3146) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3584) (meaning t m 3683) (meaning t m 4137) (meaning t m 4236) (meaning t m 4377) (meaning t m 4446) (meaning t m 4604) source

theorem rule24175 (p2027 p2307 p2578 p3422 p3874 p4432 p4501 : Prop) (h : p2027 ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p2307) ∨ (¬ p4501) ∨ (¬ p3874) ∨ (¬ p4432)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13431 t (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule24175 (meaning t m 2027) (meaning t m 2307) (meaning t m 2578) (meaning t m 3422) (meaning t m 3874) (meaning t m 4432) (meaning t m 4501) source

theorem rule24176 (p2027 p2139 p2156 p3055 p3125 p3461 p3876 p4831 p5503 : Prop) (h : (¬ p3461) ∨ (¬ p2139) ∨ (¬ p3125) ∨ (¬ p3876) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4831) ∨ (¬ p5503)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial24176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory13432 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24176 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 3055) (meaning t m 3125) (meaning t m 3461) (meaning t m 3876) (meaning t m 4831) (meaning t m 5503) source

theorem rule24177 (p2027 p2139 p2299 p2810 p2881 p3051 p3365 p3742 p4712 : Prop) (h : (¬ p4712) ∨ (¬ p3742) ∨ (¬ p3365) ∨ (¬ p2810) ∨ (¬ p2139) ∨ (¬ p3051) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2299) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial24177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory13433 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24177 (meaning t m 2027) (meaning t m 2139) (meaning t m 2299) (meaning t m 2810) (meaning t m 2881) (meaning t m 3051) (meaning t m 3365) (meaning t m 3742) (meaning t m 4712) source

theorem rule24178 (p2027 p2156 p2187 p2363 p3055 p3366 p3370 p3874 p4286 p4377 p5118 : Prop) (h : (¬ p3874) ∨ (¬ p4286) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p2363) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p3370) ∨ (¬ p2187) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4377) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial24178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory13434 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24178 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3055) (meaning t m 3366) (meaning t m 3370) (meaning t m 3874) (meaning t m 4286) (meaning t m 4377) (meaning t m 5118) source

theorem rule24179 (p2027 p2264 p2274 p3989 p4138 p4361 : Prop) (h : (¬ p4361) ∨ (¬ p4138) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial24179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory13435 t (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule24179 (meaning t m 2027) (meaning t m 2264) (meaning t m 2274) (meaning t m 3989) (meaning t m 4138) (meaning t m 4361) source

theorem rule24181 (p4283 p4647 p5199 : Prop) (h : (¬ p4283) ∨ (¬ p4647) ∨ p5199) : (¬ p4283) ∨ (¬ p4647) ∨ (p5199) := by
  classical
  tauto

theorem initial24181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4647)) ∨ (meaning t m 5199) := by
  have source := ElevenTheory.theory13437 t (m.theta 0 7) (m.theta 4 7) (m.theta 5 7)
  exact rule24181 (meaning t m 4283) (meaning t m 4647) (meaning t m 5199) source

theorem rule24182 (p2027 p2139 p2220 p3146 p3266 p3365 p3572 p4391 p4831 : Prop) (h : (¬ p2220) ∨ (¬ p2139) ∨ (¬ p3365) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial24182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory13438 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24182 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 3146) (meaning t m 3266) (meaning t m 3365) (meaning t m 3572) (meaning t m 4391) (meaning t m 4831) source

theorem rule24183 (p2027 p2139 p2156 p3125 p3365 p3461 p3572 p4391 p4831 : Prop) (h : (¬ p4391) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3125) ∨ (¬ p3572) ∨ (¬ p3461) ∨ (¬ p2139) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial24183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory13439 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24183 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 3125) (meaning t m 3365) (meaning t m 3461) (meaning t m 3572) (meaning t m 4391) (meaning t m 4831) source

theorem rule24185 (p2027 p2534 p2657 p3366 p3449 p3555 p3979 p4236 p4256 p4318 p4377 p5122 : Prop) (h : (¬ p3366) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p3555) ∨ (¬ p3979) ∨ (¬ p4318) ∨ (¬ p3449) ∨ (¬ p4256) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4318) ∨ (¬ p4377) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial24185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory13441 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24185 (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3979) (meaning t m 4236) (meaning t m 4256) (meaning t m 4318) (meaning t m 4377) (meaning t m 5122) source

theorem rule24188 (p2187 p3063 p4516 : Prop) (h : (¬ p2187) ∨ (¬ p4516) ∨ p3063) : (¬ p2187) ∨ (p3063) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial24188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (meaning t m 3063) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory13444 (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule24188 (meaning t m 2187) (meaning t m 3063) (meaning t m 4516) source

theorem rule24192 (p2027 p2510 p2528 p3989 p4347 p4718 : Prop) (h : (¬ p2528) ∨ (¬ p3989) ∨ (¬ p2510) ∨ (¬ p4718) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial24192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory13448 t (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule24192 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 3989) (meaning t m 4347) (meaning t m 4718) source

theorem rule24193 (p2630 p3136 p4700 : Prop) (h : (¬ p3136) ∨ (¬ p4700) ∨ p2630) : (p2630) ∨ (¬ p3136) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial24193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2630) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory13449 (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule24193 (meaning t m 2630) (meaning t m 3136) (meaning t m 4700) source

theorem rule24198 (p2027 p2139 p2220 p3055 p3146 p3266 p3876 p4831 p5503 : Prop) (h : (¬ p3266) ∨ (¬ p3146) ∨ (¬ p4831) ∨ (¬ p2220) ∨ (¬ p5503) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3876) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial24198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory13454 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24198 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 3055) (meaning t m 3146) (meaning t m 3266) (meaning t m 3876) (meaning t m 4831) (meaning t m 5503) source

theorem rule24201 (p2027 p2252 p2741 p2797 p2963 p3073 p3449 p3452 p4035 p4190 p4376 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p4190) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2252) ∨ (¬ p4376) ∨ (¬ p2963) ∨ (¬ p2797) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4035) ∨ (¬ p4190) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial24201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4190)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory13457 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9)
  exact rule24201 (meaning t m 2027) (meaning t m 2252) (meaning t m 2741) (meaning t m 2797) (meaning t m 2963) (meaning t m 3073) (meaning t m 3449) (meaning t m 3452) (meaning t m 4035) (meaning t m 4190) (meaning t m 4376) (meaning t m 4604) source

theorem rule24204 (p2027 p2299 p4009 p4044 p4361 p5558 : Prop) (h : (¬ p4361) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p5558) ∨ (¬ p4009) ∨ (¬ p4044)) : (p2027) ∨ (¬ p2299) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p4361) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial24204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13460 t (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule24204 (meaning t m 2027) (meaning t m 2299) (meaning t m 4009) (meaning t m 4044) (meaning t m 4361) (meaning t m 5558) source

theorem rule24206 (p2027 p2230 p2891 p3246 p3365 p3553 p3572 p4034 p4079 p4668 p4736 : Prop) (h : (¬ p3553) ∨ (¬ p4079) ∨ (¬ p4668) ∨ (¬ p3572) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4034) ∨ (¬ p4736) ∨ (¬ p2891) ∨ (¬ p3365) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4034) ∨ (¬ p4079) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13462 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24206 (meaning t m 2027) (meaning t m 2230) (meaning t m 2891) (meaning t m 3246) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4034) (meaning t m 4079) (meaning t m 4668) (meaning t m 4736) source

theorem rule24208 (p2027 p2210 p2891 p3246 p3365 p3553 p3572 p4668 p4736 : Prop) (h : (¬ p3246) ∨ (¬ p3553) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4736) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13464 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24208 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3246) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4668) (meaning t m 4736) source

theorem rule24210 (p2027 p2166 p2210 p2810 p3146 p3359 p3365 p4697 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2210) ∨ (¬ p4697) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p4697) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13466 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule24210 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2810) (meaning t m 3146) (meaning t m 3359) (meaning t m 3365) (meaning t m 4697) (meaning t m 4736) source

theorem rule24211 (p2027 p2088 p2745 p2951 p3136 p4238 p4261 p4262 : Prop) (h : (¬ p4238) ∨ (¬ p2745) ∨ (¬ p4262) ∨ p2027 ∨ (¬ p2951) ∨ (¬ p2088) ∨ (¬ p3136) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4238) ∨ (¬ p4261) ∨ (¬ p4262) := by
  classical
  tauto

theorem initial24211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) := by
  have source := ElevenTheory.theory13467 t (m.theta 0 5) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 8 9)
  exact rule24211 (meaning t m 2027) (meaning t m 2088) (meaning t m 2745) (meaning t m 2951) (meaning t m 3136) (meaning t m 4238) (meaning t m 4261) (meaning t m 4262) source

theorem rule24215 (p2373 p3645 p4120 p4210 : Prop) (h : (¬ p4120) ∨ (¬ p4210) ∨ (¬ p3645) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p3645) ∨ (¬ p4120) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial24215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory13471 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule24215 (meaning t m 2373) (meaning t m 3645) (meaning t m 4120) (meaning t m 4210) source

theorem rule24222 (p2027 p2187 p2192 p2210 p2685 p3414 p3877 p4236 p4736 p4774 : Prop) (h : (¬ p2187) ∨ (¬ p2685) ∨ (¬ p3877) ∨ (¬ p3414) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4774) ∨ (¬ p2210) ∨ (¬ p4736) ∨ (¬ p4236)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4736) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial24222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory13478 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule24222 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2685) (meaning t m 3414) (meaning t m 3877) (meaning t m 4236) (meaning t m 4736) (meaning t m 4774) source

theorem rule24223 (p3960 p4133 p4617 : Prop) (h : (¬ p4133) ∨ (¬ p3960) ∨ p4617) : (¬ p3960) ∨ (¬ p4133) ∨ (p4617) := by
  classical
  tauto

theorem initial24223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4133)) ∨ (meaning t m 4617) := by
  have source := ElevenTheory.theory13479 t (m.theta 0 8) (m.theta 6 8) (m.theta 7 8)
  exact rule24223 (meaning t m 3960) (meaning t m 4133) (meaning t m 4617) source

theorem rule24228 (p2027 p2088 p2891 p3743 p4114 p4261 p4492 p4558 : Prop) (h : (¬ p4492) ∨ (¬ p3743) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4114) ∨ (¬ p2891) ∨ (¬ p4558) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2891) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13484 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule24228 (meaning t m 2027) (meaning t m 2088) (meaning t m 2891) (meaning t m 3743) (meaning t m 4114) (meaning t m 4261) (meaning t m 4492) (meaning t m 4558) source

theorem rule24230 (p2027 p2241 p2295 p2641 p3055 p3584 p3956 p4501 p4736 : Prop) (h : (¬ p4501) ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3956) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13486 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24230 (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 3055) (meaning t m 3584) (meaning t m 3956) (meaning t m 4501) (meaning t m 4736) source

theorem rule24231 (p2027 p2241 p2284 p2992 p3055 p3684 p3880 p4507 p4736 : Prop) (h : (¬ p3880) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p2284) ∨ (¬ p4507) ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4507) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13487 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule24231 (meaning t m 2027) (meaning t m 2241) (meaning t m 2284) (meaning t m 2992) (meaning t m 3055) (meaning t m 3684) (meaning t m 3880) (meaning t m 4507) (meaning t m 4736) source

theorem rule24233 (p2027 p2387 p2819 p2901 p2957 p4198 p4428 p4558 : Prop) (h : (¬ p4428) ∨ (¬ p4558) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p4198) ∨ (¬ p2957) ∨ (¬ p2901) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p2957) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13489 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule24233 (meaning t m 2027) (meaning t m 2387) (meaning t m 2819) (meaning t m 2901) (meaning t m 2957) (meaning t m 4198) (meaning t m 4428) (meaning t m 4558) source

theorem rule24234 (p2027 p2588 p3333 p3584 p4331 p4624 : Prop) (h : (¬ p4624) ∨ (¬ p3333) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4331) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4331) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial24234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13490 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule24234 (meaning t m 2027) (meaning t m 2588) (meaning t m 3333) (meaning t m 3584) (meaning t m 4331) (meaning t m 4624) source

theorem rule24235 (p2533 p2982 p3156 p3879 : Prop) (h : (¬ p3879) ∨ (¬ p2533) ∨ (¬ p3156) ∨ p2982) : (¬ p2533) ∨ (p2982) ∨ (¬ p3156) ∨ (¬ p3879) := by
  classical
  tauto

theorem initial24235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (meaning t m 2982) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3879)) := by
  have source := ElevenTheory.theory13491 (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule24235 (meaning t m 2533) (meaning t m 2982) (meaning t m 3156) (meaning t m 3879) source

theorem rule24236 (p2533 p3115 p3156 : Prop) (h : (¬ p2533) ∨ (¬ p3156) ∨ p3115) : (¬ p2533) ∨ (p3115) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial24236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (meaning t m 3115) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory13492 (m.theta 3 5) (m.theta 5 8) (m.theta 5 9)
  exact rule24236 (meaning t m 2533) (meaning t m 3115) (meaning t m 3156) source

theorem rule24237 (p2533 p3156 p3879 p4948 : Prop) (h : (¬ p3879) ∨ (¬ p2533) ∨ (¬ p3156) ∨ (¬ p4948)) : (¬ p2533) ∨ (¬ p3156) ∨ (¬ p3879) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial24237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory13493 (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule24237 (meaning t m 2533) (meaning t m 3156) (meaning t m 3879) (meaning t m 4948) source

theorem rule24239 (p2027 p2248 p2946 p3146 p3156 p3591 p3990 p4026 p5118 p5580 : Prop) (h : (¬ p5118) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p5580) ∨ (¬ p2946) ∨ (¬ p4026) ∨ (¬ p2248) ∨ (¬ p3156) ∨ (¬ p3990) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3990) ∨ (¬ p4026) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial24239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13495 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule24239 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3591) (meaning t m 3990) (meaning t m 4026) (meaning t m 5118) (meaning t m 5580) source

theorem rule24242 (p3389 p3471 p3658 p3905 : Prop) (h : (¬ p3905) ∨ (¬ p3471) ∨ (¬ p3658) ∨ p3389) : (p3389) ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial24242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3389) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory13498 (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 4 7)
  exact rule24242 (meaning t m 3389) (meaning t m 3471) (meaning t m 3658) (meaning t m 3905) source

theorem rule24243 (p2027 p2104 p2241 p2459 p2992 p3156 p4340 p4736 p4902 : Prop) (h : (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4736) ∨ (¬ p2104) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4340) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13499 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24243 (meaning t m 2027) (meaning t m 2104) (meaning t m 2241) (meaning t m 2459) (meaning t m 2992) (meaning t m 3156) (meaning t m 4340) (meaning t m 4736) (meaning t m 4902) source

theorem rule24244 (p2027 p2088 p3097 p3955 p4114 p4347 p4489 : Prop) (h : (¬ p4347) ∨ (¬ p2088) ∨ (¬ p4489) ∨ p2027 ∨ (¬ p4114) ∨ (¬ p3097) ∨ (¬ p3955)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3955) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial24244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory13500 t (m.theta 0 6) (m.theta 0 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule24244 (meaning t m 2027) (meaning t m 2088) (meaning t m 3097) (meaning t m 3955) (meaning t m 4114) (meaning t m 4347) (meaning t m 4489) source

theorem rule24249 (p2027 p2210 p3055 p3073 p3644 p3692 p3876 p4496 p4736 p4902 : Prop) (h : (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4736) ∨ (¬ p3055) ∨ (¬ p3692) ∨ (¬ p4496) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p3876) ∨ (¬ p4496) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13505 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24249 (meaning t m 2027) (meaning t m 2210) (meaning t m 3055) (meaning t m 3073) (meaning t m 3644) (meaning t m 3692) (meaning t m 3876) (meaning t m 4496) (meaning t m 4736) (meaning t m 4902) source

theorem rule24250 (p2027 p2187 p2192 p2210 p3201 p3540 p3874 p4384 p5193 : Prop) (h : (¬ p4384) ∨ (¬ p5193) ∨ (¬ p2187) ∨ (¬ p3201) ∨ (¬ p2192) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p2210) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p4384) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13506 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule24250 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 3201) (meaning t m 3540) (meaning t m 3874) (meaning t m 4384) (meaning t m 5193) source

theorem rule24251 (p2027 p2156 p2590 p3737 p4539 p5514 : Prop) (h : (¬ p4539) ∨ (¬ p5514) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3737) ∨ (¬ p2590)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2590) ∨ (¬ p3737) ∨ (¬ p4539) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial24251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory13507 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10)
  exact rule24251 (meaning t m 2027) (meaning t m 2156) (meaning t m 2590) (meaning t m 3737) (meaning t m 4539) (meaning t m 5514) source

theorem rule24252 (p3860 p3954 p4436 : Prop) (h : (¬ p3954) ∨ (¬ p4436) ∨ p3860) : (p3860) ∨ (¬ p3954) ∨ (¬ p4436) := by
  classical
  tauto

theorem initial24252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3860) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4436)) := by
  have source := ElevenTheory.theory13508 (m.theta 0 1) (m.theta 1 2) (m.theta 1 8)
  exact rule24252 (meaning t m 3860) (meaning t m 3954) (meaning t m 4436) source

theorem rule24254 (p2027 p2248 p2373 p2459 p2542 p2651 p3860 p4261 p4902 : Prop) (h : (¬ p2651) ∨ (¬ p4261) ∨ (¬ p2459) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p4902) ∨ (¬ p2542) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13510 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24254 (meaning t m 2027) (meaning t m 2248) (meaning t m 2373) (meaning t m 2459) (meaning t m 2542) (meaning t m 2651) (meaning t m 3860) (meaning t m 4261) (meaning t m 4902) source

end SunPrize.SMT
