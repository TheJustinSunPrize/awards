import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory031
import SunPrize.Certificate.Theory032
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule21057 (p2027 p2255 p2579 p2662 p3286 p3506 p4111 p4137 p4444 p4604 : Prop) (h : (¬ p3506) ∨ (¬ p4137) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p4604) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p4444) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p4111) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10313 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21057 (meaning t m 2027) (meaning t m 2255) (meaning t m 2579) (meaning t m 2662) (meaning t m 3286) (meaning t m 3506) (meaning t m 4111) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) source

theorem rule21058 (p2027 p2255 p3298 p3767 p3848 p5284 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p3848) ∨ (¬ p3298) ∨ (¬ p3767) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2255) ∨ (¬ p3298) ∨ (¬ p3767) ∨ (¬ p3848) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 3298)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10314 t (m.theta 0 3) (m.theta 0 9) (m.theta 1 3) (m.theta 3 9) (m.theta 9 10)
  exact rule21058 (meaning t m 2027) (meaning t m 2255) (meaning t m 3298) (meaning t m 3767) (meaning t m 3848) (meaning t m 5284) source

theorem rule21061 (p2027 p2255 p2946 p3256 p4237 p4261 p4262 : Prop) (h : (¬ p2946) ∨ (¬ p3256) ∨ (¬ p2255) ∨ (¬ p4237) ∨ (¬ p4262) ∨ (¬ p4261) ∨ p2027) : (p2027) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p4237) ∨ (¬ p4261) ∨ (¬ p4262) := by
  classical
  tauto

theorem initial21061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) := by
  have source := ElevenTheory.theory10317 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule21061 (meaning t m 2027) (meaning t m 2255) (meaning t m 2946) (meaning t m 3256) (meaning t m 4237) (meaning t m 4261) (meaning t m 4262) source

theorem rule21068 (p2027 p2187 p2192 p2255 p2662 p2946 p3412 p3540 p3644 p4111 p4133 : Prop) (h : (¬ p2662) ∨ (¬ p2255) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p3412) ∨ (¬ p2946) ∨ (¬ p2192) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p3540) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory10324 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule21068 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2255) (meaning t m 2662) (meaning t m 2946) (meaning t m 3412) (meaning t m 3540) (meaning t m 3644) (meaning t m 4111) (meaning t m 4133) source

theorem rule21072 (p2027 p2156 p2255 p2958 p3662 p3952 : Prop) (h : (¬ p3662) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3952) ∨ (¬ p2156) ∨ (¬ p2958)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial21072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory10328 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule21072 (meaning t m 2027) (meaning t m 2156) (meaning t m 2255) (meaning t m 2958) (meaning t m 3662) (meaning t m 3952) source

theorem rule21073 (p2027 p2331 p3292 p3319 p4319 p5171 p5325 : Prop) (h : p2027 ∨ (¬ p2331) ∨ (¬ p3319) ∨ (¬ p3292) ∨ (¬ p5325) ∨ (¬ p5171) ∨ (¬ p4319)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3292) ∨ (¬ p3319) ∨ (¬ p4319) ∨ (¬ p5171) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial21073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5171)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory10329 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 9) (m.theta 4 9) (m.theta 6 9)
  exact rule21073 (meaning t m 2027) (meaning t m 2331) (meaning t m 3292) (meaning t m 3319) (meaning t m 4319) (meaning t m 5171) (meaning t m 5325) source

theorem rule21074 (p2027 p2255 p2901 p2946 p3368 p3486 : Prop) (h : (¬ p2255) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3368) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3368) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial21074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory10330 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule21074 (meaning t m 2027) (meaning t m 2255) (meaning t m 2901) (meaning t m 2946) (meaning t m 3368) (meaning t m 3486) source

theorem rule21076 (p2027 p2166 p2255 p2662 p2946 p3146 p3412 p3540 p4111 p4278 p4669 : Prop) (h : (¬ p4278) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p3412) ∨ (¬ p2662) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p2255) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3412) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10332 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21076 (meaning t m 2027) (meaning t m 2166) (meaning t m 2255) (meaning t m 2662) (meaning t m 2946) (meaning t m 3146) (meaning t m 3412) (meaning t m 3540) (meaning t m 4111) (meaning t m 4278) (meaning t m 4669) source

theorem rule21079 (p2027 p2619 p2992 p4312 p4360 p5053 : Prop) (h : (¬ p2992) ∨ (¬ p5053) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2619) ∨ (¬ p4312)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial21079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory10335 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule21079 (meaning t m 2027) (meaning t m 2619) (meaning t m 2992) (meaning t m 4312) (meaning t m 4360) (meaning t m 5053) source

theorem rule21081 (p1980 p2027 p2122 p2611 p3166 p3568 p3877 p4117 p4426 : Prop) (h : (¬ p4117) ∨ p2611 ∨ (¬ p4426) ∨ (¬ p3166) ∨ (¬ p3568) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p1980) ∨ (¬ p2122)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2122) ∨ (p2611) ∨ (¬ p3166) ∨ (¬ p3568) ∨ (¬ p3877) ∨ (¬ p4117) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial21081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory10337 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule21081 (meaning t m 1980) (meaning t m 2027) (meaning t m 2122) (meaning t m 2611) (meaning t m 3166) (meaning t m 3568) (meaning t m 3877) (meaning t m 4117) (meaning t m 4426) source

theorem rule21083 (p1987 p2027 p2696 p2766 p3425 p3553 p4348 p4777 : Prop) (h : (¬ p3553) ∨ (¬ p4777) ∨ (¬ p1987) ∨ (¬ p2696) ∨ p2766 ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4348)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p3425) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial21083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory10339 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21083 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2766) (meaning t m 3425) (meaning t m 3553) (meaning t m 4348) (meaning t m 4777) source

theorem rule21084 (p3553 p3659 p4325 : Prop) (h : (¬ p4325) ∨ (¬ p3659) ∨ p3553) : (p3553) ∨ (¬ p3659) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial21084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory10340 (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule21084 (meaning t m 3553) (meaning t m 3659) (meaning t m 4325) source

theorem rule21085 (p2177 p3552 p3659 p4325 : Prop) (h : (¬ p3659) ∨ (¬ p2177) ∨ (¬ p4325) ∨ (¬ p3552)) : (¬ p2177) ∨ (¬ p3552) ∨ (¬ p3659) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial21085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory10341 (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21085 (meaning t m 2177) (meaning t m 3552) (meaning t m 3659) (meaning t m 4325) source

theorem rule21086 (p2027 p2363 p3325 p3644 p4276 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3325) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4276) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p4276) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10342 t (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21086 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3644) (meaning t m 4276) (meaning t m 4348) source

theorem rule21088 (p2027 p2255 p2667 p2891 p2946 p3246 p3412 p3461 p3773 p4154 p4625 p5378 : Prop) (h : p2027 ∨ (¬ p4625) ∨ (¬ p2891) ∨ (¬ p2667) ∨ (¬ p3461) ∨ (¬ p3246) ∨ (¬ p2255) ∨ (¬ p3412) ∨ (¬ p2946) ∨ (¬ p4154) ∨ (¬ p5378) ∨ (¬ p3773)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2667) ∨ (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3412) ∨ (¬ p3461) ∨ (¬ p3773) ∨ (¬ p4154) ∨ (¬ p4625) ∨ (¬ p5378) := by
  classical
  tauto

theorem initial21088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5378)) := by
  have source := ElevenTheory.theory10344 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 9) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21088 (meaning t m 2027) (meaning t m 2255) (meaning t m 2667) (meaning t m 2891) (meaning t m 2946) (meaning t m 3246) (meaning t m 3412) (meaning t m 3461) (meaning t m 3773) (meaning t m 4154) (meaning t m 4625) (meaning t m 5378) source

theorem rule21091 (p2005 p2027 p2177 p2573 p2997 p3540 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p2005) ∨ (¬ p2573) ∨ p2997 ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3540)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2573) ∨ (p2997) ∨ (¬ p3540) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial21091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory10347 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21091 (meaning t m 2005) (meaning t m 2027) (meaning t m 2177) (meaning t m 2573) (meaning t m 2997) (meaning t m 3540) (meaning t m 3644) source

theorem rule21094 (p2098 p4234 p4398 p5344 : Prop) (h : (¬ p2098) ∨ (¬ p4234) ∨ (¬ p4398) ∨ (¬ p5344)) : (¬ p2098) ∨ (¬ p4234) ∨ (¬ p4398) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial21094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 4234)) ∨ (¬ (meaning t m 4398)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory10350 (m.theta 0 2) (m.theta 0 9) (m.theta 2 8) (m.theta 2 9)
  exact rule21094 (meaning t m 2098) (meaning t m 4234) (meaning t m 4398) (meaning t m 5344) source

theorem rule21095 (p1982 p2027 p2323 p2528 p2651 p3189 p4111 p4346 : Prop) (h : (¬ p4346) ∨ p2323 ∨ (¬ p3189) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial21095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory10351 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule21095 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2528) (meaning t m 2651) (meaning t m 3189) (meaning t m 4111) (meaning t m 4346) source

theorem rule21098 (p2027 p3096 p3097 p3564 p3947 p4570 p4623 : Prop) (h : (¬ p3096) ∨ (¬ p4570) ∨ (¬ p3097) ∨ (¬ p3947) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p4623)) : (p2027) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p3564) ∨ (¬ p3947) ∨ (¬ p4570) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial21098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory10354 t (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule21098 (meaning t m 2027) (meaning t m 3096) (meaning t m 3097) (meaning t m 3564) (meaning t m 3947) (meaning t m 4570) (meaning t m 4623) source

theorem rule21099 (p2027 p2313 p2383 p3552 p3553 p4133 : Prop) (h : (¬ p3552) ∨ (¬ p3553) ∨ (¬ p2313) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2383)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3552) ∨ (¬ p3553) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory10355 t (m.theta 0 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21099 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3552) (meaning t m 3553) (meaning t m 4133) source

theorem rule21101 (p2891 p3412 p4244 p5051 : Prop) (h : (¬ p4244) ∨ (¬ p5051) ∨ (¬ p3412) ∨ (¬ p2891)) : (¬ p2891) ∨ (¬ p3412) ∨ (¬ p4244) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial21101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory10357 (m.theta 1 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule21101 (meaning t m 2891) (meaning t m 3412) (meaning t m 4244) (meaning t m 5051) source

theorem rule21102 (p1979 p2027 p2299 p2563 p2633 p3952 p4235 p4275 : Prop) (h : (¬ p2563) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p1979) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p3952) ∨ (¬ p4235)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3952) ∨ (¬ p4235) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial21102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory10358 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21102 (meaning t m 1979) (meaning t m 2027) (meaning t m 2299) (meaning t m 2563) (meaning t m 2633) (meaning t m 3952) (meaning t m 4235) (meaning t m 4275) source

theorem rule21103 (p2027 p2248 p2807 p2996 p3555 p4365 : Prop) (h : (¬ p2807) ∨ (¬ p2248) ∨ (¬ p2996) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4365)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3555) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial21103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory10359 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 7)
  exact rule21103 (meaning t m 2027) (meaning t m 2248) (meaning t m 2807) (meaning t m 2996) (meaning t m 3555) (meaning t m 4365) source

theorem rule21104 (p2027 p2247 p2248 p2807 p2996 : Prop) (h : (¬ p2807) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial21104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory10360 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 7)
  exact rule21104 (meaning t m 2027) (meaning t m 2247) (meaning t m 2248) (meaning t m 2807) (meaning t m 2996) source

theorem rule21105 (p2027 p2166 p2210 p2299 p2579 p2588 p3347 p3954 p4902 p5216 : Prop) (h : (¬ p3954) ∨ (¬ p4902) ∨ (¬ p2166) ∨ (¬ p2299) ∨ (¬ p3347) ∨ (¬ p2210) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial21105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory10361 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21105 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 3347) (meaning t m 3954) (meaning t m 4902) (meaning t m 5216) source

theorem rule21107 (p2027 p2230 p2656 p2797 p3364 p3684 p4975 : Prop) (h : (¬ p2797) ∨ p2027 ∨ (¬ p4975) ∨ (¬ p3364) ∨ (¬ p2656) ∨ (¬ p2230) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2797) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial21107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory10363 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule21107 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2797) (meaning t m 3364) (meaning t m 3684) (meaning t m 4975) source

theorem rule21108 (p1980 p2027 p2598 p2611 p2737 p2797 p3585 : Prop) (h : (¬ p2598) ∨ (¬ p2797) ∨ (¬ p1980) ∨ p2611 ∨ (¬ p3585) ∨ p2027 ∨ (¬ p2737)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial21108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory10364 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule21108 (meaning t m 1980) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 2737) (meaning t m 2797) (meaning t m 3585) source

theorem rule21109 (p2241 p2249 p2254 : Prop) (h : p2249 ∨ (¬ p2254) ∨ (¬ p2241)) : (¬ p2241) ∨ (p2249) ∨ (¬ p2254) := by
  classical
  tauto

theorem initial21109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (meaning t m 2249) ∨ (¬ (meaning t m 2254)) := by
  have source := ElevenTheory.theory10365 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule21109 (meaning t m 2241) (meaning t m 2249) (meaning t m 2254) source

theorem rule21111 (p2027 p3506 p3574 p4425 p5176 p5324 : Prop) (h : (¬ p3574) ∨ (¬ p5176) ∨ (¬ p5324) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3506)) : (p2027) ∨ (¬ p3506) ∨ (¬ p3574) ∨ (¬ p4425) ∨ (¬ p5176) ∨ (¬ p5324) := by
  classical
  tauto

theorem initial21111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5176)) ∨ (¬ (meaning t m 5324)) := by
  have source := ElevenTheory.theory10367 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule21111 (meaning t m 2027) (meaning t m 3506) (meaning t m 3574) (meaning t m 4425) (meaning t m 5176) (meaning t m 5324) source

theorem rule21113 (p1992 p2027 p2553 p2608 p3008 p3549 p3591 : Prop) (h : (¬ p3591) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p1992) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3549)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2608) ∨ (p3008) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial21113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory10369 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule21113 (meaning t m 1992) (meaning t m 2027) (meaning t m 2553) (meaning t m 2608) (meaning t m 3008) (meaning t m 3549) (meaning t m 3591) source

theorem rule21114 (p1993 p2388 p3156 p5063 : Prop) (h : p2388 ∨ (¬ p1993) ∨ p5063 ∨ (¬ p3156)) : (¬ p1993) ∨ (p2388) ∨ (¬ p3156) ∨ (p5063) := by
  classical
  tauto

theorem initial21114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3156)) ∨ (meaning t m 5063) := by
  have source := ElevenTheory.theory10370 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule21114 (meaning t m 1993) (meaning t m 2388) (meaning t m 3156) (meaning t m 5063) source

theorem rule21115 (p2027 p2387 p2608 p3063 p4866 p5015 : Prop) (h : (¬ p2608) ∨ (¬ p3063) ∨ (¬ p2387) ∨ (¬ p4866) ∨ (¬ p5015) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p2608) ∨ (¬ p3063) ∨ (¬ p4866) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial21115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory10371 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 8)
  exact rule21115 (meaning t m 2027) (meaning t m 2387) (meaning t m 2608) (meaning t m 3063) (meaning t m 4866) (meaning t m 5015) source

theorem rule21116 (p2027 p2299 p2313 p2581 p2911 p3920 : Prop) (h : (¬ p2911) ∨ (¬ p2581) ∨ (¬ p2313) ∨ (¬ p3920) ∨ (¬ p2299) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2581) ∨ (¬ p2911) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial21116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory10372 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21116 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2581) (meaning t m 2911) (meaning t m 3920) source

theorem rule21117 (p2027 p2589 p2870 p3582 p4235 p4727 : Prop) (h : (¬ p4727) ∨ (¬ p2589) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p3582) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial21117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory10373 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule21117 (meaning t m 2027) (meaning t m 2589) (meaning t m 2870) (meaning t m 3582) (meaning t m 4235) (meaning t m 4727) source

theorem rule21118 (p1984 p2027 p2542 p2964 p3238 p3359 p3452 : Prop) (h : (¬ p3359) ∨ p2964 ∨ (¬ p3238) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2542) ∨ (¬ p3452)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2542) ∨ (p2964) ∨ (¬ p3238) ∨ (¬ p3359) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial21118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory10374 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule21118 (meaning t m 1984) (meaning t m 2027) (meaning t m 2542) (meaning t m 2964) (meaning t m 3238) (meaning t m 3359) (meaning t m 3452) source

theorem rule21119 (p2027 p2313 p2437 p2581 p3574 p4710 : Prop) (h : (¬ p2581) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4710) ∨ (¬ p3574) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2437) ∨ (¬ p2581) ∨ (¬ p3574) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial21119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory10375 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule21119 (meaning t m 2027) (meaning t m 2313) (meaning t m 2437) (meaning t m 2581) (meaning t m 3574) (meaning t m 4710) source

theorem rule21121 (p1991 p2027 p2542 p2589 p2633 p2655 p3570 p3742 p4001 : Prop) (h : p2633 ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p3570) ∨ (¬ p1991) ∨ (¬ p2542) ∨ (¬ p4001) ∨ (¬ p3742)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2655) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial21121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory10377 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule21121 (meaning t m 1991) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2633) (meaning t m 2655) (meaning t m 3570) (meaning t m 3742) (meaning t m 4001) source

theorem rule21123 (p1977 p2027 p2241 p2287 p2295 p3549 p3591 : Prop) (h : (¬ p3549) ∨ (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3591) ∨ p2287) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial21123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory10379 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule21123 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2287) (meaning t m 2295) (meaning t m 3549) (meaning t m 3591) source

theorem rule21125 (p2027 p2247 p2248 p3166 p4360 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p3166) ∨ (¬ p2248) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial21125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory10381 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 8)
  exact rule21125 (meaning t m 2027) (meaning t m 2247) (meaning t m 2248) (meaning t m 3166) (meaning t m 4360) source

theorem rule21126 (p3461 p4367 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p4367) ∨ (¬ p3461)) : (¬ p3461) ∨ (¬ p4367) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10382 (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule21126 (meaning t m 3461) (meaning t m 4367) (meaning t m 5284) source

theorem rule21127 (p2027 p3399 p3547 p3568 p3591 p4761 : Prop) (h : (¬ p4761) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p4761) := by
  classical
  tauto

theorem initial21127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4761)) := by
  have source := ElevenTheory.theory10383 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7)
  exact rule21127 (meaning t m 2027) (meaning t m 3399) (meaning t m 3547) (meaning t m 3568) (meaning t m 3591) (meaning t m 4761) source

theorem rule21128 (p2241 p3038 p3399 : Prop) (h : (¬ p2241) ∨ (¬ p3038) ∨ p3399) : (¬ p2241) ∨ (¬ p3038) ∨ (p3399) := by
  classical
  tauto

theorem initial21128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3038)) ∨ (meaning t m 3399) := by
  have source := ElevenTheory.theory10384 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7)
  exact rule21128 (meaning t m 2241) (meaning t m 3038) (meaning t m 3399) source

theorem rule21130 (p3005 p4195 p4196 : Prop) (h : (¬ p4195) ∨ (¬ p3005) ∨ (¬ p4196)) : (¬ p3005) ∨ (¬ p4195) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial21130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory10386 (m.theta 2 3) (m.theta 3 6) (m.theta 3 8)
  exact rule21130 (meaning t m 3005) (meaning t m 4195) (meaning t m 4196) source

theorem rule21132 (p2027 p2248 p2331 p3238 p3256 p3452 p3880 p4134 p4341 p4347 : Prop) (h : (¬ p2248) ∨ (¬ p3880) ∨ (¬ p4347) ∨ (¬ p3256) ∨ (¬ p4134) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4341) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3238) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4341) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10388 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21132 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3238) (meaning t m 3256) (meaning t m 3452) (meaning t m 3880) (meaning t m 4134) (meaning t m 4341) (meaning t m 4347) source

theorem rule21134 (p1984 p2027 p2247 p2911 p2914 p3553 p4111 p4112 : Prop) (h : p2914 ∨ (¬ p1984) ∨ (¬ p4111) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4112) ∨ (¬ p3553)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3553) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial21134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory10390 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule21134 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2911) (meaning t m 2914) (meaning t m 3553) (meaning t m 4111) (meaning t m 4112) source

theorem rule21136 (p2027 p2248 p2331 p2363 p2668 p2928 p3452 p4278 p4669 : Prop) (h : (¬ p2363) ∨ (¬ p4278) ∨ (¬ p3452) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p2668) ∨ (¬ p2248) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10392 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21136 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4669) source

theorem rule21137 (p1987 p2027 p2459 p2633 p2696 p3425 p3685 p4118 p4963 : Prop) (h : p2633 ∨ (¬ p1987) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2459) ∨ (¬ p3685) ∨ (¬ p4963) ∨ (¬ p4118)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p4118) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial21137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory10393 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21137 (meaning t m 1987) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2696) (meaning t m 3425) (meaning t m 3685) (meaning t m 4118) (meaning t m 4963) source

theorem rule21138 (p1987 p2027 p2807 p2963 p3128 p3572 p4037 : Prop) (h : p3128 ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2807) ∨ (¬ p1987) ∨ (¬ p3572) ∨ (¬ p4037)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (p3128) ∨ (¬ p3572) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial21138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory10394 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 9)
  exact rule21138 (meaning t m 1987) (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3128) (meaning t m 3572) (meaning t m 4037) source

theorem rule21140 (p1980 p3008 p3574 p4975 : Prop) (h : (¬ p1980) ∨ p4975 ∨ (¬ p3574) ∨ p3008) : (¬ p1980) ∨ (p3008) ∨ (¬ p3574) ∨ (p4975) := by
  classical
  tauto

theorem initial21140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 4975) := by
  have source := ElevenTheory.theory10396 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule21140 (meaning t m 1980) (meaning t m 3008) (meaning t m 3574) (meaning t m 4975) source

theorem rule21146 (p2003 p2114 p2829 p4867 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p2003) ∨ p2114 ∨ (¬ p2829) ∨ p4867) : (¬ p2003) ∨ (p2114) ∨ (¬ p2829) ∨ (p4867) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial21146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 4867) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory10402 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6)
  exact rule21146 (meaning t m 2003) (meaning t m 2114) (meaning t m 2829) (meaning t m 4867) (meaning t m 5016) source

theorem rule21147 (p2027 p2177 p2248 p2295 p2331 p3238 p3452 p3880 p4905 : Prop) (h : (¬ p2177) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p3452) ∨ (¬ p2295) ∨ (¬ p2248) ∨ (¬ p3238) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial21147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory10403 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21147 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 4905) source

theorem rule21148 (p2027 p2248 p2264 p2807 p3193 p3452 p3941 p4425 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p3452) ∨ (¬ p2264) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3193) ∨ (¬ p2248) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10404 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21148 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2807) (meaning t m 3193) (meaning t m 3452) (meaning t m 3941) (meaning t m 4425) (meaning t m 5119) source

theorem rule21149 (p2027 p2248 p2264 p2459 p2807 p3238 p3452 p4948 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p2248) ∨ (¬ p4948) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p3452) ∨ (¬ p2459) ∨ (¬ p3238) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial21149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory10405 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21149 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3238) (meaning t m 3452) (meaning t m 4948) (meaning t m 5059) source

theorem rule21150 (p1998 p2027 p2088 p2622 p2707 p2743 p3577 p4348 p4590 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3577) ∨ (¬ p2088) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p4590) ∨ (¬ p2707)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2088) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) ∨ (¬ p4348) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial21150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory10406 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21150 (meaning t m 1998) (meaning t m 2027) (meaning t m 2088) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3577) (meaning t m 4348) (meaning t m 4590) source

theorem rule21151 (p2027 p2248 p3166 p3256 p3857 p5242 : Prop) (h : p2027 ∨ (¬ p2248) ∨ p5242 ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (p5242) := by
  classical
  tauto

theorem initial21151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (meaning t m 5242) := by
  have source := ElevenTheory.theory10407 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 8) (m.theta 3 8) (m.theta 8 9)
  exact rule21151 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3857) (meaning t m 5242) source

theorem rule21153 (p2027 p2248 p2264 p2459 p2499 p2807 p3452 p4137 p4604 : Prop) (h : (¬ p4137) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p4604) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p2264) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10409 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21153 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2499) (meaning t m 2807) (meaning t m 3452) (meaning t m 4137) (meaning t m 4604) source

theorem rule21154 (p1984 p2027 p2177 p2191 p2192 p2997 p3369 p3646 p4132 : Prop) (h : (¬ p3646) ∨ p2027 ∨ p2997 ∨ (¬ p1984) ∨ (¬ p2192) ∨ (¬ p2191) ∨ (¬ p3369) ∨ (¬ p2177) ∨ (¬ p4132)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (p2997) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4132) := by
  classical
  tauto

theorem initial21154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4132)) := by
  have source := ElevenTheory.theory10410 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21154 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2191) (meaning t m 2192) (meaning t m 2997) (meaning t m 3369) (meaning t m 3646) (meaning t m 4132) source

theorem rule21156 (p1994 p2027 p2341 p2630 p3360 p3553 p3572 : Prop) (h : (¬ p2341) ∨ p3360 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3572) ∨ (¬ p3553)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2630) ∨ (p3360) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial21156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory10412 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule21156 (meaning t m 1994) (meaning t m 2027) (meaning t m 2341) (meaning t m 2630) (meaning t m 3360) (meaning t m 3553) (meaning t m 3572) source

theorem rule21158 (p2027 p2248 p2449 p2499 p2761 p2807 p3452 p5254 p5514 : Prop) (h : (¬ p2807) ∨ (¬ p2449) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2499) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p5514)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial21158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory10414 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21158 (meaning t m 2027) (meaning t m 2248) (meaning t m 2449) (meaning t m 2499) (meaning t m 2761) (meaning t m 2807) (meaning t m 3452) (meaning t m 5254) (meaning t m 5514) source

theorem rule21159 (p2027 p2248 p2331 p2363 p2668 p3238 p3452 p4948 p5059 : Prop) (h : (¬ p4948) ∨ (¬ p2668) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2248) ∨ (¬ p3238)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial21159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory10415 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21159 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3238) (meaning t m 3452) (meaning t m 4948) (meaning t m 5059) source

theorem rule21160 (p2027 p2248 p2331 p2668 p3193 p3452 p3979 p4425 p5119 : Prop) (h : (¬ p5119) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4425) ∨ (¬ p3193) ∨ (¬ p2248) ∨ (¬ p3979) ∨ (¬ p2668) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10416 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21160 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2668) (meaning t m 3193) (meaning t m 3452) (meaning t m 3979) (meaning t m 4425) (meaning t m 5119) source

theorem rule21163 (p1982 p2027 p2248 p2331 p2363 p2668 p3238 p3452 p3880 p3982 p5568 : Prop) (h : (¬ p2331) ∨ (¬ p3238) ∨ p3982 ∨ (¬ p3880) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p2668) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2248)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (p3982) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory10419 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21163 (meaning t m 1982) (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 3982) (meaning t m 5568) source

theorem rule21165 (p1990 p3578 p3989 p4134 : Prop) (h : p3578 ∨ (¬ p3989) ∨ p4134 ∨ (¬ p1990)) : (¬ p1990) ∨ (p3578) ∨ (¬ p3989) ∨ (p4134) := by
  classical
  tauto

theorem initial21165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3989)) ∨ (meaning t m 4134) := by
  have source := ElevenTheory.theory10421 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule21165 (meaning t m 1990) (meaning t m 3578) (meaning t m 3989) (meaning t m 4134) source

theorem rule21166 (p2027 p2387 p2510 p2528 p2581 p4347 : Prop) (h : (¬ p2528) ∨ (¬ p2510) ∨ (¬ p2581) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2581) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10422 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21166 (meaning t m 2027) (meaning t m 2387) (meaning t m 2510) (meaning t m 2528) (meaning t m 2581) (meaning t m 4347) source

theorem rule21167 (p1977 p2027 p2241 p3008 p3564 p3591 p4037 p4319 : Prop) (h : (¬ p3591) ∨ (¬ p4319) ∨ p3008 ∨ (¬ p3564) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p3008) ∨ (¬ p3564) ∨ (¬ p3591) ∨ (¬ p4037) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial21167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory10423 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule21167 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 3008) (meaning t m 3564) (meaning t m 3591) (meaning t m 4037) (meaning t m 4319) source

theorem rule21169 (p2027 p2499 p2581 p3222 p3946 p4331 : Prop) (h : p2027 ∨ (¬ p2581) ∨ (¬ p2499) ∨ (¬ p4331) ∨ (¬ p3946) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2581) ∨ (¬ p3222) ∨ (¬ p3946) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial21169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory10425 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule21169 (meaning t m 2027) (meaning t m 2499) (meaning t m 2581) (meaning t m 3222) (meaning t m 3946) (meaning t m 4331) source

theorem rule21170 (p1984 p2027 p2459 p2633 p3486 p3555 p3692 p4119 : Prop) (h : (¬ p1984) ∨ (¬ p4119) ∨ (¬ p2459) ∨ (¬ p3486) ∨ (¬ p3692) ∨ (¬ p3555) ∨ p2633 ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial21170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory10426 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21170 (meaning t m 1984) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3486) (meaning t m 3555) (meaning t m 3692) (meaning t m 4119) source

theorem rule21171 (p2027 p2387 p2499 p2518 p2581 p4157 : Prop) (h : (¬ p2581) ∨ (¬ p4157) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2499) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2581) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial21171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory10427 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule21171 (meaning t m 2027) (meaning t m 2387) (meaning t m 2499) (meaning t m 2518) (meaning t m 2581) (meaning t m 4157) source

theorem rule21173 (p2027 p2248 p2499 p2946 p3146 p3156 p3452 p4137 p4604 : Prop) (h : (¬ p4137) ∨ (¬ p2248) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p2946) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10429 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule21173 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3452) (meaning t m 4137) (meaning t m 4604) source

theorem rule21176 (p1982 p2027 p2622 p2952 p3136 p3146 p3166 p4311 : Prop) (h : (¬ p3146) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2952) ∨ p2622 ∨ (¬ p4311) ∨ (¬ p3136) ∨ (¬ p3166)) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3166) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial21176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory10432 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule21176 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2952) (meaning t m 3136) (meaning t m 3146) (meaning t m 3166) (meaning t m 4311) source

theorem rule21177 (p1994 p2027 p2588 p2997 p3564 p3744 p3952 p4700 : Prop) (h : (¬ p1994) ∨ (¬ p3952) ∨ (¬ p2588) ∨ (¬ p3564) ∨ p2027 ∨ p2997 ∨ (¬ p4700) ∨ (¬ p3744)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial21177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory10433 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule21177 (meaning t m 1994) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3564) (meaning t m 3744) (meaning t m 3952) (meaning t m 4700) source

theorem rule21179 (p2027 p2459 p3461 p4604 p5117 p5558 : Prop) (h : p2027 ∨ (¬ p2459) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5117) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5117) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial21179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5117)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory10435 t (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule21179 (meaning t m 2027) (meaning t m 2459) (meaning t m 3461) (meaning t m 4604) (meaning t m 5117) (meaning t m 5558) source

theorem rule21189 (p2027 p2248 p2928 p3166 p3256 p3266 p3452 p4831 p5503 : Prop) (h : (¬ p4831) ∨ (¬ p2928) ∨ (¬ p3166) ∨ (¬ p2248) ∨ (¬ p5503) ∨ (¬ p3452) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial21189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory10445 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule21189 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3452) (meaning t m 4831) (meaning t m 5503) source

theorem rule21190 (p2027 p2220 p2248 p2499 p2958 p3115 p3452 p3497 p4137 p4397 : Prop) (h : (¬ p3452) ∨ (¬ p3115) ∨ (¬ p2248) ∨ (¬ p4397) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2499) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2958) ∨ (¬ p3115) ∨ (¬ p3452) ∨ (¬ p3497) ∨ (¬ p4137) ∨ (¬ p4397) := by
  classical
  tauto

theorem initial21190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4397)) := by
  have source := ElevenTheory.theory10446 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9)
  exact rule21190 (meaning t m 2027) (meaning t m 2220) (meaning t m 2248) (meaning t m 2499) (meaning t m 2958) (meaning t m 3115) (meaning t m 3452) (meaning t m 3497) (meaning t m 4137) (meaning t m 4397) source

theorem rule21191 (p2027 p3276 p3692 p3945 p4444 p4636 p4902 : Prop) (h : (¬ p3276) ∨ (¬ p4636) ∨ p2027 ∨ (¬ p3945) ∨ (¬ p4902) ∨ (¬ p3692) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4444) ∨ (¬ p4636) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial21191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory10447 t (m.theta 4 9) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21191 (meaning t m 2027) (meaning t m 3276) (meaning t m 3692) (meaning t m 3945) (meaning t m 4444) (meaning t m 4636) (meaning t m 4902) source

theorem rule21193 (p2027 p2249 p2542 p2589 p2655 p2727 : Prop) (h : (¬ p2655) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p2727)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial21193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory10449 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5)
  exact rule21193 (meaning t m 2027) (meaning t m 2249) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2727) source

theorem rule21199 (p2027 p2307 p2493 p2578 p3568 p4194 p4814 : Prop) (h : (¬ p2493) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3568) ∨ (¬ p4194) ∨ p2027 ∨ (¬ p4814)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3568) ∨ (¬ p4194) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial21199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory10455 t (m.theta 0 6) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule21199 (meaning t m 2027) (meaning t m 2307) (meaning t m 2493) (meaning t m 2578) (meaning t m 3568) (meaning t m 4194) (meaning t m 4814) source

theorem rule21202 (p2027 p2248 p2493 p2509 p2579 p2807 p3005 p3572 p4108 p5009 : Prop) (h : p2027 ∨ (¬ p2579) ∨ (¬ p2493) ∨ (¬ p5009) ∨ (¬ p2509) ∨ (¬ p4108) ∨ (¬ p2248) ∨ (¬ p3572) ∨ (¬ p3005) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p4108) ∨ (¬ p5009) := by
  classical
  tauto

theorem initial21202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 5009)) := by
  have source := ElevenTheory.theory10458 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8)
  exact rule21202 (meaning t m 2027) (meaning t m 2248) (meaning t m 2493) (meaning t m 2509) (meaning t m 2579) (meaning t m 2807) (meaning t m 3005) (meaning t m 3572) (meaning t m 4108) (meaning t m 5009) source

theorem rule21207 (p2027 p2249 p2264 p3027 p3551 p4849 : Prop) (h : (¬ p2249) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p4849) ∨ (¬ p2264) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial21207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory10463 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8)
  exact rule21207 (meaning t m 2027) (meaning t m 2249) (meaning t m 2264) (meaning t m 3027) (meaning t m 3551) (meaning t m 4849) source

theorem rule21208 (p2027 p2249 p2264 p2727 p3551 p3580 p4849 : Prop) (h : (¬ p4849) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p2264) ∨ (¬ p3551) ∨ (¬ p3580)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2264) ∨ (¬ p2727) ∨ (¬ p3551) ∨ (¬ p3580) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial21208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory10464 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule21208 (meaning t m 2027) (meaning t m 2249) (meaning t m 2264) (meaning t m 2727) (meaning t m 3551) (meaning t m 3580) (meaning t m 4849) source

theorem rule21209 (p2027 p2241 p2589 p3073 p3859 p3989 p4110 p4118 p4771 p5193 : Prop) (h : (¬ p4771) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2589) ∨ (¬ p3989) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3859) ∨ (¬ p4118) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3859) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4118) ∨ (¬ p4771) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial21209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory10465 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule21209 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3073) (meaning t m 3859) (meaning t m 3989) (meaning t m 4110) (meaning t m 4118) (meaning t m 4771) (meaning t m 5193) source

theorem rule21215 (p1984 p2169 p2589 p3989 p4110 p4658 p4660 p5193 : Prop) (h : (¬ p3989) ∨ (¬ p1984) ∨ (¬ p5193) ∨ p2169 ∨ (¬ p2589) ∨ (¬ p4110) ∨ p4658 ∨ (¬ p4660)) : (¬ p1984) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (p4658) ∨ (¬ p4660) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial21215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4658) ∨ (¬ (meaning t m 4660)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory10471 t (m.theta 0 1) (m.theta 0 4) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9)
  exact rule21215 (meaning t m 1984) (meaning t m 2169) (meaning t m 2589) (meaning t m 3989) (meaning t m 4110) (meaning t m 4658) (meaning t m 4660) (meaning t m 5193) source

theorem rule21216 (p1986 p2027 p2177 p2997 p3367 p3588 p3659 : Prop) (h : (¬ p3588) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p1986) ∨ p2997 ∨ (¬ p3659) ∨ (¬ p2177)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial21216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory10472 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21216 (meaning t m 1986) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3367) (meaning t m 3588) (meaning t m 3659) source

theorem rule21217 (p1986 p2027 p2881 p2938 p3366 p3367 p3425 p3659 : Prop) (h : (¬ p3659) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p1986) ∨ (¬ p3425) ∨ p2938 ∨ (¬ p2881) ∨ (¬ p3367)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial21217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory10473 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule21217 (meaning t m 1986) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3366) (meaning t m 3367) (meaning t m 3425) (meaning t m 3659) source

theorem rule21224 (p2498 p3319 p4137 : Prop) (h : (¬ p2498) ∨ (¬ p4137) ∨ (¬ p3319)) : (¬ p2498) ∨ (¬ p3319) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial21224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory10480 (m.theta 1 6) (m.theta 4 6) (m.theta 6 9)
  exact rule21224 (meaning t m 2498) (meaning t m 3319) (meaning t m 4137) source

theorem rule21225 (p2498 p4026 p4137 : Prop) (h : (¬ p2498) ∨ (¬ p4137) ∨ p4026) : (¬ p2498) ∨ (p4026) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial21225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (meaning t m 4026) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory10481 (m.theta 1 6) (m.theta 4 6) (m.theta 6 9)
  exact rule21225 (meaning t m 2498) (meaning t m 4026) (meaning t m 4137) source

theorem rule21229 (p2027 p2499 p2992 p3016 p3402 p4704 : Prop) (h : p2027 ∨ (¬ p4704) ∨ (¬ p3016) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p3402) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial21229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory10485 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule21229 (meaning t m 2027) (meaning t m 2499) (meaning t m 2992) (meaning t m 3016) (meaning t m 3402) (meaning t m 4704) source

theorem rule21230 (p2027 p2247 p2341 p3246 p3570 p4037 p4154 p4625 p5207 : Prop) (h : (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2341) ∨ (¬ p5207) ∨ (¬ p4037) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4625) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial21230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory10486 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule21230 (meaning t m 2027) (meaning t m 2247) (meaning t m 2341) (meaning t m 3246) (meaning t m 3570) (meaning t m 4037) (meaning t m 4154) (meaning t m 4625) (meaning t m 5207) source

theorem rule21233 (p1981 p2027 p2156 p2187 p2388 p2901 p3556 : Prop) (h : (¬ p2156) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p2187) ∨ (¬ p1981) ∨ p2388) : (¬ p1981) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (p2388) ∨ (¬ p2901) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial21233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory10489 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule21233 (meaning t m 1981) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2388) (meaning t m 2901) (meaning t m 3556) source

theorem rule21235 (p2027 p2499 p3016 p3189 p3402 p5011 : Prop) (h : (¬ p3402) ∨ (¬ p3189) ∨ (¬ p3016) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p5011)) : (p2027) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3189) ∨ (¬ p3402) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial21235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory10491 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6)
  exact rule21235 (meaning t m 2027) (meaning t m 2499) (meaning t m 3016) (meaning t m 3189) (meaning t m 3402) (meaning t m 5011) source

theorem rule21236 (p2027 p2248 p2509 p2761 p2807 p3434 p3452 p4286 p4777 p5123 : Prop) (h : (¬ p4777) ∨ (¬ p3452) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2807) ∨ (¬ p5123) ∨ (¬ p3434) ∨ (¬ p4286) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p4286) ∨ (¬ p4777) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial21236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory10492 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 7) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21236 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2761) (meaning t m 2807) (meaning t m 3434) (meaning t m 3452) (meaning t m 4286) (meaning t m 4777) (meaning t m 5123) source

theorem rule21238 (p3697 p4114 p4198 : Prop) (h : (¬ p4114) ∨ p4198 ∨ (¬ p3697)) : (¬ p3697) ∨ (¬ p4114) ∨ (p4198) := by
  classical
  tauto

theorem initial21238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 4114)) ∨ (meaning t m 4198) := by
  have source := ElevenTheory.theory10494 (m.theta 0 5) (m.theta 0 6) (m.theta 0 8)
  exact rule21238 (meaning t m 3697) (meaning t m 4114) (meaning t m 4198) source

theorem rule21241 (p2027 p2534 p3707 p4351 p4444 p4690 : Prop) (h : (¬ p3707) ∨ (¬ p4690) ∨ p2027 ∨ (¬ p4351) ∨ (¬ p2534) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3707) ∨ (¬ p4351) ∨ (¬ p4444) ∨ (¬ p4690) := by
  classical
  tauto

theorem initial21241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4690)) := by
  have source := ElevenTheory.theory10497 t (m.theta 1 8) (m.theta 1 9) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule21241 (meaning t m 2027) (meaning t m 2534) (meaning t m 3707) (meaning t m 4351) (meaning t m 4444) (meaning t m 4690) source

theorem rule21243 (p2027 p2249 p2437 p2655 p2727 p3540 : Prop) (h : p2027 ∨ (¬ p2249) ∨ (¬ p2727) ∨ (¬ p3540) ∨ (¬ p2437) ∨ (¬ p2655)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2727) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial21243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory10499 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7)
  exact rule21243 (meaning t m 2027) (meaning t m 2249) (meaning t m 2437) (meaning t m 2655) (meaning t m 2727) (meaning t m 3540) source

theorem rule21244 (p1981 p2027 p2668 p2699 p3093 p3309 p3568 : Prop) (h : p2699 ∨ (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3568) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p3309)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2668) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial21244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory10500 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21244 (meaning t m 1981) (meaning t m 2027) (meaning t m 2668) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) (meaning t m 3568) source

theorem rule21247 (p3984 p4389 : Prop) (h : p3984 ∨ p4389) : (p3984) ∨ (p4389) := by
  classical
  tauto

theorem initial21247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3984) ∨ (meaning t m 4389) := by
  have source := ElevenTheory.theory10503 (m.theta 3 6) (m.theta 4 6)
  exact rule21247 (meaning t m 3984) (meaning t m 4389) source

theorem rule21249 (p1987 p2027 p2437 p2545 p2737 p3363 p3540 p3585 : Prop) (h : (¬ p1987) ∨ (¬ p2737) ∨ (¬ p3585) ∨ p2545 ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3363)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial21249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory10505 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule21249 (meaning t m 1987) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2737) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) source

theorem rule21251 (p2027 p2248 p2651 p2810 p3365 p3873 : Prop) (h : p2027 ∨ (¬ p3873) ∨ (¬ p3365) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial21251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory10507 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4)
  exact rule21251 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 2810) (meaning t m 3365) (meaning t m 3873) source

theorem rule21253 (p1983 p2027 p2553 p3008 p3323 p3461 p3568 p4381 : Prop) (h : p3008 ∨ (¬ p1983) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p3323) ∨ (¬ p4381) ∨ (¬ p2553) ∨ (¬ p3461)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3568) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial21253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory10509 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21253 (meaning t m 1983) (meaning t m 2027) (meaning t m 2553) (meaning t m 3008) (meaning t m 3323) (meaning t m 3461) (meaning t m 3568) (meaning t m 4381) source

theorem rule21254 (p2027 p2254 p2440 p2608 p2657 p2707 p2717 p3880 p4905 : Prop) (h : p2027 ∨ (¬ p2254) ∨ (¬ p2440) ∨ (¬ p2707) ∨ (¬ p2657) ∨ (¬ p3880) ∨ (¬ p4905) ∨ (¬ p2717) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3880) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial21254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory10510 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule21254 (meaning t m 2027) (meaning t m 2254) (meaning t m 2440) (meaning t m 2608) (meaning t m 2657) (meaning t m 2707) (meaning t m 2717) (meaning t m 3880) (meaning t m 4905) source

theorem rule21255 (p2027 p2254 p2608 p2707 p2717 p3146 p3172 p4118 p4905 : Prop) (h : (¬ p3172) ∨ (¬ p3146) ∨ (¬ p2707) ∨ (¬ p4905) ∨ (¬ p2717) ∨ (¬ p2254) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4118)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial21255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory10511 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21255 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3146) (meaning t m 3172) (meaning t m 4118) (meaning t m 4905) source

theorem rule21259 (p1984 p2027 p2352 p3008 p3688 p3954 p4358 : Prop) (h : p3008 ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p4358) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p2352)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2352) ∨ (p3008) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial21259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory10515 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule21259 (meaning t m 1984) (meaning t m 2027) (meaning t m 2352) (meaning t m 3008) (meaning t m 3688) (meaning t m 3954) (meaning t m 4358) source

theorem rule21262 (p1998 p2027 p2248 p2497 p2553 p2901 p2946 p3008 p3146 p3452 p3549 p3747 p4348 : Prop) (h : (¬ p2497) ∨ (¬ p3747) ∨ (¬ p3146) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2901) ∨ (¬ p2946) ∨ p3008 ∨ (¬ p1998) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p3549)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2248) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (p3008) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p3747) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10518 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 1 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21262 (meaning t m 1998) (meaning t m 2027) (meaning t m 2248) (meaning t m 2497) (meaning t m 2553) (meaning t m 2901) (meaning t m 2946) (meaning t m 3008) (meaning t m 3146) (meaning t m 3452) (meaning t m 3549) (meaning t m 3747) (meaning t m 4348) source

theorem rule21264 (p2577 p4108 p5015 : Prop) (h : (¬ p2577) ∨ p5015 ∨ (¬ p4108)) : (¬ p2577) ∨ (¬ p4108) ∨ (p5015) := by
  classical
  tauto

theorem initial21264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 4108)) ∨ (meaning t m 5015) := by
  have source := ElevenTheory.theory10520 (m.theta 0 1) (m.theta 0 4) (m.theta 0 6)
  exact rule21264 (meaning t m 2577) (meaning t m 4108) (meaning t m 5015) source

theorem rule21265 (p2027 p2313 p2553 p2577 p2659 p3016 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2659) ∨ (¬ p3016) ∨ (¬ p2577)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial21265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory10521 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule21265 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2659) (meaning t m 3016) source

theorem rule21266 (p1988 p2027 p2148 p2156 p2274 p2396 p2761 : Prop) (h : p2027 ∨ p2148 ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2156)) : (¬ p1988) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial21266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory10522 t (m.theta 0 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule21266 (meaning t m 1988) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2761) source

theorem rule21267 (p2027 p3319 p3568 p3690 p4319 p4556 p4623 : Prop) (h : (¬ p4319) ∨ (¬ p3690) ∨ (¬ p3568) ∨ (¬ p4556) ∨ (¬ p3319) ∨ (¬ p4623) ∨ p2027) : (p2027) ∨ (¬ p3319) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4319) ∨ (¬ p4556) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial21267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory10523 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule21267 (meaning t m 2027) (meaning t m 3319) (meaning t m 3568) (meaning t m 3690) (meaning t m 4319) (meaning t m 4556) (meaning t m 4623) source

theorem rule21272 (p1976 p2027 p2169 p2630 p2657 p3956 p4195 p4236 p4389 : Prop) (h : (¬ p3956) ∨ (¬ p1976) ∨ p2169 ∨ p2027 ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p2630)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3956) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial21272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory10528 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule21272 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2630) (meaning t m 2657) (meaning t m 3956) (meaning t m 4195) (meaning t m 4236) (meaning t m 4389) source

theorem rule21276 (p1976 p2027 p2459 p2534 p2633 p3055 p3876 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p1976) ∨ (¬ p3876) ∨ (¬ p2459) ∨ p2027 ∨ p2633 ∨ (¬ p2534) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial21276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory10532 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21276 (meaning t m 1976) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 3055) (meaning t m 3876) (meaning t m 4186) source

theorem rule21278 (p2027 p2668 p2870 p3694 p4204 p4506 p4560 : Prop) (h : (¬ p4506) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p2668) ∨ (¬ p4560) ∨ (¬ p2870) ∨ (¬ p4204)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p4204) ∨ (¬ p4506) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial21278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory10534 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule21278 (meaning t m 2027) (meaning t m 2668) (meaning t m 2870) (meaning t m 3694) (meaning t m 4204) (meaning t m 4506) (meaning t m 4560) source

theorem rule21279 (p2027 p2313 p2581 p3868 p3920 p4260 : Prop) (h : (¬ p3920) ∨ (¬ p2313) ∨ (¬ p3868) ∨ (¬ p4260) ∨ (¬ p2581) ∨ p2027) : (p2027) ∨ (¬ p2313) ∨ (¬ p2581) ∨ (¬ p3868) ∨ (¬ p3920) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial21279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory10535 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10)
  exact rule21279 (meaning t m 2027) (meaning t m 2313) (meaning t m 2581) (meaning t m 3868) (meaning t m 3920) (meaning t m 4260) source

theorem rule21280 (p2027 p2210 p2254 p2657 p2881 p2891 p3742 p4278 p4666 : Prop) (h : (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3742) ∨ (¬ p2881) ∨ (¬ p2254) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10536 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21280 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2881) (meaning t m 2891) (meaning t m 3742) (meaning t m 4278) (meaning t m 4666) source

theorem rule21282 (p1983 p3944 p4381 p4831 : Prop) (h : (¬ p4381) ∨ p3944 ∨ (¬ p1983) ∨ p4831) : (¬ p1983) ∨ (p3944) ∨ (¬ p4381) ∨ (p4831) := by
  classical
  tauto

theorem initial21282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 3944) ∨ (¬ (meaning t m 4381)) ∨ (meaning t m 4831) := by
  have source := ElevenTheory.theory10538 t (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21282 (meaning t m 1983) (meaning t m 3944) (meaning t m 4381) (meaning t m 4831) source

theorem rule21285 (p1976 p2027 p2764 p3055 p3684 p4322 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p1976) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p4322) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial21285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory10541 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule21285 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3055) (meaning t m 3684) (meaning t m 4322) (meaning t m 4948) source

theorem rule21293 (p2027 p2284 p2950 p3136 p3646 p4787 : Prop) (h : (¬ p3136) ∨ (¬ p4787) ∨ (¬ p2950) ∨ (¬ p3646) ∨ (¬ p2284) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3646) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial21293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory10549 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule21293 (meaning t m 2027) (meaning t m 2284) (meaning t m 2950) (meaning t m 3136) (meaning t m 3646) (meaning t m 4787) source

theorem rule21296 (p2027 p2254 p2657 p3707 p3742 p3830 p4278 p4444 p4669 : Prop) (h : (¬ p3742) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4278) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3707) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3707) ∨ (¬ p3742) ∨ (¬ p3830) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10552 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21296 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3707) (meaning t m 3742) (meaning t m 3830) (meaning t m 4278) (meaning t m 4444) (meaning t m 4669) source

theorem rule21298 (p1988 p2027 p2542 p2545 p2589 p3355 p3680 p4952 : Prop) (h : (¬ p1988) ∨ p2545 ∨ (¬ p3355) ∨ (¬ p3680) ∨ (¬ p4952) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2542)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p3355) ∨ (¬ p3680) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial21298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory10554 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule21298 (meaning t m 1988) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 3355) (meaning t m 3680) (meaning t m 4952) source

theorem rule21299 (p2027 p2245 p2657 p2727 p3449 p5078 : Prop) (h : (¬ p2245) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2657) ∨ (¬ p5078) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3449) ∨ (¬ p5078) := by
  classical
  tauto

theorem initial21299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 5078)) := by
  have source := ElevenTheory.theory10555 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4)
  exact rule21299 (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 3449) (meaning t m 5078) source

theorem rule21301 (p1976 p2842 p3055 p3819 p5257 : Prop) (h : (¬ p1976) ∨ p2842 ∨ (¬ p3055) ∨ p5257 ∨ (¬ p3819)) : (¬ p1976) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3819) ∨ (p5257) := by
  classical
  tauto

theorem initial21301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3819)) ∨ (meaning t m 5257) := by
  have source := ElevenTheory.theory10557 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 4)
  exact rule21301 (meaning t m 1976) (meaning t m 2842) (meaning t m 3055) (meaning t m 3819) (meaning t m 5257) source

theorem rule21303 (p2027 p2396 p3346 p3389 p4276 p4636 : Prop) (h : (¬ p4636) ∨ (¬ p3389) ∨ (¬ p3346) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4276)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4276) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial21303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory10559 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule21303 (meaning t m 2027) (meaning t m 2396) (meaning t m 3346) (meaning t m 3389) (meaning t m 4276) (meaning t m 4636) source

theorem rule21306 (p1994 p2630 p2842 p4749 : Prop) (h : (¬ p1994) ∨ p4749 ∨ (¬ p2630) ∨ p2842) : (¬ p1994) ∨ (¬ p2630) ∨ (p2842) ∨ (p4749) := by
  classical
  tauto

theorem initial21306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2842) ∨ (meaning t m 4749) := by
  have source := ElevenTheory.theory10562 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule21306 (meaning t m 1994) (meaning t m 2630) (meaning t m 2842) (meaning t m 4749) source

theorem rule21307 (p2000 p3360 p3540 p5203 : Prop) (h : p5203 ∨ (¬ p2000) ∨ p3360 ∨ (¬ p3540)) : (¬ p2000) ∨ (p3360) ∨ (¬ p3540) ∨ (p5203) := by
  classical
  tauto

theorem initial21307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3540)) ∨ (meaning t m 5203) := by
  have source := ElevenTheory.theory10563 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7)
  exact rule21307 (meaning t m 2000) (meaning t m 3360) (meaning t m 3540) (meaning t m 5203) source

theorem rule21308 (p2027 p2449 p2588 p4107 p4156 p4976 : Prop) (h : (¬ p2588) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p4976) ∨ (¬ p2449) ∨ (¬ p4156)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2588) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial21308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory10564 t (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule21308 (meaning t m 2027) (meaning t m 2449) (meaning t m 2588) (meaning t m 4107) (meaning t m 4156) (meaning t m 4976) source

theorem rule21310 (p2027 p2387 p2696 p2787 p3136 p4272 p4347 p4444 p5400 : Prop) (h : (¬ p4444) ∨ (¬ p4347) ∨ (¬ p5400) ∨ p2027 ∨ (¬ p2787) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p2387) ∨ (¬ p4272)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3136) ∨ (¬ p4272) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial21310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory10566 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule21310 (meaning t m 2027) (meaning t m 2387) (meaning t m 2696) (meaning t m 2787) (meaning t m 3136) (meaning t m 4272) (meaning t m 4347) (meaning t m 4444) (meaning t m 5400) source

theorem rule21311 (p2027 p2248 p2946 p3156 p3591 p3969 p4026 p4191 p5119 : Prop) (h : (¬ p3591) ∨ (¬ p2248) ∨ (¬ p4191) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p5119) ∨ (¬ p3156) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3969) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10567 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21311 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3156) (meaning t m 3591) (meaning t m 3969) (meaning t m 4026) (meaning t m 4191) (meaning t m 5119) source

theorem rule21314 (p2027 p2590 p3016 p3878 p4149 p4608 p5600 : Prop) (h : (¬ p3878) ∨ (¬ p5600) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2590) ∨ (¬ p4149) ∨ (¬ p4608)) : (p2027) ∨ (¬ p2590) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p4149) ∨ (¬ p4608) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial21314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4608)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory10570 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 8 10)
  exact rule21314 (meaning t m 2027) (meaning t m 2590) (meaning t m 3016) (meaning t m 3878) (meaning t m 4149) (meaning t m 4608) (meaning t m 5600) source

theorem rule21315 (p1990 p2027 p2563 p2766 p3266 p4033 p4191 p4948 : Prop) (h : (¬ p4033) ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p4191) ∨ (¬ p3266) ∨ p2766 ∨ p2027 ∨ (¬ p4948)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial21315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory10571 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21315 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2766) (meaning t m 3266) (meaning t m 4033) (meaning t m 4191) (meaning t m 4948) source

theorem rule21317 (p1998 p2027 p2230 p2427 p2656 p2688 p2727 p2881 : Prop) (h : (¬ p1998) ∨ p2027 ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p2230) ∨ (¬ p2881) ∨ (¬ p2427)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial21317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory10573 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule21317 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2881) source

theorem rule21322 (p1976 p2027 p2545 p3027 p3365 p3572 p4111 : Prop) (h : (¬ p1976) ∨ (¬ p3365) ∨ p2545 ∨ (¬ p3027) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3572)) : (¬ p1976) ∨ (p2027) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial21322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory10578 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule21322 (meaning t m 1976) (meaning t m 2027) (meaning t m 2545) (meaning t m 3027) (meaning t m 3365) (meaning t m 3572) (meaning t m 4111) source

theorem rule21323 (p1979 p2027 p2881 p2938 p2946 p3414 p3553 : Prop) (h : (¬ p3414) ∨ p2027 ∨ p2938 ∨ (¬ p3553) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial21323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory10579 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule21323 (meaning t m 1979) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 2946) (meaning t m 3414) (meaning t m 3553) source

theorem rule21324 (p2027 p2996 p3189 p3644 p4378 p4653 : Prop) (h : (¬ p4378) ∨ (¬ p4653) ∨ p2027 ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4378) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial21324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory10580 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule21324 (meaning t m 2027) (meaning t m 2996) (meaning t m 3189) (meaning t m 3644) (meaning t m 4378) (meaning t m 4653) source

theorem rule21325 (p1999 p2027 p2331 p2545 p2657 p3276 p4191 p4421 p5175 : Prop) (h : p2027 ∨ (¬ p1999) ∨ p2545 ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p3276) ∨ (¬ p5175)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial21325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory10581 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 9) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule21325 (meaning t m 1999) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 3276) (meaning t m 4191) (meaning t m 4421) (meaning t m 5175) source

theorem rule21328 (p2707 p3367 p5085 : Prop) (h : (¬ p3367) ∨ (¬ p5085) ∨ p2707) : (p2707) ∨ (¬ p3367) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial21328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2707) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory10584 (m.theta 1 2) (m.theta 2 4) (m.theta 2 7)
  exact rule21328 (meaning t m 2707) (meaning t m 3367) (meaning t m 5085) source

theorem rule21333 (p2177 p3527 p4427 : Prop) (h : (¬ p3527) ∨ (¬ p4427) ∨ p2177) : (p2177) ∨ (¬ p3527) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial21333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory10589 (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21333 (meaning t m 2177) (meaning t m 3527) (meaning t m 4427) source

theorem rule21334 (p1978 p2027 p2997 p3097 p3680 p3946 p4191 p4198 p4334 : Prop) (h : p2997 ∨ (¬ p1978) ∨ (¬ p3946) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p4334) ∨ (¬ p4191) ∨ (¬ p3680)) : (¬ p1978) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3680) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4198) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial21334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory10590 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule21334 (meaning t m 1978) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3680) (meaning t m 3946) (meaning t m 4191) (meaning t m 4198) (meaning t m 4334) source

theorem rule21335 (p1982 p2027 p2657 p2688 p2727 p3166 p3256 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p3256) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p2657)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial21335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory10591 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule21335 (meaning t m 1982) (meaning t m 2027) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3166) (meaning t m 3256) source

theorem rule21337 (p2027 p2972 p3486 p3821 p4135 p4155 p4280 : Prop) (h : (¬ p4280) ∨ (¬ p4155) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p4135) ∨ (¬ p3486) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3821) ∨ (¬ p4135) ∨ (¬ p4155) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial21337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory10593 t (m.theta 0 7) (m.theta 1 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule21337 (meaning t m 2027) (meaning t m 2972) (meaning t m 3486) (meaning t m 3821) (meaning t m 4135) (meaning t m 4155) (meaning t m 4280) source

theorem rule21338 (p2027 p2315 p3063 p3549 p3550 p3551 : Prop) (h : (¬ p3063) ∨ p2027 ∨ (¬ p3550) ∨ (¬ p2315) ∨ (¬ p3551) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2315) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial21338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory10594 t (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21338 (meaning t m 2027) (meaning t m 2315) (meaning t m 3063) (meaning t m 3549) (meaning t m 3550) (meaning t m 3551) source

theorem rule21339 (p1994 p2027 p2299 p2311 p2386 p2396 p2633 p3574 p3821 : Prop) (h : (¬ p2386) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p2396) ∨ (¬ p2311) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p1994) ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3574) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial21339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory10595 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21339 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2311) (meaning t m 2386) (meaning t m 2396) (meaning t m 2633) (meaning t m 3574) (meaning t m 3821) source

theorem rule21341 (p2027 p2299 p2311 p2396 p2608 p2619 p2839 p3821 p4902 p5021 : Prop) (h : (¬ p4902) ∨ (¬ p3821) ∨ (¬ p2299) ∨ (¬ p5021) ∨ (¬ p2619) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3821) ∨ (¬ p4902) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial21341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory10597 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21341 (meaning t m 2027) (meaning t m 2299) (meaning t m 2311) (meaning t m 2396) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 3821) (meaning t m 4902) (meaning t m 5021) source

theorem rule21342 (p2027 p2122 p2311 p2396 p2782 p3821 : Prop) (h : (¬ p2311) ∨ (¬ p2122) ∨ (¬ p3821) ∨ (¬ p2396) ∨ (¬ p2782) ∨ p2027) : (p2027) ∨ (¬ p2122) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2782) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial21342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory10598 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule21342 (meaning t m 2027) (meaning t m 2122) (meaning t m 2311) (meaning t m 2396) (meaning t m 2782) (meaning t m 3821) source

theorem rule21343 (p2318 p3959 p4475 : Prop) (h : p2318 ∨ (¬ p4475) ∨ (¬ p3959)) : (p2318) ∨ (¬ p3959) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial21343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2318) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory10599 (m.theta 0 7) (m.theta 2 7) (m.theta 6 7)
  exact rule21343 (meaning t m 2318) (meaning t m 3959) (meaning t m 4475) source

theorem rule21344 (p2027 p2608 p3527 p3551 p4377 p4431 p5206 : Prop) (h : (¬ p2608) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p5206) ∨ (¬ p4431)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4377) ∨ (¬ p4431) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial21344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory10600 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 7 8)
  exact rule21344 (meaning t m 2027) (meaning t m 2608) (meaning t m 3527) (meaning t m 3551) (meaning t m 4377) (meaning t m 4431) (meaning t m 5206) source

theorem rule21345 (p2027 p2191 p2220 p2504 p2665 p3574 p4338 p4399 : Prop) (h : (¬ p2504) ∨ (¬ p2665) ∨ (¬ p4338) ∨ (¬ p3574) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p4399) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2504) ∨ (¬ p2665) ∨ (¬ p3574) ∨ (¬ p4338) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial21345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory10601 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8)
  exact rule21345 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2504) (meaning t m 2665) (meaning t m 3574) (meaning t m 4338) (meaning t m 4399) source

theorem rule21346 (p2027 p2248 p2946 p3156 p3591 p3923 p3969 p4347 p5122 : Prop) (h : (¬ p3969) ∨ (¬ p3923) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3591) ∨ (¬ p4347) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory10602 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21346 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3156) (meaning t m 3591) (meaning t m 3923) (meaning t m 3969) (meaning t m 4347) (meaning t m 5122) source

theorem rule21347 (p1988 p2027 p2114 p2651 p2737 p2811 p3276 p3343 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p3343) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p2811) ∨ (¬ p1988) ∨ (¬ p3276)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3276) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial21347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory10603 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule21347 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3276) (meaning t m 3343) source

theorem rule21348 (p2027 p3556 p3631 p3690 p4431 p4522 : Prop) (h : (¬ p4522) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p4431) ∨ (¬ p3690) ∨ (¬ p3556)) : (p2027) ∨ (¬ p3556) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4431) ∨ (¬ p4522) := by
  classical
  tauto

theorem initial21348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4522)) := by
  have source := ElevenTheory.theory10604 t (m.theta 0 5) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule21348 (meaning t m 2027) (meaning t m 3556) (meaning t m 3631) (meaning t m 3690) (meaning t m 4431) (meaning t m 4522) source

theorem rule21349 (p2027 p2248 p2528 p2651 p3083 p3555 p3744 p4173 p4604 : Prop) (h : (¬ p3744) ∨ (¬ p4604) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p4173) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10605 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule21349 (meaning t m 2027) (meaning t m 2248) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4604) source

theorem rule21353 (p1997 p2027 p2396 p2542 p2997 p3690 p3742 p4001 : Prop) (h : (¬ p2542) ∨ (¬ p3742) ∨ p2997 ∨ (¬ p2396) ∨ (¬ p1997) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p3690)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2542) ∨ (p2997) ∨ (¬ p3690) ∨ (¬ p3742) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial21353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory10609 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21353 (meaning t m 1997) (meaning t m 2027) (meaning t m 2396) (meaning t m 2542) (meaning t m 2997) (meaning t m 3690) (meaning t m 3742) (meaning t m 4001) source

theorem rule21359 (p2027 p2470 p2528 p2665 p3878 p4118 : Prop) (h : (¬ p2665) ∨ (¬ p3878) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2665) ∨ (¬ p3878) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial21359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory10615 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule21359 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2665) (meaning t m 3878) (meaning t m 4118) source

theorem rule21361 (p2027 p2248 p2946 p3115 p3591 p3680 p3923 p5123 p5580 : Prop) (h : (¬ p3591) ∨ (¬ p2248) ∨ (¬ p3923) ∨ (¬ p3680) ∨ (¬ p5580) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3591) ∨ (¬ p3680) ∨ (¬ p3923) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial21361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory10617 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21361 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3115) (meaning t m 3591) (meaning t m 3680) (meaning t m 3923) (meaning t m 5123) (meaning t m 5580) source

theorem rule21362 (p2027 p2156 p2247 p4172 p4173 p4959 : Prop) (h : p2027 ∨ (¬ p2156) ∨ (¬ p4959) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial21362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory10618 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 5 6)
  exact rule21362 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 4172) (meaning t m 4173) (meaning t m 4959) source

theorem rule21363 (p2027 p2406 p2589 p3093 p3541 p4108 p4870 : Prop) (h : (¬ p3093) ∨ (¬ p2406) ∨ (¬ p3541) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial21363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory10619 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5)
  exact rule21363 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 3093) (meaning t m 3541) (meaning t m 4108) (meaning t m 4870) source

theorem rule21366 (p3670 p4191 p5265 : Prop) (h : (¬ p5265) ∨ (¬ p3670) ∨ (¬ p4191)) : (¬ p3670) ∨ (¬ p4191) ∨ (¬ p5265) := by
  classical
  tauto

theorem initial21366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5265)) := by
  have source := ElevenTheory.theory10622 (m.theta 2 9) (m.theta 6 9) (m.theta 9 10)
  exact rule21366 (meaning t m 3670) (meaning t m 4191) (meaning t m 5265) source

theorem rule21367 (p1987 p2027 p2299 p2311 p2396 p2633 p2667 p3821 p4195 : Prop) (h : (¬ p2396) ∨ p2027 ∨ (¬ p2667) ∨ (¬ p3821) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p2311) ∨ (¬ p4195) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2667) ∨ (¬ p3821) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial21367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory10623 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21367 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2311) (meaning t m 2396) (meaning t m 2633) (meaning t m 2667) (meaning t m 3821) (meaning t m 4195) source

theorem rule21368 (p1997 p2027 p2177 p2284 p2957 p2997 p3551 p4110 p4984 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p4984) ∨ (¬ p3551) ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p2284) ∨ p2997 ∨ (¬ p2957)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial21368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory10624 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule21368 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2284) (meaning t m 2957) (meaning t m 2997) (meaning t m 3551) (meaning t m 4110) (meaning t m 4984) source

theorem rule21373 (p2027 p3830 p3860 p4118 p4352 p5079 : Prop) (h : (¬ p5079) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4118)) : (p2027) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4118) ∨ (¬ p4352) ∨ (¬ p5079) := by
  classical
  tauto

theorem initial21373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 5079)) := by
  have source := ElevenTheory.theory10629 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 3 8) (m.theta 8 9)
  exact rule21373 (meaning t m 2027) (meaning t m 3830) (meaning t m 3860) (meaning t m 4118) (meaning t m 4352) (meaning t m 5079) source

theorem rule21376 (p2311 p2787 p5260 : Prop) (h : (¬ p2311) ∨ (¬ p2787) ∨ p5260) : (¬ p2311) ∨ (¬ p2787) ∨ (p5260) := by
  classical
  tauto

theorem initial21376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2787)) ∨ (meaning t m 5260) := by
  have source := ElevenTheory.theory10632 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7)
  exact rule21376 (meaning t m 2311) (meaning t m 2787) (meaning t m 5260) source

theorem rule21377 (p2027 p2315 p2819 p3550 p3551 p3822 : Prop) (h : (¬ p3822) ∨ (¬ p3550) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2315) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2315) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3551) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial21377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory10633 t (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21377 (meaning t m 2027) (meaning t m 2315) (meaning t m 2819) (meaning t m 3550) (meaning t m 3551) (meaning t m 3822) source

theorem rule21379 (p2027 p2315 p3483 p3821 p3822 p4623 : Prop) (h : (¬ p4623) ∨ (¬ p3821) ∨ (¬ p2315) ∨ (¬ p3483) ∨ p2027 ∨ (¬ p3822)) : (p2027) ∨ (¬ p2315) ∨ (¬ p3483) ∨ (¬ p3821) ∨ (¬ p3822) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial21379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory10635 t (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule21379 (meaning t m 2027) (meaning t m 2315) (meaning t m 3483) (meaning t m 3821) (meaning t m 3822) (meaning t m 4623) source

theorem rule21380 (p2027 p2177 p2315 p3548 p3631 p3821 : Prop) (h : (¬ p3631) ∨ p2027 ∨ (¬ p2315) ∨ (¬ p2177) ∨ (¬ p3821) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial21380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory10636 t (m.theta 0 7) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21380 (meaning t m 2027) (meaning t m 2177) (meaning t m 2315) (meaning t m 3548) (meaning t m 3631) (meaning t m 3821) source

theorem rule21381 (p2027 p2341 p2936 p3631 p3644 p3821 : Prop) (h : p2027 ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p2936) ∨ (¬ p3644) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2936) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial21381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory10637 t (m.theta 0 7) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21381 (meaning t m 2027) (meaning t m 2341) (meaning t m 2936) (meaning t m 3631) (meaning t m 3644) (meaning t m 3821) source

theorem rule21383 (p2298 p2313 p3414 p3987 : Prop) (h : (¬ p2298) ∨ (¬ p3414) ∨ (¬ p3987) ∨ p2313) : (¬ p2298) ∨ (p2313) ∨ (¬ p3414) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial21383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (meaning t m 2313) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory10639 (m.theta 0 3) (m.theta 0 6) (m.theta 3 7) (m.theta 6 7)
  exact rule21383 (meaning t m 2298) (meaning t m 2313) (meaning t m 3414) (meaning t m 3987) source

theorem rule21386 (p2013 p3599 p4023 p5329 : Prop) (h : (¬ p2013) ∨ p5329 ∨ p4023 ∨ (¬ p3599)) : (¬ p2013) ∨ (¬ p3599) ∨ (p4023) ∨ (p5329) := by
  classical
  tauto

theorem initial21386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2013)) ∨ (¬ (meaning t m 3599)) ∨ (meaning t m 4023) ∨ (meaning t m 5329) := by
  have source := ElevenTheory.theory10642 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 9)
  exact rule21386 (meaning t m 2013) (meaning t m 3599) (meaning t m 4023) (meaning t m 5329) source

theorem rule21387 (p2027 p2156 p2657 p2958 p3952 p4704 : Prop) (h : (¬ p4704) ∨ (¬ p2958) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial21387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory10643 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule21387 (meaning t m 2027) (meaning t m 2156) (meaning t m 2657) (meaning t m 2958) (meaning t m 3952) (meaning t m 4704) source

theorem rule21388 (p2027 p3156 p3238 p3413 p3880 p4811 : Prop) (h : (¬ p3156) ∨ (¬ p3413) ∨ (¬ p4811) ∨ (¬ p3880) ∨ (¬ p3238) ∨ p2027) : (p2027) ∨ (¬ p3156) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3880) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial21388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory10644 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule21388 (meaning t m 2027) (meaning t m 3156) (meaning t m 3238) (meaning t m 3413) (meaning t m 3880) (meaning t m 4811) source

theorem rule21389 (p2027 p2459 p3083 p3359 p4420 p4440 : Prop) (h : (¬ p4420) ∨ (¬ p4440) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p3359) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3083) ∨ (¬ p3359) ∨ (¬ p4420) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial21389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory10645 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21389 (meaning t m 2027) (meaning t m 2459) (meaning t m 3083) (meaning t m 3359) (meaning t m 4420) (meaning t m 4440) source

theorem rule21392 (p2002 p2344 p2667 p4195 p4845 : Prop) (h : (¬ p2667) ∨ p2344 ∨ (¬ p2002) ∨ (¬ p4195) ∨ p4845) : (¬ p2002) ∨ (p2344) ∨ (¬ p2667) ∨ (¬ p4195) ∨ (p4845) := by
  classical
  tauto

theorem initial21392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 4195)) ∨ (meaning t m 4845) := by
  have source := ElevenTheory.theory10648 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule21392 (meaning t m 2002) (meaning t m 2344) (meaning t m 2667) (meaning t m 4195) (meaning t m 4845) source

theorem rule21393 (p1979 p3136 p3474 p5049 : Prop) (h : p5049 ∨ (¬ p1979) ∨ (¬ p3136) ∨ p3474) : (¬ p1979) ∨ (¬ p3136) ∨ (p3474) ∨ (p5049) := by
  classical
  tauto

theorem initial21393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (¬ (meaning t m 3136)) ∨ (meaning t m 3474) ∨ (meaning t m 5049) := by
  have source := ElevenTheory.theory10649 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule21393 (meaning t m 1979) (meaning t m 3136) (meaning t m 3474) (meaning t m 5049) source

theorem rule21395 (p2027 p2122 p2254 p2608 p2829 p2881 p3414 p3553 p4559 : Prop) (h : p2027 ∨ (¬ p4559) ∨ (¬ p3553) ∨ (¬ p2881) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial21395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory10651 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21395 (meaning t m 2027) (meaning t m 2122) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 2881) (meaning t m 3414) (meaning t m 3553) (meaning t m 4559) source

theorem rule21396 (p1992 p2027 p2743 p3128 p3461 p4195 p5274 p5284 : Prop) (h : p3128 ∨ (¬ p5284) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p5274) ∨ (¬ p1992) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p4195) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10652 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule21396 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 3128) (meaning t m 3461) (meaning t m 4195) (meaning t m 5274) (meaning t m 5284) source

theorem rule21398 (p2027 p2098 p2780 p3324 p4326 p4846 : Prop) (h : (¬ p4846) ∨ (¬ p2780) ∨ (¬ p4326) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3324) ∨ (¬ p4326) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial21398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory10654 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8)
  exact rule21398 (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 3324) (meaning t m 4326) (meaning t m 4846) source

theorem rule21401 (p2470 p3860 p4079 p4370 : Prop) (h : (¬ p3860) ∨ (¬ p4370) ∨ (¬ p4079) ∨ (¬ p2470)) : (¬ p2470) ∨ (¬ p3860) ∨ (¬ p4079) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial21401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory10657 (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 4 8)
  exact rule21401 (meaning t m 2470) (meaning t m 3860) (meaning t m 4079) (meaning t m 4370) source

theorem rule21402 (p1990 p2027 p2563 p2668 p2997 p3568 p3880 p4506 : Prop) (h : (¬ p3568) ∨ (¬ p2668) ∨ p2027 ∨ p2997 ∨ (¬ p3880) ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p4506)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3880) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial21402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory10658 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21402 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3880) (meaning t m 4506) source

theorem rule21404 (p1992 p2027 p2177 p2743 p2997 p3361 p3414 p3553 : Prop) (h : (¬ p2177) ∨ p2997 ∨ (¬ p3361) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p1992) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2743) ∨ (p2997) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial21404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory10660 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21404 (meaning t m 1992) (meaning t m 2027) (meaning t m 2177) (meaning t m 2743) (meaning t m 2997) (meaning t m 3361) (meaning t m 3414) (meaning t m 3553) source

theorem rule21405 (p2027 p2254 p2911 p2922 p2950 p3379 p3568 p3646 p3986 p4107 p4666 : Prop) (h : (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3568) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4666) ∨ (¬ p3986) ∨ (¬ p4107) ∨ (¬ p3379) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p3646) ∨ (¬ p3986) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10661 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21405 (meaning t m 2027) (meaning t m 2254) (meaning t m 2911) (meaning t m 2922) (meaning t m 2950) (meaning t m 3379) (meaning t m 3568) (meaning t m 3646) (meaning t m 3986) (meaning t m 4107) (meaning t m 4666) source

theorem rule21407 (p2017 p2633 p3941 p5560 : Prop) (h : p5560 ∨ p2633 ∨ (¬ p3941) ∨ (¬ p2017)) : (¬ p2017) ∨ (p2633) ∨ (¬ p3941) ∨ (p5560) := by
  classical
  tauto

theorem initial21407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3941)) ∨ (meaning t m 5560) := by
  have source := ElevenTheory.theory10663 t (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule21407 (meaning t m 2017) (meaning t m 2633) (meaning t m 3941) (meaning t m 5560) source

theorem rule21409 (p1979 p2027 p2440 p2657 p2765 p2946 p4110 : Prop) (h : (¬ p2946) ∨ p2765 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p1979) ∨ (¬ p2657) ∨ (¬ p2440)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p2946) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial21409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory10665 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule21409 (meaning t m 1979) (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2765) (meaning t m 2946) (meaning t m 4110) source

theorem rule21410 (p1986 p2027 p2459 p2633 p3367 p3588 p3857 p3959 p3961 : Prop) (h : (¬ p3959) ∨ (¬ p3588) ∨ p2633 ∨ (¬ p2459) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p3367) ∨ (¬ p3961) ∨ (¬ p3857)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3857) ∨ (¬ p3959) ∨ (¬ p3961) := by
  classical
  tauto

theorem initial21410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 3961)) := by
  have source := ElevenTheory.theory10666 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21410 (meaning t m 1986) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3367) (meaning t m 3588) (meaning t m 3857) (meaning t m 3959) (meaning t m 3961) source

theorem rule21412 (p1986 p2027 p2311 p2396 p2785 p2997 p3367 p3688 p3821 : Prop) (h : (¬ p3821) ∨ (¬ p3367) ∨ (¬ p2396) ∨ p2997 ∨ p2027 ∨ (¬ p3688) ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2785) ∨ (p2997) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial21412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory10668 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule21412 (meaning t m 1986) (meaning t m 2027) (meaning t m 2311) (meaning t m 2396) (meaning t m 2785) (meaning t m 2997) (meaning t m 3367) (meaning t m 3688) (meaning t m 3821) source

theorem rule21414 (p2027 p2220 p2588 p3646 p4203 p4405 p4441 : Prop) (h : (¬ p3646) ∨ (¬ p4405) ∨ (¬ p2220) ∨ (¬ p2588) ∨ (¬ p4203) ∨ p2027 ∨ (¬ p4441)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2588) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4405) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial21414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory10670 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21414 (meaning t m 2027) (meaning t m 2220) (meaning t m 2588) (meaning t m 3646) (meaning t m 4203) (meaning t m 4405) (meaning t m 4441) source

theorem rule21415 (p2027 p2137 p2156 p2187 p4244 p4275 p4405 : Prop) (h : (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2137) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p4275) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial21415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory10671 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule21415 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2187) (meaning t m 4244) (meaning t m 4275) (meaning t m 4405) source

theorem rule21417 (p1978 p2850 p3474 p4109 p4881 : Prop) (h : (¬ p1978) ∨ p4881 ∨ (¬ p4109) ∨ (¬ p2850) ∨ p3474) : (¬ p1978) ∨ (¬ p2850) ∨ (p3474) ∨ (¬ p4109) ∨ (p4881) := by
  classical
  tauto

theorem initial21417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 4109)) ∨ (meaning t m 4881) := by
  have source := ElevenTheory.theory10673 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule21417 (meaning t m 1978) (meaning t m 2850) (meaning t m 3474) (meaning t m 4109) (meaning t m 4881) source

theorem rule21418 (p2027 p2440 p3016 p4173 p4203 p4629 : Prop) (h : (¬ p4203) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2440) ∨ (¬ p4629)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial21418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory10674 t (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule21418 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4173) (meaning t m 4203) (meaning t m 4629) source

theorem rule21419 (p1997 p2027 p2098 p2542 p2842 p3055 p3742 p4186 p5373 : Prop) (h : (¬ p5373) ∨ p2842 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p1997) ∨ (¬ p3742) ∨ (¬ p3055) ∨ (¬ p4186) ∨ (¬ p2098)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2542) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3742) ∨ (¬ p4186) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial21419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory10675 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule21419 (meaning t m 1997) (meaning t m 2027) (meaning t m 2098) (meaning t m 2542) (meaning t m 2842) (meaning t m 3055) (meaning t m 3742) (meaning t m 4186) (meaning t m 5373) source

theorem rule21420 (p1989 p2027 p2766 p2860 p3694 p4173 p4347 p4506 : Prop) (h : (¬ p1989) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p2860) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506) ∨ p2766) : (¬ p1989) ∨ (p2027) ∨ (p2766) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial21420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory10676 t (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21420 (meaning t m 1989) (meaning t m 2027) (meaning t m 2766) (meaning t m 2860) (meaning t m 3694) (meaning t m 4173) (meaning t m 4347) (meaning t m 4506) source

theorem rule21422 (p2027 p2470 p3540 p3553 p4327 p4404 : Prop) (h : (¬ p3553) ∨ (¬ p4327) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4404) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3553) ∨ (¬ p4327) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial21422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory10678 t (m.theta 0 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule21422 (meaning t m 2027) (meaning t m 2470) (meaning t m 3540) (meaning t m 3553) (meaning t m 4327) (meaning t m 4404) source

theorem rule21423 (p2027 p3073 p3692 p4034 p4235 p4496 p4904 : Prop) (h : (¬ p4496) ∨ (¬ p4904) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4034) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4034) ∨ (¬ p4235) ∨ (¬ p4496) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial21423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory10679 t (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule21423 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 4034) (meaning t m 4235) (meaning t m 4496) (meaning t m 4904) source

theorem rule21424 (p2027 p2122 p3093 p4366 p4427 p4867 : Prop) (h : (¬ p4427) ∨ (¬ p2122) ∨ (¬ p4867) ∨ (¬ p4366) ∨ (¬ p3093) ∨ p2027) : (p2027) ∨ (¬ p2122) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4867) := by
  classical
  tauto

theorem initial21424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4867)) := by
  have source := ElevenTheory.theory10680 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7)
  exact rule21424 (meaning t m 2027) (meaning t m 2122) (meaning t m 3093) (meaning t m 4366) (meaning t m 4427) (meaning t m 4867) source

theorem rule21426 (p2027 p2299 p2619 p4042 p4244 p4559 : Prop) (h : p2027 ∨ (¬ p2299) ∨ (¬ p4559) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2619) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial21426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory10682 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21426 (meaning t m 2027) (meaning t m 2299) (meaning t m 2619) (meaning t m 4042) (meaning t m 4244) (meaning t m 4559) source

theorem rule21428 (p2027 p2254 p2952 p3073 p3093 p3136 p3877 p4317 p4347 p4774 : Prop) (h : (¬ p3093) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4317) ∨ (¬ p4774) ∨ (¬ p4347) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p2254) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4317) ∨ (¬ p4347) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial21428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory10684 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21428 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3073) (meaning t m 3093) (meaning t m 3136) (meaning t m 3877) (meaning t m 4317) (meaning t m 4347) (meaning t m 4774) source

theorem rule21429 (p1997 p2027 p2287 p2441 p2449 p2685 p4195 p4278 : Prop) (h : p2287 ∨ (¬ p4278) ∨ (¬ p2449) ∨ (¬ p1997) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p2441)) : (¬ p1997) ∨ (p2027) ∨ (p2287) ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p4195) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial21429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory10685 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule21429 (meaning t m 1997) (meaning t m 2027) (meaning t m 2287) (meaning t m 2441) (meaning t m 2449) (meaning t m 2685) (meaning t m 4195) (meaning t m 4278) source

theorem rule21430 (p1991 p2027 p2202 p2563 p2630 p2657 p3745 p4195 : Prop) (h : (¬ p1991) ∨ (¬ p2630) ∨ (¬ p3745) ∨ (¬ p2657) ∨ p2202 ∨ (¬ p4195) ∨ (¬ p2563) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3745) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial21430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory10686 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule21430 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2630) (meaning t m 2657) (meaning t m 3745) (meaning t m 4195) source

theorem rule21431 (p2386 p2779 p4390 : Prop) (h : (¬ p2779) ∨ (¬ p2386) ∨ p4390) : (¬ p2386) ∨ (¬ p2779) ∨ (p4390) := by
  classical
  tauto

theorem initial21431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2779)) ∨ (meaning t m 4390) := by
  have source := ElevenTheory.theory10687 (m.theta 0 6) (m.theta 2 6) (m.theta 4 6)
  exact rule21431 (meaning t m 2386) (meaning t m 2779) (meaning t m 4390) source

theorem rule21432 (p1992 p2027 p2202 p2427 p2608 p3486 p3555 : Prop) (h : (¬ p1992) ∨ (¬ p3555) ∨ (¬ p2608) ∨ (¬ p3486) ∨ p2027 ∨ p2202 ∨ (¬ p2427)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3486) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial21432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory10688 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule21432 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2608) (meaning t m 3486) (meaning t m 3555) source

theorem rule21434 (p1987 p2027 p2545 p2696 p3016 p3055 p3584 : Prop) (h : p2027 ∨ (¬ p1987) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3016) ∨ p2545) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p3016) ∨ (¬ p3055) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial21434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory10690 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule21434 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2696) (meaning t m 3016) (meaning t m 3055) (meaning t m 3584) source

theorem rule21435 (p2027 p2254 p2952 p3063 p3093 p3979 p4208 p4322 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4322) ∨ (¬ p2254) ∨ (¬ p3979) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p4208) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3979) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10691 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21435 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3979) (meaning t m 4208) (meaning t m 4322) (meaning t m 5119) source

theorem rule21436 (p1998 p2027 p2114 p2177 p2295 p2331 p2737 p2811 : Prop) (h : (¬ p2811) ∨ (¬ p1998) ∨ (¬ p2295) ∨ p2027 ∨ p2114 ∨ (¬ p2331) ∨ (¬ p2177) ∨ (¬ p2737)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial21436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory10692 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule21436 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 2737) (meaning t m 2811) source

theorem rule21437 (p2027 p2248 p2295 p2331 p3555 p3791 p4322 p4363 p4826 : Prop) (h : (¬ p4363) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3791) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2248) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3555) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial21437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory10693 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule21437 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3555) (meaning t m 3791) (meaning t m 4322) (meaning t m 4363) (meaning t m 4826) source

theorem rule21438 (p2027 p2191 p2248 p2295 p2331 p2396 p3555 p3692 p3950 : Prop) (h : (¬ p2191) ∨ (¬ p3950) ∨ (¬ p2248) ∨ (¬ p3692) ∨ (¬ p3555) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory10694 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21438 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) source

end SunPrize.SMT
