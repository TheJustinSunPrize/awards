import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory036
import SunPrize.Certificate.Theory037
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule22930 (p1979 p2202 p2440 p4704 : Prop) (h : (¬ p1979) ∨ (¬ p2440) ∨ p2202 ∨ p4704) : (¬ p1979) ∨ (p2202) ∨ (¬ p2440) ∨ (p4704) := by
  classical
  tauto

theorem initial22930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 4704) := by
  have source := ElevenTheory.theory12186 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule22930 (meaning t m 1979) (meaning t m 2202) (meaning t m 2440) (meaning t m 4704) source

theorem rule22932 (p2027 p2264 p2685 p3551 p4787 p4849 : Prop) (h : (¬ p4787) ∨ p2027 ∨ (¬ p4849) ∨ (¬ p2685) ∨ (¬ p3551) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p3551) ∨ (¬ p4787) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial22932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory12188 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule22932 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 3551) (meaning t m 4787) (meaning t m 4849) source

theorem rule22933 (p2027 p2177 p3399 p3542 p3860 p5142 : Prop) (h : (¬ p5142) ∨ (¬ p3860) ∨ (¬ p3542) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p5142) := by
  classical
  tauto

theorem initial22933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5142)) := by
  have source := ElevenTheory.theory12189 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 6 7) (m.theta 7 8)
  exact rule22933 (meaning t m 2027) (meaning t m 2177) (meaning t m 3399) (meaning t m 3542) (meaning t m 3860) (meaning t m 5142) source

theorem rule22934 (p2027 p2657 p2946 p3742 p4241 p4644 : Prop) (h : (¬ p4241) ∨ (¬ p3742) ∨ (¬ p2946) ∨ (¬ p4644) ∨ p2027 ∨ (¬ p2657)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3742) ∨ (¬ p4241) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial22934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12190 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule22934 (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 3742) (meaning t m 4241) (meaning t m 4644) source

theorem rule22935 (p2027 p2210 p2247 p4111 p4282 p4704 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p4282) ∨ (¬ p4704) ∨ (¬ p2210) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4111) ∨ (¬ p4282) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial22935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory12191 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5)
  exact rule22935 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 4111) (meaning t m 4282) (meaning t m 4704) source

theorem rule22937 (p2027 p2210 p2440 p3452 p4210 p4814 : Prop) (h : (¬ p2440) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p4814) ∨ (¬ p4210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial22937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12193 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5)
  exact rule22937 (meaning t m 2027) (meaning t m 2210) (meaning t m 2440) (meaning t m 3452) (meaning t m 4210) (meaning t m 4814) source

theorem rule22938 (p2027 p2177 p2191 p2891 p4132 p4556 : Prop) (h : (¬ p4132) ∨ (¬ p2177) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2191) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12194 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule22938 (meaning t m 2027) (meaning t m 2177) (meaning t m 2191) (meaning t m 2891) (meaning t m 4132) (meaning t m 4556) source

theorem rule22939 (p2027 p2166 p2440 p3880 p3948 p4814 : Prop) (h : (¬ p3880) ∨ p2027 ∨ (¬ p3948) ∨ (¬ p2440) ∨ (¬ p4814) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2440) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial22939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12195 t (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8)
  exact rule22939 (meaning t m 2027) (meaning t m 2166) (meaning t m 2440) (meaning t m 3880) (meaning t m 3948) (meaning t m 4814) source

theorem rule22940 (p1998 p2027 p2230 p2233 p2437 p2440 p2881 p3569 : Prop) (h : p2027 ∨ (¬ p2437) ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2233 ∨ (¬ p3569) ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2881) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial22940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory12196 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule22940 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2437) (meaning t m 2440) (meaning t m 2881) (meaning t m 3569) source

theorem rule22941 (p2027 p2665 p3516 p3742 p4278 p5201 : Prop) (h : (¬ p3742) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p5201)) : (p2027) ∨ (¬ p2665) ∨ (¬ p3516) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial22941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory12197 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule22941 (meaning t m 2027) (meaning t m 2665) (meaning t m 3516) (meaning t m 3742) (meaning t m 4278) (meaning t m 5201) source

theorem rule22943 (p2027 p2509 p2839 p3475 p3641 p4257 p5052 : Prop) (h : (¬ p3641) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p2509) ∨ (¬ p4257) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2839) ∨ (¬ p3475) ∨ (¬ p3641) ∨ (¬ p4257) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial22943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12199 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8)
  exact rule22943 (meaning t m 2027) (meaning t m 2509) (meaning t m 2839) (meaning t m 3475) (meaning t m 3641) (meaning t m 4257) (meaning t m 5052) source

theorem rule22945 (p2027 p2241 p2579 p3506 p3842 p3956 p5123 p5193 p5580 : Prop) (h : p2027 ∨ (¬ p3956) ∨ (¬ p3506) ∨ (¬ p5193) ∨ (¬ p5580) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p5123) ∨ (¬ p3842)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p3956) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12201 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule22945 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 3506) (meaning t m 3842) (meaning t m 3956) (meaning t m 5123) (meaning t m 5193) (meaning t m 5580) source

theorem rule22947 (p2027 p2241 p2579 p3189 p4009 p4137 p4191 p5119 p5193 : Prop) (h : (¬ p4009) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p2579) ∨ (¬ p3189) ∨ (¬ p4191) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3189) ∨ (¬ p4009) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12203 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule22947 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 3189) (meaning t m 4009) (meaning t m 4137) (meaning t m 4191) (meaning t m 5119) (meaning t m 5193) source

theorem rule22948 (p2027 p2396 p2579 p2608 p2685 p2737 p3581 p4278 p4570 p5193 : Prop) (h : (¬ p2685) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p2396) ∨ (¬ p4278) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3581) ∨ (¬ p4570)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3581) ∨ (¬ p4278) ∨ (¬ p4570) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12204 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22948 (meaning t m 2027) (meaning t m 2396) (meaning t m 2579) (meaning t m 2608) (meaning t m 2685) (meaning t m 2737) (meaning t m 3581) (meaning t m 4278) (meaning t m 4570) (meaning t m 5193) source

theorem rule22950 (p2027 p2396 p2901 p4208 p4382 p4556 : Prop) (h : (¬ p2901) ∨ (¬ p4382) ∨ (¬ p2396) ∨ (¬ p4208) ∨ (¬ p4556) ∨ p2027) : (p2027) ∨ (¬ p2396) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4382) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12206 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22950 (meaning t m 2027) (meaning t m 2396) (meaning t m 2901) (meaning t m 4208) (meaning t m 4382) (meaning t m 4556) source

theorem rule22951 (p1994 p2027 p2166 p2210 p2396 p2699 p2901 p3497 p3742 p4278 p4556 : Prop) (h : (¬ p3742) ∨ (¬ p4278) ∨ p2699 ∨ (¬ p2210) ∨ (¬ p1994) ∨ (¬ p2901) ∨ (¬ p4556) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3497)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2396) ∨ (p2699) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12207 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9)
  exact rule22951 (meaning t m 1994) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2396) (meaning t m 2699) (meaning t m 2901) (meaning t m 3497) (meaning t m 3742) (meaning t m 4278) (meaning t m 4556) source

theorem rule22952 (p2027 p2191 p2891 p3246 p4132 p4668 : Prop) (h : (¬ p2191) ∨ (¬ p4132) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4132) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12208 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22952 (meaning t m 2027) (meaning t m 2191) (meaning t m 2891) (meaning t m 3246) (meaning t m 4132) (meaning t m 4668) source

theorem rule22953 (p2027 p2166 p2499 p3880 p3948 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p2499) ∨ (¬ p2166) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p3948)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2499) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12209 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule22953 (meaning t m 2027) (meaning t m 2166) (meaning t m 2499) (meaning t m 3880) (meaning t m 3948) (meaning t m 4715) source

theorem rule22954 (p2010 p2027 p2341 p2657 p2688 p2727 p3644 p4104 : Prop) (h : (¬ p3644) ∨ (¬ p2010) ∨ (¬ p2657) ∨ (¬ p4104) ∨ (¬ p2727) ∨ (¬ p2341) ∨ p2027 ∨ p2688) : (¬ p2010) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3644) ∨ (¬ p4104) := by
  classical
  tauto

theorem initial22954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4104)) := by
  have source := ElevenTheory.theory12210 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule22954 (meaning t m 2010) (meaning t m 2027) (meaning t m 2341) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3644) (meaning t m 4104) source

theorem rule22955 (p2027 p2299 p2396 p2881 p4277 p4278 : Prop) (h : (¬ p4277) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2881) ∨ (¬ p2396) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial22955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory12211 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22955 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2881) (meaning t m 4277) (meaning t m 4278) source

theorem rule22956 (p3581 p3746 p4635 : Prop) (h : (¬ p4635) ∨ (¬ p3581) ∨ p3746) : (¬ p3581) ∨ (p3746) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial22956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3581)) ∨ (meaning t m 3746) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory12212 (m.theta 4 6) (m.theta 4 7) (m.theta 4 9)
  exact rule22956 (meaning t m 3581) (meaning t m 3746) (meaning t m 4635) source

theorem rule22958 (p2951 p3370 p4282 : Prop) (h : (¬ p2951) ∨ (¬ p4282) ∨ p3370) : (¬ p2951) ∨ (p3370) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial22958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (meaning t m 3370) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory12214 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5)
  exact rule22958 (meaning t m 2951) (meaning t m 3370) (meaning t m 4282) source

theorem rule22959 (p2156 p2192 p2951 p4282 : Prop) (h : (¬ p2156) ∨ (¬ p4282) ∨ (¬ p2951) ∨ p2192) : (¬ p2156) ∨ (p2192) ∨ (¬ p2951) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial22959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 2192) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory12215 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule22959 (meaning t m 2156) (meaning t m 2192) (meaning t m 2951) (meaning t m 4282) source

theorem rule22960 (p2027 p3880 p3998 p4238 p4539 p5568 : Prop) (h : (¬ p5568) ∨ p2027 ∨ (¬ p4238) ∨ (¬ p3880) ∨ (¬ p4539) ∨ (¬ p3998)) : (p2027) ∨ (¬ p3880) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p4539) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial22960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory12216 t (m.theta 0 5) (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule22960 (meaning t m 2027) (meaning t m 3880) (meaning t m 3998) (meaning t m 4238) (meaning t m 4539) (meaning t m 5568) source

theorem rule22961 (p2027 p2264 p3551 p3580 p3876 p4279 p4750 : Prop) (h : (¬ p4750) ∨ p2027 ∨ (¬ p3580) ∨ (¬ p3551) ∨ (¬ p3876) ∨ (¬ p4279) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3551) ∨ (¬ p3580) ∨ (¬ p3876) ∨ (¬ p4279) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12217 t (m.theta 0 7) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule22961 (meaning t m 2027) (meaning t m 2264) (meaning t m 3551) (meaning t m 3580) (meaning t m 3876) (meaning t m 4279) (meaning t m 4750) source

theorem rule22962 (p2027 p2743 p2839 p2952 p4787 p5051 : Prop) (h : p2027 ∨ (¬ p2952) ∨ (¬ p4787) ∨ (¬ p5051) ∨ (¬ p2743) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2952) ∨ (¬ p4787) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial22962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory12218 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule22962 (meaning t m 2027) (meaning t m 2743) (meaning t m 2839) (meaning t m 2952) (meaning t m 4787) (meaning t m 5051) source

theorem rule22963 (p2027 p2992 p3684 p4111 p4241 p4750 : Prop) (h : p2027 ∨ (¬ p3684) ∨ (¬ p4750) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241)) : (p2027) ∨ (¬ p2992) ∨ (¬ p3684) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12219 t (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule22963 (meaning t m 2027) (meaning t m 2992) (meaning t m 3684) (meaning t m 4111) (meaning t m 4241) (meaning t m 4750) source

theorem rule22964 (p2027 p2417 p2598 p3201 p3486 p3555 p3570 p4668 p4733 : Prop) (h : (¬ p3570) ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p3555) ∨ (¬ p2417) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12220 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22964 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4668) (meaning t m 4733) source

theorem rule22965 (p2027 p2138 p2417 p3367 p3389 p3486 p3570 p3759 p4243 p4668 p4734 : Prop) (h : (¬ p3759) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p4668) ∨ (¬ p3389) ∨ (¬ p2138) ∨ (¬ p3570) ∨ (¬ p4243) ∨ (¬ p3486) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4243) ∨ (¬ p4668) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12221 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22965 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 3367) (meaning t m 3389) (meaning t m 3486) (meaning t m 3570) (meaning t m 3759) (meaning t m 4243) (meaning t m 4668) (meaning t m 4734) source

theorem rule22966 (p2027 p2528 p2598 p3555 p3641 p3744 p4173 p4604 p4733 : Prop) (h : (¬ p4733) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3641) ∨ (¬ p3555) ∨ (¬ p2528) ∨ (¬ p4604) ∨ (¬ p2598) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12222 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22966 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 3555) (meaning t m 3641) (meaning t m 3744) (meaning t m 4173) (meaning t m 4604) (meaning t m 4733) source

theorem rule22967 (p2027 p2298 p2641 p2996 p3323 p4624 : Prop) (h : (¬ p2996) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p2298) ∨ (¬ p4624) ∨ p2027) : (p2027) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3323) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory12223 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22967 (meaning t m 2027) (meaning t m 2298) (meaning t m 2641) (meaning t m 2996) (meaning t m 3323) (meaning t m 4624) source

theorem rule22968 (p2027 p2934 p3527 p3551 p3876 p4279 p5217 : Prop) (h : (¬ p5217) ∨ (¬ p3876) ∨ (¬ p3551) ∨ (¬ p4279) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p2934)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3876) ∨ (¬ p4279) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial22968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory12224 t (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule22968 (meaning t m 2027) (meaning t m 2934) (meaning t m 3527) (meaning t m 3551) (meaning t m 3876) (meaning t m 4279) (meaning t m 5217) source

theorem rule22969 (p2027 p3027 p3876 p4066 p4111 p4279 p4750 : Prop) (h : (¬ p4066) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p3876) ∨ (¬ p4279) ∨ (¬ p4111) ∨ (¬ p3027)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3876) ∨ (¬ p4066) ∨ (¬ p4111) ∨ (¬ p4279) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12225 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule22969 (meaning t m 2027) (meaning t m 3027) (meaning t m 3876) (meaning t m 4066) (meaning t m 4111) (meaning t m 4279) (meaning t m 4750) source

theorem rule22970 (p2027 p2191 p2417 p2598 p3201 p3555 p3692 p3950 p4733 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p2191) ∨ (¬ p3555) ∨ (¬ p2417) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12226 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22970 (meaning t m 2027) (meaning t m 2191) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) (meaning t m 4733) source

theorem rule22974 (p2027 p2352 p2598 p3097 p3422 p3555 p4173 p4405 p4733 : Prop) (h : (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p4405) ∨ (¬ p4173) ∨ (¬ p4733) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3097) ∨ (¬ p3422) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12230 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22974 (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 3097) (meaning t m 3422) (meaning t m 3555) (meaning t m 4173) (meaning t m 4405) (meaning t m 4733) source

theorem rule22975 (p3555 p3591 p4512 : Prop) (h : (¬ p4512) ∨ (¬ p3555) ∨ p3591) : (¬ p3555) ∨ (p3591) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial22975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3555)) ∨ (meaning t m 3591) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory12231 (m.theta 0 1) (m.theta 1 5) (m.theta 1 6)
  exact rule22975 (meaning t m 3555) (meaning t m 3591) (meaning t m 4512) source

theorem rule22978 (p2027 p2992 p3156 p3745 p4154 p4509 : Prop) (h : (¬ p2992) ∨ (¬ p4154) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3745) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12234 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule22978 (meaning t m 2027) (meaning t m 2992) (meaning t m 3156) (meaning t m 3745) (meaning t m 4154) (meaning t m 4509) source

theorem rule22979 (p4153 p4195 p4315 : Prop) (h : (¬ p4153) ∨ (¬ p4315) ∨ p4195) : (¬ p4153) ∨ (p4195) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial22979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4153)) ∨ (meaning t m 4195) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory12235 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule22979 (meaning t m 4153) (meaning t m 4195) (meaning t m 4315) source

theorem rule22982 (p2027 p2138 p3309 p3822 p4193 p4734 p4869 : Prop) (h : p2027 ∨ (¬ p3822) ∨ (¬ p3309) ∨ (¬ p4869) ∨ (¬ p2138) ∨ (¬ p4734) ∨ (¬ p4193)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4734) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial22982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory12238 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule22982 (meaning t m 2027) (meaning t m 2138) (meaning t m 3309) (meaning t m 3822) (meaning t m 4193) (meaning t m 4734) (meaning t m 4869) source

theorem rule22983 (p2027 p2138 p2352 p2573 p3097 p3367 p3758 p3759 p4405 p4734 : Prop) (h : (¬ p3759) ∨ (¬ p4405) ∨ (¬ p3758) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p4734) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3758) ∨ (¬ p3759) ∨ (¬ p4405) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12239 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22983 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2573) (meaning t m 3097) (meaning t m 3367) (meaning t m 3758) (meaning t m 3759) (meaning t m 4405) (meaning t m 4734) source

theorem rule22989 (p3324 p3745 p3989 : Prop) (h : (¬ p3745) ∨ (¬ p3989) ∨ p3324) : (p3324) ∨ (¬ p3745) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial22989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory12245 (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule22989 (meaning t m 3324) (meaning t m 3745) (meaning t m 3989) source

theorem rule22991 (p2027 p2191 p2192 p2598 p2911 p3201 p3369 p3646 p4733 p4905 : Prop) (h : (¬ p4733) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2911) ∨ (¬ p4905) ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p3646) ∨ (¬ p3369)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial22991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory12247 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule22991 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3369) (meaning t m 3646) (meaning t m 4733) (meaning t m 4905) source

theorem rule22993 (p2727 p3027 p3580 : Prop) (h : (¬ p3580) ∨ (¬ p2727) ∨ p3027) : (¬ p2727) ∨ (p3027) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial22993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (meaning t m 3027) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory12249 (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule22993 (meaning t m 2727) (meaning t m 3027) (meaning t m 3580) source

theorem rule22994 (p2027 p3156 p3413 p3684 p4031 p4120 p4750 : Prop) (h : (¬ p3156) ∨ (¬ p3413) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4120)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12250 t (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule22994 (meaning t m 2027) (meaning t m 3156) (meaning t m 3413) (meaning t m 3684) (meaning t m 4031) (meaning t m 4120) (meaning t m 4750) source

theorem rule22995 (p2027 p3256 p3692 p3952 p4237 p4509 : Prop) (h : (¬ p3692) ∨ (¬ p4237) ∨ p2027 ∨ (¬ p4509) ∨ (¬ p3952) ∨ (¬ p3256)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12251 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule22995 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 3952) (meaning t m 4237) (meaning t m 4509) source

theorem rule22996 (p2829 p3367 p4375 : Prop) (h : (¬ p3367) ∨ (¬ p4375) ∨ p2829) : (p2829) ∨ (¬ p3367) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial22996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2829) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory12252 (m.theta 1 2) (m.theta 2 4) (m.theta 2 6)
  exact rule22996 (meaning t m 2829) (meaning t m 3367) (meaning t m 4375) source

theorem rule22997 (p2027 p3527 p3570 p4320 p4431 p4960 : Prop) (h : (¬ p4960) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p3527) ∨ (¬ p4431) ∨ p2027) : (p2027) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4431) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial22997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory12253 t (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule22997 (meaning t m 2027) (meaning t m 3527) (meaning t m 3570) (meaning t m 4320) (meaning t m 4431) (meaning t m 4960) source

theorem rule22998 (p2027 p2657 p2797 p2807 p3572 p4975 : Prop) (h : (¬ p2807) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p3572) ∨ (¬ p2797) ∨ (¬ p4975)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial22998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12254 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule22998 (meaning t m 2027) (meaning t m 2657) (meaning t m 2797) (meaning t m 2807) (meaning t m 3572) (meaning t m 4975) source

theorem rule22999 (p2027 p3146 p3266 p4349 p5063 p5284 : Prop) (h : (¬ p5063) ∨ (¬ p3266) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4349) ∨ (¬ p5284)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4349) ∨ (¬ p5063) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial22999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 5063)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory12255 t (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule22999 (meaning t m 2027) (meaning t m 3146) (meaning t m 3266) (meaning t m 4349) (meaning t m 5063) (meaning t m 5284) source

theorem rule23005 (p2027 p2499 p2657 p2946 p3487 p4241 p4715 : Prop) (h : (¬ p2946) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p2499) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3487) ∨ (¬ p4241) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12261 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule23005 (meaning t m 2027) (meaning t m 2499) (meaning t m 2657) (meaning t m 2946) (meaning t m 3487) (meaning t m 4241) (meaning t m 4715) source

theorem rule23006 (p2027 p3609 p3692 p3988 p4244 p4555 p4744 : Prop) (h : (¬ p3988) ∨ (¬ p3609) ∨ (¬ p4555) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4744)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4244) ∨ (¬ p4555) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial23006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory12262 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule23006 (meaning t m 2027) (meaning t m 3609) (meaning t m 3692) (meaning t m 3988) (meaning t m 4244) (meaning t m 4555) (meaning t m 4744) source

theorem rule23007 (p4191 p4381 p4623 : Prop) (h : (¬ p4623) ∨ (¬ p4191) ∨ p4381) : (¬ p4191) ∨ (p4381) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial23007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4191)) ∨ (meaning t m 4381) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory12263 (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23007 (meaning t m 4191) (meaning t m 4381) (meaning t m 4623) source

theorem rule23008 (p2027 p2299 p2396 p4118 p4443 p4550 : Prop) (h : p2027 ∨ (¬ p4443) ∨ (¬ p2396) ∨ (¬ p2299) ∨ (¬ p4550) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p4118) ∨ (¬ p4443) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial23008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory12264 t (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23008 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 4118) (meaning t m 4443) (meaning t m 4550) source

theorem rule23009 (p2027 p2331 p2952 p3497 p3986 p4507 : Prop) (h : (¬ p3986) ∨ (¬ p2331) ∨ (¬ p4507) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3986) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12265 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule23009 (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3497) (meaning t m 3986) (meaning t m 4507) source

theorem rule23010 (p2027 p2493 p3574 p3662 p4281 p4701 : Prop) (h : (¬ p3574) ∨ (¬ p3662) ∨ (¬ p4701) ∨ (¬ p4281) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3574) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12266 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule23010 (meaning t m 2027) (meaning t m 2493) (meaning t m 3574) (meaning t m 3662) (meaning t m 4281) (meaning t m 4701) source

theorem rule23011 (p2027 p2241 p2579 p3189 p3956 p4009 p4347 p5122 p5193 : Prop) (h : (¬ p5122) ∨ (¬ p4009) ∨ (¬ p2241) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p5193) ∨ (¬ p3956) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3189) ∨ (¬ p3956) ∨ (¬ p4009) ∨ (¬ p4347) ∨ (¬ p5122) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12267 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23011 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 3189) (meaning t m 3956) (meaning t m 4009) (meaning t m 4347) (meaning t m 5122) (meaning t m 5193) source

theorem rule23012 (p2027 p3422 p3646 p3684 p4203 p4533 : Prop) (h : (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4533) ∨ (¬ p4203) ∨ (¬ p3646) ∨ p2027) : (p2027) ∨ (¬ p3422) ∨ (¬ p3646) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial23012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory12268 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule23012 (meaning t m 2027) (meaning t m 3422) (meaning t m 3646) (meaning t m 3684) (meaning t m 4203) (meaning t m 4533) source

theorem rule23013 (p2027 p2177 p2901 p3497 p4132 p4556 : Prop) (h : (¬ p2901) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4556) ∨ (¬ p4132) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12269 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23013 (meaning t m 2027) (meaning t m 2177) (meaning t m 2901) (meaning t m 3497) (meaning t m 4132) (meaning t m 4556) source

theorem rule23015 (p2027 p2241 p2396 p2901 p2992 p3540 p4278 p4556 p5193 : Prop) (h : (¬ p2396) ∨ (¬ p4556) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4278) ∨ (¬ p2241) ∨ (¬ p3540) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2396) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4556) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12271 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule23015 (meaning t m 2027) (meaning t m 2241) (meaning t m 2396) (meaning t m 2901) (meaning t m 2992) (meaning t m 3540) (meaning t m 4278) (meaning t m 4556) (meaning t m 5193) source

theorem rule23016 (p2027 p2177 p2427 p3880 p4132 p4556 : Prop) (h : p2027 ∨ (¬ p2177) ∨ (¬ p3880) ∨ (¬ p4556) ∨ (¬ p2427) ∨ (¬ p4132)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12272 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23016 (meaning t m 2027) (meaning t m 2177) (meaning t m 2427) (meaning t m 3880) (meaning t m 4132) (meaning t m 4556) source

theorem rule23017 (p3821 p3947 p4155 : Prop) (h : (¬ p3821) ∨ (¬ p4155) ∨ p3947) : (¬ p3821) ∨ (p3947) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial23017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3821)) ∨ (meaning t m 3947) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory12273 (m.theta 0 7) (m.theta 3 7) (m.theta 7 9)
  exact rule23017 (meaning t m 3821) (meaning t m 3947) (meaning t m 4155) source

theorem rule23018 (p2027 p2177 p3051 p3551 p4556 p4984 : Prop) (h : p2027 ∨ (¬ p3051) ∨ (¬ p2177) ∨ (¬ p4556) ∨ (¬ p3551) ∨ (¬ p4984)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3051) ∨ (¬ p3551) ∨ (¬ p4556) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial23018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory12274 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23018 (meaning t m 2027) (meaning t m 2177) (meaning t m 3051) (meaning t m 3551) (meaning t m 4556) (meaning t m 4984) source

theorem rule23019 (p2156 p2563 p4031 : Prop) (h : (¬ p4031) ∨ (¬ p2563) ∨ p2156) : (p2156) ∨ (¬ p2563) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial23019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory12275 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule23019 (meaning t m 2156) (meaning t m 2563) (meaning t m 4031) source

theorem rule23021 (p2027 p2299 p2396 p3692 p4443 p4902 : Prop) (h : (¬ p2396) ∨ (¬ p4443) ∨ (¬ p2299) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3692)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12277 t (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23021 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule23022 (p2027 p2341 p2396 p3570 p3821 p4556 : Prop) (h : (¬ p2396) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4556) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12278 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23022 (meaning t m 2027) (meaning t m 2341) (meaning t m 2396) (meaning t m 3570) (meaning t m 3821) (meaning t m 4556) source

theorem rule23025 (p2027 p2934 p3631 p3742 p3821 p4279 p4814 : Prop) (h : (¬ p3742) ∨ (¬ p4814) ∨ (¬ p3631) ∨ (¬ p4279) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p2934)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3631) ∨ (¬ p3742) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12281 t (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule23025 (meaning t m 2027) (meaning t m 2934) (meaning t m 3631) (meaning t m 3742) (meaning t m 3821) (meaning t m 4279) (meaning t m 4814) source

theorem rule23026 (p2027 p2143 p2192 p2743 p3371 p3646 p5052 : Prop) (h : p2027 ∨ (¬ p2192) ∨ (¬ p3646) ∨ (¬ p2743) ∨ (¬ p2143) ∨ (¬ p3371) ∨ (¬ p5052)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3371) ∨ (¬ p3646) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12282 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule23026 (meaning t m 2027) (meaning t m 2143) (meaning t m 2192) (meaning t m 2743) (meaning t m 3371) (meaning t m 3646) (meaning t m 5052) source

theorem rule23030 (p2027 p2608 p3631 p3821 p4793 p5206 : Prop) (h : (¬ p3631) ∨ p2027 ∨ (¬ p4793) ∨ (¬ p3821) ∨ (¬ p5206) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4793) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial23030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4793)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory12286 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 7 9)
  exact rule23030 (meaning t m 2027) (meaning t m 2608) (meaning t m 3631) (meaning t m 3821) (meaning t m 4793) (meaning t m 5206) source

theorem rule23033 (p2934 p3038 p4281 : Prop) (h : (¬ p4281) ∨ (¬ p2934) ∨ p3038) : (¬ p2934) ∨ (p3038) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial23033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2934)) ∨ (meaning t m 3038) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory12289 (m.theta 1 3) (m.theta 1 4) (m.theta 1 7)
  exact rule23033 (meaning t m 2934) (meaning t m 3038) (meaning t m 4281) source

theorem rule23035 (p2027 p2247 p2608 p2742 p2839 p5052 : Prop) (h : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p5052) ∨ (¬ p2742) ∨ p2027 ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2839) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12291 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5)
  exact rule23035 (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2742) (meaning t m 2839) (meaning t m 5052) source

theorem rule23036 (p2027 p2140 p2717 p3556 p3570 p3587 : Prop) (h : p2027 ∨ (¬ p2140) ∨ (¬ p3556) ∨ (¬ p3587) ∨ (¬ p3570) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2717) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial23036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory12292 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule23036 (meaning t m 2027) (meaning t m 2140) (meaning t m 2717) (meaning t m 3556) (meaning t m 3570) (meaning t m 3587) source

theorem rule23037 (p2027 p2143 p2891 p3371 p3556 p3585 p4884 : Prop) (h : (¬ p4884) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p3371) ∨ (¬ p3556) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p3556) ∨ (¬ p3585) ∨ (¬ p4884) := by
  classical
  tauto

theorem initial23037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4884)) := by
  have source := ElevenTheory.theory12293 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule23037 (meaning t m 2027) (meaning t m 2143) (meaning t m 2891) (meaning t m 3371) (meaning t m 3556) (meaning t m 3585) (meaning t m 4884) source

theorem rule23038 (p2027 p2247 p3506 p3645 p3646 p3830 p3853 p3989 p4959 p5123 p5580 : Prop) (h : (¬ p3989) ∨ (¬ p4959) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p5123) ∨ (¬ p2247) ∨ (¬ p5580) ∨ (¬ p3853) ∨ (¬ p3830) ∨ (¬ p3646) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3989) ∨ (¬ p4959) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4959)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12294 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 1 9) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23038 (meaning t m 2027) (meaning t m 2247) (meaning t m 3506) (meaning t m 3645) (meaning t m 3646) (meaning t m 3830) (meaning t m 3853) (meaning t m 3989) (meaning t m 4959) (meaning t m 5123) (meaning t m 5580) source

theorem rule23040 (p2027 p2177 p3105 p3694 p4132 p4402 p4556 : Prop) (h : (¬ p4132) ∨ (¬ p3694) ∨ (¬ p3105) ∨ (¬ p4402) ∨ (¬ p2177) ∨ (¬ p4556) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4402) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12296 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8)
  exact rule23040 (meaning t m 2027) (meaning t m 2177) (meaning t m 3105) (meaning t m 3694) (meaning t m 4132) (meaning t m 4402) (meaning t m 4556) source

theorem rule23041 (p2027 p2534 p3073 p3742 p4186 p4688 p4814 : Prop) (h : (¬ p4814) ∨ (¬ p3742) ∨ (¬ p4186) ∨ p2027 ∨ (¬ p4688) ∨ (¬ p3073) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3742) ∨ (¬ p4186) ∨ (¬ p4688) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4688)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12297 t (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule23041 (meaning t m 2027) (meaning t m 2534) (meaning t m 3073) (meaning t m 3742) (meaning t m 4186) (meaning t m 4688) (meaning t m 4814) source

theorem rule23042 (p2027 p2192 p2440 p3646 p3948 p4031 p4814 : Prop) (h : (¬ p3948) ∨ (¬ p3646) ∨ (¬ p2192) ∨ (¬ p4031) ∨ (¬ p4814) ∨ p2027 ∨ (¬ p2440)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2440) ∨ (¬ p3646) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12298 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule23042 (meaning t m 2027) (meaning t m 2192) (meaning t m 2440) (meaning t m 3646) (meaning t m 3948) (meaning t m 4031) (meaning t m 4814) source

theorem rule23044 (p2027 p2210 p2737 p3365 p3873 p4877 : Prop) (h : (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4877) ∨ (¬ p2737) ∨ (¬ p2210) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12300 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3)
  exact rule23044 (meaning t m 2027) (meaning t m 2210) (meaning t m 2737) (meaning t m 3365) (meaning t m 3873) (meaning t m 4877) source

theorem rule23045 (p2027 p2737 p3365 p3399 p3873 p4796 : Prop) (h : (¬ p4796) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3873) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial23045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory12301 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3)
  exact rule23045 (meaning t m 2027) (meaning t m 2737) (meaning t m 3365) (meaning t m 3399) (meaning t m 3873) (meaning t m 4796) source

theorem rule23046 (p2027 p2191 p3093 p3555 p4507 p4516 : Prop) (h : (¬ p4516) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p4507) ∨ (¬ p2191) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2191) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4507) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial23046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory12302 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8)
  exact rule23046 (meaning t m 2027) (meaning t m 2191) (meaning t m 3093) (meaning t m 3555) (meaning t m 4507) (meaning t m 4516) source

theorem rule23049 (p2363 p2396 p3955 p4443 : Prop) (h : (¬ p4443) ∨ (¬ p2396) ∨ (¬ p3955) ∨ p2363) : (p2363) ∨ (¬ p2396) ∨ (¬ p3955) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial23049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory12305 (m.theta 6 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23049 (meaning t m 2363) (meaning t m 2396) (meaning t m 3955) (meaning t m 4443) source

theorem rule23051 (p2027 p2210 p2749 p3859 p4181 p4416 p4877 p5590 : Prop) (h : (¬ p2210) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p5590) ∨ (¬ p4416) ∨ (¬ p2749) ∨ (¬ p3859) ∨ (¬ p4181)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2749) ∨ (¬ p3859) ∨ (¬ p4181) ∨ (¬ p4416) ∨ (¬ p4877) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial23051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory12307 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 8) (m.theta 8 10)
  exact rule23051 (meaning t m 2027) (meaning t m 2210) (meaning t m 2749) (meaning t m 3859) (meaning t m 4181) (meaning t m 4416) (meaning t m 4877) (meaning t m 5590) source

theorem rule23052 (p3955 p3990 p4187 : Prop) (h : (¬ p4187) ∨ (¬ p3955) ∨ p3990) : (¬ p3955) ∨ (p3990) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial23052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3955)) ∨ (meaning t m 3990) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory12308 (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule23052 (meaning t m 3955) (meaning t m 3990) (meaning t m 4187) source

theorem rule23053 (p2027 p2191 p2311 p3631 p3821 p4356 p4431 p4507 : Prop) (h : (¬ p3821) ∨ (¬ p4356) ∨ (¬ p2311) ∨ (¬ p4431) ∨ (¬ p4507) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p3631)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2311) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4356) ∨ (¬ p4431) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12309 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule23053 (meaning t m 2027) (meaning t m 2191) (meaning t m 2311) (meaning t m 3631) (meaning t m 3821) (meaning t m 4356) (meaning t m 4431) (meaning t m 4507) source

theorem rule23054 (p2027 p2210 p3631 p3687 p3821 p4877 p5206 : Prop) (h : (¬ p2210) ∨ (¬ p3687) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p5206) ∨ (¬ p4877)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p4877) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial23054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory12310 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 7 9)
  exact rule23054 (meaning t m 2027) (meaning t m 2210) (meaning t m 3631) (meaning t m 3687) (meaning t m 3821) (meaning t m 4877) (meaning t m 5206) source

theorem rule23055 (p2003 p2027 p2352 p2387 p2396 p2997 p3581 p4278 : Prop) (h : p2997 ∨ (¬ p2352) ∨ (¬ p2003) ∨ (¬ p2387) ∨ (¬ p3581) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2396)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3581) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial23055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory12311 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule23055 (meaning t m 2003) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2396) (meaning t m 2997) (meaning t m 3581) (meaning t m 4278) source

theorem rule23059 (p2027 p2696 p3005 p3540 p4009 p4278 p4381 p4729 p5119 : Prop) (h : (¬ p3005) ∨ (¬ p4729) ∨ (¬ p4009) ∨ (¬ p3540) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p4278) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3540) ∨ (¬ p4009) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial23059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory12315 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23059 (meaning t m 2027) (meaning t m 2696) (meaning t m 3005) (meaning t m 3540) (meaning t m 4009) (meaning t m 4278) (meaning t m 4381) (meaning t m 4729) (meaning t m 5119) source

theorem rule23061 (p3359 p3742 p4635 : Prop) (h : (¬ p4635) ∨ (¬ p3742) ∨ p3359) : (p3359) ∨ (¬ p3742) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial23061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3359) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory12317 (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule23061 (meaning t m 3359) (meaning t m 3742) (meaning t m 4635) source

theorem rule23064 (p3486 p4282 p4320 : Prop) (h : (¬ p4282) ∨ (¬ p3486) ∨ p4320) : (¬ p3486) ∨ (¬ p4282) ∨ (p4320) := by
  classical
  tauto

theorem initial23064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4282)) ∨ (meaning t m 4320) := by
  have source := ElevenTheory.theory12320 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule23064 (meaning t m 3486) (meaning t m 4282) (meaning t m 4320) source

theorem rule23066 (p2027 p3073 p3449 p3645 p3646 p3954 p3989 p4877 p5118 p5580 : Prop) (h : p2027 ∨ (¬ p5118) ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p4877) ∨ (¬ p3954) ∨ (¬ p5580) ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p3645)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12322 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23066 (meaning t m 2027) (meaning t m 3073) (meaning t m 3449) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 3989) (meaning t m 4877) (meaning t m 5118) (meaning t m 5580) source

theorem rule23070 (p1994 p2027 p2630 p2873 p3093 p3555 p3922 p4195 : Prop) (h : (¬ p3922) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p1994) ∨ (¬ p3555) ∨ p2873 ∨ (¬ p4195) ∨ (¬ p3093)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2873) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3922) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial23070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory12326 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule23070 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2873) (meaning t m 3093) (meaning t m 3555) (meaning t m 3922) (meaning t m 4195) source

theorem rule23073 (p2027 p3516 p3947 p3986 p4067 p4120 p4507 p4988 : Prop) (h : (¬ p4120) ∨ (¬ p4067) ∨ (¬ p3986) ∨ (¬ p4507) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p3986) ∨ (¬ p4067) ∨ (¬ p4120) ∨ (¬ p4507) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial23073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory12329 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule23073 (meaning t m 2027) (meaning t m 3516) (meaning t m 3947) (meaning t m 3986) (meaning t m 4067) (meaning t m 4120) (meaning t m 4507) (meaning t m 4988) source

theorem rule23074 (p2982 p3695 p4385 : Prop) (h : (¬ p2982) ∨ (¬ p3695) ∨ (¬ p4385)) : (¬ p2982) ∨ (¬ p3695) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial23074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory12330 (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule23074 (meaning t m 2982) (meaning t m 3695) (meaning t m 4385) source

theorem rule23076 (p2027 p2284 p3680 p4314 p5043 p5284 : Prop) (h : (¬ p4314) ∨ (¬ p5043) ∨ (¬ p2284) ∨ (¬ p3680) ∨ (¬ p5284) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p5043) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 5043)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory12332 t (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule23076 (meaning t m 2027) (meaning t m 2284) (meaning t m 3680) (meaning t m 4314) (meaning t m 5043) (meaning t m 5284) source

theorem rule23077 (p2027 p2143 p2264 p2696 p2742 p3027 p3556 p3583 p3690 p4666 p4737 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p2742) ∨ (¬ p2143) ∨ (¬ p4737) ∨ (¬ p3027) ∨ (¬ p3690) ∨ (¬ p3583) ∨ (¬ p3556) ∨ (¬ p2264) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p4666) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12333 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23077 (meaning t m 2027) (meaning t m 2143) (meaning t m 2264) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3556) (meaning t m 3583) (meaning t m 3690) (meaning t m 4666) (meaning t m 4737) source

theorem rule23078 (p2027 p2144 p2307 p2962 p3688 p3822 p4737 : Prop) (h : (¬ p2144) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2307) ∨ (¬ p3688) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12334 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7)
  exact rule23078 (meaning t m 2027) (meaning t m 2144) (meaning t m 2307) (meaning t m 2962) (meaning t m 3688) (meaning t m 3822) (meaning t m 4737) source

theorem rule23082 (p2027 p2641 p2696 p2742 p3323 p3551 p3588 p3959 p4330 p4348 p4737 : Prop) (h : (¬ p2696) ∨ (¬ p3588) ∨ (¬ p2641) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2742) ∨ (¬ p4330) ∨ (¬ p3959) ∨ (¬ p4737) ∨ (¬ p4348) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12338 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23082 (meaning t m 2027) (meaning t m 2641) (meaning t m 2696) (meaning t m 2742) (meaning t m 3323) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) (meaning t m 4330) (meaning t m 4348) (meaning t m 4737) source

theorem rule23086 (p2027 p2459 p2641 p2668 p2696 p2742 p3588 p3857 p3959 p3961 p4133 p4737 : Prop) (h : (¬ p3961) ∨ (¬ p3857) ∨ (¬ p2641) ∨ (¬ p4737) ∨ (¬ p4133) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3959) ∨ (¬ p3588) ∨ (¬ p2696) ∨ (¬ p2742)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3588) ∨ (¬ p3857) ∨ (¬ p3959) ∨ (¬ p3961) ∨ (¬ p4133) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12342 t (m.theta 0 2) (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23086 (meaning t m 2027) (meaning t m 2459) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) (meaning t m 3588) (meaning t m 3857) (meaning t m 3959) (meaning t m 3961) (meaning t m 4133) (meaning t m 4737) source

theorem rule23087 (p1990 p2027 p2241 p2427 p2542 p2699 p2727 p4204 : Prop) (h : (¬ p2427) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (¬ p4204) ∨ (¬ p2727) ∨ p2699 ∨ p2027 ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial23087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory12343 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule23087 (meaning t m 1990) (meaning t m 2027) (meaning t m 2241) (meaning t m 2427) (meaning t m 2542) (meaning t m 2699) (meaning t m 2727) (meaning t m 4204) source

theorem rule23088 (p2027 p2313 p2518 p2528 p2598 p2785 p3590 p3688 p4107 p4669 p4737 : Prop) (h : (¬ p2313) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2785) ∨ (¬ p4107) ∨ (¬ p2598) ∨ (¬ p2528) ∨ (¬ p2518) ∨ (¬ p4737) ∨ (¬ p3688) ∨ (¬ p3590)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12344 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23088 (meaning t m 2027) (meaning t m 2313) (meaning t m 2518) (meaning t m 2528) (meaning t m 2598) (meaning t m 2785) (meaning t m 3590) (meaning t m 3688) (meaning t m 4107) (meaning t m 4669) (meaning t m 4737) source

theorem rule23090 (p2027 p2299 p2313 p2696 p2742 p2785 p2992 p3156 p3688 p4737 p4902 : Prop) (h : (¬ p3156) ∨ (¬ p2313) ∨ (¬ p2992) ∨ (¬ p2299) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p3688) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p2785) ∨ (¬ p4902)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2785) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3688) ∨ (¬ p4737) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12346 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23090 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2696) (meaning t m 2742) (meaning t m 2785) (meaning t m 2992) (meaning t m 3156) (meaning t m 3688) (meaning t m 4737) (meaning t m 4902) source

theorem rule23091 (p2027 p2177 p2311 p2696 p2742 p2785 p2901 p2992 p3551 p3688 p4556 p4737 : Prop) (h : (¬ p2742) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2696) ∨ (¬ p2992) ∨ (¬ p4556) ∨ (¬ p4737) ∨ (¬ p3688) ∨ (¬ p2785) ∨ (¬ p2311) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2785) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p4556) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12347 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23091 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2696) (meaning t m 2742) (meaning t m 2785) (meaning t m 2901) (meaning t m 2992) (meaning t m 3551) (meaning t m 3688) (meaning t m 4556) (meaning t m 4737) source

theorem rule23093 (p2027 p2696 p2742 p2901 p2911 p2992 p3363 p3551 p3585 p4647 p4737 p5197 : Prop) (h : (¬ p4737) ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p2742) ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p5197) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p4647) ∨ (¬ p3585) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p2992) ∨ (¬ p3363) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p4647) ∨ (¬ p4737) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial23093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory12349 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule23093 (meaning t m 2027) (meaning t m 2696) (meaning t m 2742) (meaning t m 2901) (meaning t m 2911) (meaning t m 2992) (meaning t m 3363) (meaning t m 3551) (meaning t m 3585) (meaning t m 4647) (meaning t m 4737) (meaning t m 5197) source

theorem rule23096 (p2027 p2707 p2819 p3923 p3953 p4476 : Prop) (h : (¬ p4476) ∨ (¬ p3953) ∨ (¬ p2707) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p3923)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2819) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4476) := by
  classical
  tauto

theorem initial23096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4476)) := by
  have source := ElevenTheory.theory12352 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 8)
  exact rule23096 (meaning t m 2027) (meaning t m 2707) (meaning t m 2819) (meaning t m 3923) (meaning t m 3953) (meaning t m 4476) source

theorem rule23097 (p3362 p3589 p4079 : Prop) (h : (¬ p3362) ∨ (¬ p3589) ∨ p4079) : (¬ p3362) ∨ (¬ p3589) ∨ (p4079) := by
  classical
  tauto

theorem initial23097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3589)) ∨ (meaning t m 4079) := by
  have source := ElevenTheory.theory12353 (m.theta 0 1) (m.theta 0 2) (m.theta 0 4)
  exact rule23097 (meaning t m 3362) (meaning t m 3589) (meaning t m 4079) source

theorem rule23098 (p1992 p2027 p2579 p3008 p3389 p3585 p3876 : Prop) (h : p2027 ∨ (¬ p2579) ∨ (¬ p3876) ∨ (¬ p1992) ∨ (¬ p3389) ∨ p3008 ∨ (¬ p3585)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2579) ∨ (p3008) ∨ (¬ p3389) ∨ (¬ p3585) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial23098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory12354 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule23098 (meaning t m 1992) (meaning t m 2027) (meaning t m 2579) (meaning t m 3008) (meaning t m 3389) (meaning t m 3585) (meaning t m 3876) source

theorem rule23100 (p2027 p2341 p2657 p3553 p4067 p4104 p4975 : Prop) (h : (¬ p2341) ∨ (¬ p4975) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4104) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2657) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4104) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12356 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule23100 (meaning t m 2027) (meaning t m 2341) (meaning t m 2657) (meaning t m 3553) (meaning t m 4067) (meaning t m 4104) (meaning t m 4975) source

theorem rule23102 (p2027 p2696 p2742 p2992 p3156 p3363 p3540 p3585 p3644 p4737 p4902 : Prop) (h : (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p2992) ∨ (¬ p4902) ∨ (¬ p2696) ∨ (¬ p4737) ∨ (¬ p3540) ∨ (¬ p3156) ∨ (¬ p2742) ∨ p2027) : (p2027) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4737) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12358 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8)
  exact rule23102 (meaning t m 2027) (meaning t m 2696) (meaning t m 2742) (meaning t m 2992) (meaning t m 3156) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 3644) (meaning t m 4737) (meaning t m 4902) source

theorem rule23104 (p2027 p2608 p3707 p3773 p5329 p5486 : Prop) (h : (¬ p5486) ∨ p2027 ∨ (¬ p3773) ∨ (¬ p2608) ∨ (¬ p3707) ∨ (¬ p5329)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3707) ∨ (¬ p3773) ∨ (¬ p5329) ∨ (¬ p5486) := by
  classical
  tauto

theorem initial23104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 5329)) ∨ (¬ (meaning t m 5486)) := by
  have source := ElevenTheory.theory12360 t (m.theta 0 1) (m.theta 0 9) (m.theta 1 2) (m.theta 1 9) (m.theta 9 10)
  exact rule23104 (meaning t m 2027) (meaning t m 2608) (meaning t m 3707) (meaning t m 3773) (meaning t m 5329) (meaning t m 5486) source

theorem rule23105 (p2027 p2534 p2563 p3146 p4507 p4607 : Prop) (h : (¬ p3146) ∨ (¬ p2534) ∨ (¬ p2563) ∨ (¬ p4507) ∨ (¬ p4607) ∨ p2027) : (p2027) ∨ (¬ p2534) ∨ (¬ p2563) ∨ (¬ p3146) ∨ (¬ p4507) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial23105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory12361 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule23105 (meaning t m 2027) (meaning t m 2534) (meaning t m 2563) (meaning t m 3146) (meaning t m 4507) (meaning t m 4607) source

theorem rule23109 (p2027 p2579 p3367 p3422 p3905 p4734 : Prop) (h : (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4734) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12365 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6)
  exact rule23109 (meaning t m 2027) (meaning t m 2579) (meaning t m 3367) (meaning t m 3422) (meaning t m 3905) (meaning t m 4734) source

theorem rule23110 (p2027 p2663 p2952 p3389 p3742 p4701 : Prop) (h : (¬ p4701) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3742) ∨ (¬ p3389) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12366 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule23110 (meaning t m 2027) (meaning t m 2663) (meaning t m 2952) (meaning t m 3389) (meaning t m 3742) (meaning t m 4701) source

theorem rule23111 (p2027 p2657 p2743 p2829 p3361 p4328 p4975 : Prop) (h : (¬ p4328) ∨ (¬ p3361) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2657) ∨ (¬ p4975)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3361) ∨ (¬ p4328) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12367 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6)
  exact rule23111 (meaning t m 2027) (meaning t m 2657) (meaning t m 2743) (meaning t m 2829) (meaning t m 3361) (meaning t m 4328) (meaning t m 4975) source

theorem rule23112 (p2027 p2299 p2313 p2373 p2406 p2598 p2785 p3590 p3688 p4737 p4902 : Prop) (h : (¬ p2373) ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p4902) ∨ (¬ p4737) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p3590)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4737) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12368 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23112 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2373) (meaning t m 2406) (meaning t m 2598) (meaning t m 2785) (meaning t m 3590) (meaning t m 3688) (meaning t m 4737) (meaning t m 4902) source

theorem rule23113 (p2027 p2667 p2727 p2952 p3987 p4154 p4701 : Prop) (h : p2027 ∨ (¬ p2952) ∨ (¬ p4701) ∨ (¬ p2727) ∨ (¬ p3987) ∨ (¬ p2667) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p4154) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12369 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule23113 (meaning t m 2027) (meaning t m 2667) (meaning t m 2727) (meaning t m 2952) (meaning t m 3987) (meaning t m 4154) (meaning t m 4701) source

theorem rule23114 (p2027 p2440 p3016 p4203 p4948 p5043 : Prop) (h : (¬ p4203) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p5043) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p4948) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial23114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory12370 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule23114 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4203) (meaning t m 4948) (meaning t m 5043) source

theorem rule23115 (p3581 p4646 p4717 : Prop) (h : (¬ p4717) ∨ (¬ p3581) ∨ p4646) : (¬ p3581) ∨ (p4646) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial23115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3581)) ∨ (meaning t m 4646) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory12371 t (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule23115 (meaning t m 3581) (meaning t m 4646) (meaning t m 4717) source

theorem rule23116 (p2027 p2449 p2995 p3497 p3581 p4203 p4278 p4507 : Prop) (h : (¬ p2995) ∨ (¬ p4203) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p3497) ∨ (¬ p2449) ∨ (¬ p3581)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3497) ∨ (¬ p3581) ∨ (¬ p4203) ∨ (¬ p4278) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12372 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule23116 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3497) (meaning t m 3581) (meaning t m 4203) (meaning t m 4278) (meaning t m 4507) source

theorem rule23117 (p2027 p2406 p2630 p3879 p4315 p4814 : Prop) (h : (¬ p2406) ∨ (¬ p4315) ∨ (¬ p3879) ∨ (¬ p4814) ∨ (¬ p2630) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2630) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12373 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule23117 (meaning t m 2027) (meaning t m 2406) (meaning t m 2630) (meaning t m 3879) (meaning t m 4315) (meaning t m 4814) source

theorem rule23118 (p2027 p2563 p3969 p4286 p4507 p4607 : Prop) (h : (¬ p3969) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p4286) ∨ (¬ p4607) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3969) ∨ (¬ p4286) ∨ (¬ p4507) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial23118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory12374 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule23118 (meaning t m 2027) (meaning t m 2563) (meaning t m 3969) (meaning t m 4286) (meaning t m 4507) (meaning t m 4607) source

theorem rule23119 (p2027 p2191 p2641 p3156 p3368 p3413 p4975 : Prop) (h : (¬ p4975) ∨ (¬ p3413) ∨ (¬ p3368) ∨ (¬ p2641) ∨ (¬ p3156) ∨ (¬ p2191) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2641) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3413) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12375 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule23119 (meaning t m 2027) (meaning t m 2191) (meaning t m 2641) (meaning t m 3156) (meaning t m 3368) (meaning t m 3413) (meaning t m 4975) source

theorem rule23120 (p2027 p2177 p2311 p2406 p2427 p2598 p2785 p3551 p3590 p3688 p4556 p4737 : Prop) (h : (¬ p2177) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2311) ∨ (¬ p4737) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p2406) ∨ (¬ p3590)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4556) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12376 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23120 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2406) (meaning t m 2427) (meaning t m 2598) (meaning t m 2785) (meaning t m 3551) (meaning t m 3590) (meaning t m 3688) (meaning t m 4556) (meaning t m 4737) source

theorem rule23121 (p2027 p2396 p2427 p4382 p4556 p4948 : Prop) (h : p2027 ∨ (¬ p2396) ∨ (¬ p2427) ∨ (¬ p4948) ∨ (¬ p4556) ∨ (¬ p4382)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2427) ∨ (¬ p4382) ∨ (¬ p4556) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial23121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory12377 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule23121 (meaning t m 2027) (meaning t m 2396) (meaning t m 2427) (meaning t m 4382) (meaning t m 4556) (meaning t m 4948) source

theorem rule23123 (p2027 p2406 p3032 p3379 p3740 p4366 p4644 : Prop) (h : (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p3032) ∨ p2027 ∨ (¬ p3740) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2406) ∨ (¬ p3032) ∨ (¬ p3379) ∨ (¬ p3740) ∨ (¬ p4366) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12379 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule23123 (meaning t m 2027) (meaning t m 2406) (meaning t m 3032) (meaning t m 3379) (meaning t m 3740) (meaning t m 4366) (meaning t m 4644) source

theorem rule23124 (p2027 p2406 p2498 p3379 p3591 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p2498) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p2406)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12380 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6)
  exact rule23124 (meaning t m 2027) (meaning t m 2406) (meaning t m 2498) (meaning t m 3379) (meaning t m 3591) (meaning t m 4715) source

theorem rule23125 (p1991 p2287 p2657 p4972 : Prop) (h : (¬ p1991) ∨ p2287 ∨ (¬ p2657) ∨ p4972) : (¬ p1991) ∨ (p2287) ∨ (¬ p2657) ∨ (p4972) := by
  classical
  tauto

theorem initial23125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 4972) := by
  have source := ElevenTheory.theory12381 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule23125 (meaning t m 1991) (meaning t m 2287) (meaning t m 2657) (meaning t m 4972) source

theorem rule23126 (p2027 p2440 p2657 p2850 p3475 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p3475) ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12382 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule23126 (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2850) (meaning t m 3475) (meaning t m 4787) source

theorem rule23127 (p2027 p2241 p2449 p3027 p3055 p3684 p3951 p4736 p4948 : Prop) (h : (¬ p2449) ∨ (¬ p4736) ∨ (¬ p3027) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3951) ∨ (¬ p3055) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3951) ∨ (¬ p4736) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial23127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory12383 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 9)
  exact rule23127 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3055) (meaning t m 3684) (meaning t m 3951) (meaning t m 4736) (meaning t m 4948) source

theorem rule23128 (p2027 p2136 p2696 p2870 p3556 p5049 : Prop) (h : (¬ p2696) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p2136) ∨ (¬ p3556) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2696) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12384 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule23128 (meaning t m 2027) (meaning t m 2136) (meaning t m 2696) (meaning t m 2870) (meaning t m 3556) (meaning t m 5049) source

theorem rule23129 (p2027 p3212 p3556 p4135 p4277 p4278 : Prop) (h : (¬ p4277) ∨ (¬ p3556) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4135) ∨ (¬ p3212)) : (p2027) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial23129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory12385 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule23129 (meaning t m 2027) (meaning t m 3212) (meaning t m 3556) (meaning t m 4135) (meaning t m 4277) (meaning t m 4278) source

theorem rule23130 (p2027 p2137 p2191 p2220 p2737 p4874 p5049 : Prop) (h : (¬ p2137) ∨ (¬ p4874) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p5049) ∨ (¬ p2737) ∨ p2027) : (p2027) ∨ (¬ p2137) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2737) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12386 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule23130 (meaning t m 2027) (meaning t m 2137) (meaning t m 2191) (meaning t m 2220) (meaning t m 2737) (meaning t m 4874) (meaning t m 5049) source

theorem rule23132 (p2027 p2136 p2696 p2860 p3646 p5049 : Prop) (h : (¬ p2696) ∨ (¬ p3646) ∨ (¬ p2860) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p5049)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2696) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12388 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule23132 (meaning t m 2027) (meaning t m 2136) (meaning t m 2696) (meaning t m 2860) (meaning t m 3646) (meaning t m 5049) source

theorem rule23133 (p2027 p2950 p3136 p3156 p4120 p4787 : Prop) (h : (¬ p4787) ∨ (¬ p2950) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12389 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule23133 (meaning t m 2027) (meaning t m 2950) (meaning t m 3136) (meaning t m 3156) (meaning t m 4120) (meaning t m 4787) source

theorem rule23135 (p2027 p2254 p2299 p2417 p2922 p2963 p3379 p3568 p4668 : Prop) (h : (¬ p2299) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12391 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23135 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2417) (meaning t m 2922) (meaning t m 2963) (meaning t m 3379) (meaning t m 3568) (meaning t m 4668) source

theorem rule23136 (p2027 p2476 p2881 p3389 p4277 p4383 : Prop) (h : (¬ p4277) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p2476) ∨ p2027) : (p2027) ∨ (¬ p2476) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p4277) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial23136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory12392 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule23136 (meaning t m 2027) (meaning t m 2476) (meaning t m 2881) (meaning t m 3389) (meaning t m 4277) (meaning t m 4383) source

theorem rule23137 (p2027 p2284 p2630 p2950 p3413 p3646 p4787 : Prop) (h : (¬ p2630) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p2284) ∨ (¬ p4787) ∨ p2027 ∨ (¬ p2950)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2630) ∨ (¬ p2950) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12393 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule23137 (meaning t m 2027) (meaning t m 2284) (meaning t m 2630) (meaning t m 2950) (meaning t m 3413) (meaning t m 3646) (meaning t m 4787) source

theorem rule23138 (p2027 p3506 p3568 p4191 p4421 p4624 : Prop) (h : (¬ p3506) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4624)) : (p2027) ∨ (¬ p3506) ∨ (¬ p3568) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory12394 t (m.theta 3 6) (m.theta 3 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule23138 (meaning t m 2027) (meaning t m 3506) (meaning t m 3568) (meaning t m 4191) (meaning t m 4421) (meaning t m 4624) source

theorem rule23139 (p2027 p3707 p4173 p4322 p4942 p5046 : Prop) (h : p2027 ∨ (¬ p5046) ∨ (¬ p4942) ∨ (¬ p4173) ∨ (¬ p3707) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3707) ∨ (¬ p4173) ∨ (¬ p4322) ∨ (¬ p4942) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4942)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory12395 t (m.theta 1 5) (m.theta 1 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule23139 (meaning t m 2027) (meaning t m 3707) (meaning t m 4173) (meaning t m 4322) (meaning t m 4942) (meaning t m 5046) source

theorem rule23141 (p2027 p2187 p2860 p4244 p4275 p4405 : Prop) (h : (¬ p2860) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4405) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial23141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory12397 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule23141 (meaning t m 2027) (meaning t m 2187) (meaning t m 2860) (meaning t m 4244) (meaning t m 4275) (meaning t m 4405) source

theorem rule23143 (p2027 p2417 p2780 p2922 p3379 p3950 p4347 p4358 p4736 : Prop) (h : (¬ p4358) ∨ (¬ p2417) ∨ (¬ p3379) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2922) ∨ (¬ p4736) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2780) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12399 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23143 (meaning t m 2027) (meaning t m 2417) (meaning t m 2780) (meaning t m 2922) (meaning t m 3379) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) (meaning t m 4736) source

theorem rule23144 (p2027 p2387 p2668 p2797 p3983 p4787 : Prop) (h : (¬ p2797) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p4787) ∨ (¬ p3983)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p3983) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12400 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8)
  exact rule23144 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2797) (meaning t m 3983) (meaning t m 4787) source

theorem rule23146 (p2027 p2963 p3286 p3917 p4367 p4843 : Prop) (h : (¬ p4843) ∨ (¬ p2963) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p4367) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p3917) ∨ (¬ p4367) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial23146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory12402 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule23146 (meaning t m 2027) (meaning t m 2963) (meaning t m 3286) (meaning t m 3917) (meaning t m 4367) (meaning t m 4843) source

theorem rule23147 (p2027 p2177 p2311 p3204 p3319 p3551 p4624 : Prop) (h : (¬ p3319) ∨ (¬ p2311) ∨ (¬ p2177) ∨ (¬ p3204) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4624)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3204) ∨ (¬ p3319) ∨ (¬ p3551) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory12403 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule23147 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 3204) (meaning t m 3319) (meaning t m 3551) (meaning t m 4624) source

theorem rule23149 (p1991 p2027 p2952 p2997 p3136 p3568 p4195 : Prop) (h : (¬ p1991) ∨ (¬ p3568) ∨ p2027 ∨ p2997 ∨ (¬ p4195) ∨ (¬ p2952) ∨ (¬ p3136)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3136) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial23149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory12405 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule23149 (meaning t m 1991) (meaning t m 2027) (meaning t m 2952) (meaning t m 2997) (meaning t m 3136) (meaning t m 3568) (meaning t m 4195) source

theorem rule23150 (p2027 p2254 p2352 p2493 p2952 p3097 p3379 p3952 p4405 : Prop) (h : (¬ p4405) ∨ (¬ p2493) ∨ (¬ p2352) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3952) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial23150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory12406 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23150 (meaning t m 2027) (meaning t m 2254) (meaning t m 2352) (meaning t m 2493) (meaning t m 2952) (meaning t m 3097) (meaning t m 3379) (meaning t m 3952) (meaning t m 4405) source

theorem rule23151 (p2027 p2187 p3097 p3550 p4260 p5559 : Prop) (h : (¬ p3550) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p5559) ∨ (¬ p4260) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p4260) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial23151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory12407 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule23151 (meaning t m 2027) (meaning t m 2187) (meaning t m 3097) (meaning t m 3550) (meaning t m 4260) (meaning t m 5559) source

theorem rule23152 (p1998 p2027 p2177 p2274 p2829 p3474 p3583 p4185 : Prop) (h : p2027 ∨ (¬ p3583) ∨ p3474 ∨ (¬ p4185) ∨ (¬ p2829) ∨ (¬ p2274) ∨ (¬ p2177) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (p3474) ∨ (¬ p3583) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial23152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory12408 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23152 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2829) (meaning t m 3474) (meaning t m 3583) (meaning t m 4185) source

theorem rule23154 (p3568 p4140 p4153 p4320 : Prop) (h : (¬ p4153) ∨ (¬ p3568) ∨ (¬ p4140) ∨ p4320) : (¬ p3568) ∨ (¬ p4140) ∨ (¬ p4153) ∨ (p4320) := by
  classical
  tauto

theorem initial23154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4153)) ∨ (meaning t m 4320) := by
  have source := ElevenTheory.theory12410 (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7)
  exact rule23154 (meaning t m 3568) (meaning t m 4140) (meaning t m 4153) (meaning t m 4320) source

theorem rule23155 (p2027 p3005 p3551 p3572 p4378 p4851 : Prop) (h : p2027 ∨ (¬ p3551) ∨ (¬ p4378) ∨ (¬ p3572) ∨ (¬ p3005) ∨ (¬ p4851)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4378) ∨ (¬ p4851) := by
  classical
  tauto

theorem initial23155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4851)) := by
  have source := ElevenTheory.theory12411 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule23155 (meaning t m 2027) (meaning t m 3005) (meaning t m 3551) (meaning t m 3572) (meaning t m 4378) (meaning t m 4851) source

theorem rule23156 (p2027 p2138 p2493 p3379 p3564 p3690 p4244 p4621 p4736 : Prop) (h : (¬ p2493) ∨ (¬ p2138) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p4244) ∨ (¬ p3690) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4621)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4621) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12412 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule23156 (meaning t m 2027) (meaning t m 2138) (meaning t m 2493) (meaning t m 3379) (meaning t m 3564) (meaning t m 3690) (meaning t m 4244) (meaning t m 4621) (meaning t m 4736) source

theorem rule23157 (p2027 p2743 p2829 p2963 p4328 p4787 : Prop) (h : (¬ p2829) ∨ (¬ p4328) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p4787)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p2963) ∨ (¬ p4328) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12413 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule23157 (meaning t m 2027) (meaning t m 2743) (meaning t m 2829) (meaning t m 2963) (meaning t m 4328) (meaning t m 4787) source

theorem rule23158 (p2027 p2657 p3201 p3475 p3742 p4787 : Prop) (h : (¬ p2657) ∨ (¬ p4787) ∨ (¬ p3475) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p3742) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12414 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule23158 (meaning t m 2027) (meaning t m 2657) (meaning t m 3201) (meaning t m 3475) (meaning t m 3742) (meaning t m 4787) source

theorem rule23159 (p2027 p2542 p2553 p3568 p4194 p4715 : Prop) (h : (¬ p4194) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2542) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p4194) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12415 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule23159 (meaning t m 2027) (meaning t m 2542) (meaning t m 2553) (meaning t m 3568) (meaning t m 4194) (meaning t m 4715) source

theorem rule23160 (p2027 p2254 p2608 p2707 p2952 p3434 p3570 p4320 p4668 : Prop) (h : p2027 ∨ (¬ p4668) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p3434) ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12416 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23160 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2952) (meaning t m 3434) (meaning t m 3570) (meaning t m 4320) (meaning t m 4668) source

theorem rule23162 (p2027 p2241 p2589 p2641 p3323 p3692 p3880 p4330 p5193 : Prop) (h : (¬ p2241) ∨ (¬ p3323) ∨ (¬ p5193) ∨ (¬ p2641) ∨ (¬ p4330) ∨ (¬ p3692) ∨ (¬ p2589) ∨ (¬ p3880) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12418 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule23162 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 2641) (meaning t m 3323) (meaning t m 3692) (meaning t m 3880) (meaning t m 4330) (meaning t m 5193) source

theorem rule23164 (p2027 p3527 p3570 p4173 p4431 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p4173) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4173) ∨ (¬ p4431) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12420 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule23164 (meaning t m 2027) (meaning t m 3527) (meaning t m 3570) (meaning t m 4173) (meaning t m 4431) (meaning t m 4558) source

theorem rule23165 (p2027 p2241 p2295 p2589 p2641 p3744 p4110 p4620 p5193 : Prop) (h : (¬ p2589) ∨ (¬ p2641) ∨ (¬ p4110) ∨ (¬ p3744) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p4620) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4620) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12421 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule23165 (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2589) (meaning t m 2641) (meaning t m 3744) (meaning t m 4110) (meaning t m 4620) (meaning t m 5193) source

theorem rule23166 (p2027 p2138 p2396 p3093 p3309 p3692 p3694 p3950 p4736 : Prop) (h : (¬ p3692) ∨ (¬ p3950) ∨ (¬ p3694) ∨ (¬ p3309) ∨ (¬ p2138) ∨ (¬ p2396) ∨ (¬ p4736) ∨ (¬ p3093) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12422 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23166 (meaning t m 2027) (meaning t m 2138) (meaning t m 2396) (meaning t m 3093) (meaning t m 3309) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4736) source

theorem rule23167 (p2027 p2241 p2264 p2589 p3027 p3690 p4235 p4666 p5193 : Prop) (h : p2027 ∨ (¬ p4235) ∨ (¬ p2264) ∨ (¬ p3690) ∨ (¬ p4666) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p3027) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4666) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12423 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23167 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2589) (meaning t m 3027) (meaning t m 3690) (meaning t m 4235) (meaning t m 4666) (meaning t m 5193) source

theorem rule23168 (p2027 p2138 p2542 p2598 p3698 p4750 : Prop) (h : (¬ p2598) ∨ (¬ p2542) ∨ (¬ p3698) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2542) ∨ (¬ p2598) ∨ (¬ p3698) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12424 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5)
  exact rule23168 (meaning t m 2027) (meaning t m 2138) (meaning t m 2542) (meaning t m 2598) (meaning t m 3698) (meaning t m 4750) source

theorem rule23170 (p1986 p2027 p2997 p3097 p3367 p3583 p3698 p4110 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p4110) ∨ (¬ p3097) ∨ (¬ p3698) ∨ (¬ p3583) ∨ (¬ p3367) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial23170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory12426 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule23170 (meaning t m 1986) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4110) source

theorem rule23171 (p2027 p2241 p2476 p2534 p2641 p2668 p3146 p4134 p5193 : Prop) (h : (¬ p2641) ∨ (¬ p4134) ∨ (¬ p5193) ∨ (¬ p2668) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12427 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23171 (meaning t m 2027) (meaning t m 2241) (meaning t m 2476) (meaning t m 2534) (meaning t m 2641) (meaning t m 2668) (meaning t m 3146) (meaning t m 4134) (meaning t m 5193) source

theorem rule23172 (p2027 p2532 p3105 p3694 p4118 p5063 : Prop) (h : p2027 ∨ (¬ p3105) ∨ (¬ p2532) ∨ (¬ p4118) ∨ (¬ p3694) ∨ (¬ p5063)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4118) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial23172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory12428 t (m.theta 2 5) (m.theta 3 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule23172 (meaning t m 2027) (meaning t m 2532) (meaning t m 3105) (meaning t m 3694) (meaning t m 4118) (meaning t m 5063) source

theorem rule23175 (p2027 p2579 p2588 p2641 p2668 p2696 p2742 p3363 p3585 p4405 p4737 : Prop) (h : (¬ p2742) ∨ (¬ p2696) ∨ (¬ p2641) ∨ (¬ p4737) ∨ (¬ p2668) ∨ (¬ p4405) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4405) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12431 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23175 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) (meaning t m 3363) (meaning t m 3585) (meaning t m 4405) (meaning t m 4737) source

theorem rule23176 (p2027 p2241 p2476 p2534 p3027 p3931 p4444 p4826 p5193 : Prop) (h : (¬ p3027) ∨ (¬ p4826) ∨ (¬ p3931) ∨ (¬ p2241) ∨ (¬ p2534) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12432 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23176 (meaning t m 2027) (meaning t m 2241) (meaning t m 2476) (meaning t m 2534) (meaning t m 3027) (meaning t m 3931) (meaning t m 4444) (meaning t m 4826) (meaning t m 5193) source

theorem rule23180 (p1992 p2027 p2132 p2780 p2997 p3097 p3583 p4428 : Prop) (h : (¬ p2780) ∨ (¬ p3583) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4428) ∨ p2997 ∨ (¬ p3097)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial23180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory12436 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule23180 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 2997) (meaning t m 3097) (meaning t m 3583) (meaning t m 4428) source

theorem rule23181 (p2027 p2241 p2449 p3027 p3266 p3346 p3950 p4425 p5193 : Prop) (h : (¬ p2241) ∨ (¬ p5193) ∨ (¬ p2449) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p3346) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3950) ∨ (¬ p4425) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12437 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23181 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3266) (meaning t m 3346) (meaning t m 3950) (meaning t m 4425) (meaning t m 5193) source

theorem rule23182 (p2027 p2427 p2850 p3556 p3904 p4727 : Prop) (h : p2027 ∨ (¬ p4727) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p2850) ∨ (¬ p3904)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2850) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial23182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory12438 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23182 (meaning t m 2027) (meaning t m 2427) (meaning t m 2850) (meaning t m 3556) (meaning t m 3904) (meaning t m 4727) source

theorem rule23183 (p1992 p2027 p2143 p2177 p2997 p3570 p3583 p3646 p4204 : Prop) (h : p2997 ∨ (¬ p2177) ∨ (¬ p3583) ∨ (¬ p4204) ∨ (¬ p3570) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial23183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory12439 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23183 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2177) (meaning t m 2997) (meaning t m 3570) (meaning t m 3583) (meaning t m 3646) (meaning t m 4204) source

theorem rule23184 (p2027 p2241 p2449 p2579 p3027 p3950 p3956 p4347 p5193 : Prop) (h : (¬ p3950) ∨ (¬ p5193) ∨ (¬ p2579) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2449) ∨ (¬ p4347) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12440 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23184 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2579) (meaning t m 3027) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) (meaning t m 5193) source

theorem rule23185 (p2027 p2850 p3367 p3688 p4342 p4715 : Prop) (h : (¬ p3688) ∨ (¬ p4342) ∨ (¬ p3367) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p2850)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12441 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule23185 (meaning t m 2027) (meaning t m 2850) (meaning t m 3367) (meaning t m 3688) (meaning t m 4342) (meaning t m 4715) source

theorem rule23188 (p2027 p2088 p2295 p4118 p4170 p4196 p4501 : Prop) (h : (¬ p4196) ∨ (¬ p4170) ∨ (¬ p2088) ∨ (¬ p4118) ∨ (¬ p2295) ∨ (¬ p4501) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p2295) ∨ (¬ p4118) ∨ (¬ p4170) ∨ (¬ p4196) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial23188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory12444 t (m.theta 0 8) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule23188 (meaning t m 2027) (meaning t m 2088) (meaning t m 2295) (meaning t m 4118) (meaning t m 4170) (meaning t m 4196) (meaning t m 4501) source

theorem rule23189 (p2027 p2651 p3172 p3641 p4437 p4753 : Prop) (h : (¬ p2651) ∨ (¬ p4437) ∨ (¬ p4753) ∨ (¬ p3641) ∨ (¬ p3172) ∨ p2027) : (p2027) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p3641) ∨ (¬ p4437) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial23189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory12445 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule23189 (meaning t m 2027) (meaning t m 2651) (meaning t m 3172) (meaning t m 3641) (meaning t m 4437) (meaning t m 4753) source

theorem rule23190 (p2027 p2144 p3051 p3365 p4244 p5052 : Prop) (h : p2027 ∨ (¬ p5052) ∨ (¬ p3365) ∨ (¬ p2144) ∨ (¬ p4244) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p4244) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12446 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule23190 (meaning t m 2027) (meaning t m 2144) (meaning t m 3051) (meaning t m 3365) (meaning t m 4244) (meaning t m 5052) source

theorem rule23191 (p2027 p2166 p2743 p3371 p3694 p5052 : Prop) (h : (¬ p3371) ∨ (¬ p2166) ∨ (¬ p3694) ∨ (¬ p2743) ∨ (¬ p5052) ∨ p2027) : (p2027) ∨ (¬ p2166) ∨ (¬ p2743) ∨ (¬ p3371) ∨ (¬ p3694) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12447 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule23191 (meaning t m 2027) (meaning t m 2166) (meaning t m 2743) (meaning t m 3371) (meaning t m 3694) (meaning t m 5052) source

theorem rule23192 (p1975 p2027 p2427 p2765 p3246 p4107 p4110 : Prop) (h : p2765 ∨ (¬ p4107) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4110) ∨ (¬ p2427)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3246) ∨ (¬ p4107) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial23192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory12448 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule23192 (meaning t m 1975) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3246) (meaning t m 4107) (meaning t m 4110) source

theorem rule23193 (p2027 p3256 p3692 p3952 p4237 p4509 : Prop) (h : (¬ p3256) ∨ (¬ p4237) ∨ (¬ p4509) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial23193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12449 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule23193 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 3952) (meaning t m 4237) (meaning t m 4509) source

theorem rule23195 (p2027 p3136 p3156 p3745 p4195 p4509 : Prop) (h : (¬ p3156) ∨ (¬ p4509) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p3136)) : (p2027) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial23195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12451 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule23195 (meaning t m 2027) (meaning t m 3136) (meaning t m 3156) (meaning t m 3745) (meaning t m 4195) (meaning t m 4509) source

theorem rule23197 (p2027 p2396 p3093 p3309 p3365 p3877 p3950 p4118 p4736 : Prop) (h : (¬ p4118) ∨ (¬ p3950) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12453 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23197 (meaning t m 2027) (meaning t m 2396) (meaning t m 3093) (meaning t m 3309) (meaning t m 3365) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4736) source

theorem rule23199 (p2027 p2230 p2630 p2656 p4195 p4389 p4715 : Prop) (h : p2027 ∨ (¬ p4389) ∨ (¬ p4715) ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12455 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule23199 (meaning t m 2027) (meaning t m 2230) (meaning t m 2630) (meaning t m 2656) (meaning t m 4195) (meaning t m 4389) (meaning t m 4715) source

theorem rule23200 (p2027 p2352 p2493 p3365 p3379 p3568 p4195 p4405 p4736 : Prop) (h : (¬ p3365) ∨ (¬ p2352) ∨ (¬ p4736) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4405) ∨ (¬ p3379) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12456 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23200 (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 3365) (meaning t m 3379) (meaning t m 3568) (meaning t m 4195) (meaning t m 4405) (meaning t m 4736) source

theorem rule23204 (p2027 p2138 p2499 p2518 p2573 p3570 p4079 p4133 p4157 p4244 p4736 : Prop) (h : (¬ p4079) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p4736) ∨ (¬ p2573) ∨ (¬ p2518) ∨ (¬ p4244) ∨ (¬ p2499) ∨ (¬ p4133) ∨ (¬ p4157)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2573) ∨ (¬ p3570) ∨ (¬ p4079) ∨ (¬ p4133) ∨ (¬ p4157) ∨ (¬ p4244) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12460 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23204 (meaning t m 2027) (meaning t m 2138) (meaning t m 2499) (meaning t m 2518) (meaning t m 2573) (meaning t m 3570) (meaning t m 4079) (meaning t m 4133) (meaning t m 4157) (meaning t m 4244) (meaning t m 4736) source

theorem rule23206 (p2027 p2363 p3063 p3093 p3365 p4208 p4315 p4736 p5059 : Prop) (h : (¬ p3063) ∨ (¬ p5059) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2363) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4736) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial23206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory12462 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23206 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3365) (meaning t m 4208) (meaning t m 4315) (meaning t m 4736) (meaning t m 5059) source

theorem rule23207 (p1982 p2027 p2499 p2518 p2528 p2573 p2699 p4079 : Prop) (h : (¬ p2518) ∨ (¬ p4079) ∨ (¬ p2499) ∨ p2699 ∨ (¬ p2573) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (p2699) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial23207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory12463 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule23207 (meaning t m 1982) (meaning t m 2027) (meaning t m 2499) (meaning t m 2518) (meaning t m 2528) (meaning t m 2573) (meaning t m 2699) (meaning t m 4079) source

theorem rule23208 (p2027 p2579 p3212 p4399 p4715 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4715) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p4399)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4715) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial23208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory12464 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule23208 (meaning t m 2027) (meaning t m 2579) (meaning t m 3212) (meaning t m 4399) (meaning t m 4715) (meaning t m 4948) source

theorem rule23209 (p2027 p2138 p2417 p2922 p3379 p3570 p4244 p4668 p4736 : Prop) (h : (¬ p4244) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p2922) ∨ (¬ p2417) ∨ (¬ p4736) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12465 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23209 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 2922) (meaning t m 3379) (meaning t m 3570) (meaning t m 4244) (meaning t m 4668) (meaning t m 4736) source

theorem rule23210 (p2027 p2138 p2510 p2528 p2573 p3570 p4079 p4133 p4244 p4347 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p3570) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2510) ∨ (¬ p4079) ∨ (¬ p4133) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p3570) ∨ (¬ p4079) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4347) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12466 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23210 (meaning t m 2027) (meaning t m 2138) (meaning t m 2510) (meaning t m 2528) (meaning t m 2573) (meaning t m 3570) (meaning t m 4079) (meaning t m 4133) (meaning t m 4244) (meaning t m 4347) (meaning t m 4736) source

theorem rule23212 (p2027 p2383 p2630 p2951 p2962 p4358 p4701 p4841 : Prop) (h : (¬ p4841) ∨ (¬ p4358) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4701) ∨ (¬ p2951) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p4358) ∨ (¬ p4701) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial23212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory12468 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 8)
  exact rule23212 (meaning t m 2027) (meaning t m 2383) (meaning t m 2630) (meaning t m 2951) (meaning t m 2962) (meaning t m 4358) (meaning t m 4701) (meaning t m 4841) source

theorem rule23213 (p2027 p3073 p3365 p3449 p3497 p4315 p4348 p4736 p4905 : Prop) (h : (¬ p3449) ∨ (¬ p4905) ∨ (¬ p3497) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4736) ∨ (¬ p3365) ∨ (¬ p4315)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3449) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial23213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory12469 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23213 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3449) (meaning t m 3497) (meaning t m 4315) (meaning t m 4348) (meaning t m 4736) (meaning t m 4905) source

theorem rule23214 (p2027 p2254 p2307 p3063 p3146 p3172 p3549 p4118 p4134 p5020 : Prop) (h : (¬ p3172) ∨ (¬ p4134) ∨ (¬ p3063) ∨ (¬ p3146) ∨ (¬ p2254) ∨ (¬ p5020) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p4118) ∨ p2027) : (p2027) ∨ (¬ p2254) ∨ (¬ p2307) ∨ (¬ p3063) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3549) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial23214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory12470 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule23214 (meaning t m 2027) (meaning t m 2254) (meaning t m 2307) (meaning t m 3063) (meaning t m 3146) (meaning t m 3172) (meaning t m 3549) (meaning t m 4118) (meaning t m 4134) (meaning t m 5020) source

theorem rule23215 (p2027 p2220 p2437 p3096 p3574 p3575 p4509 p4984 : Prop) (h : (¬ p3096) ∨ (¬ p4984) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p3575) ∨ (¬ p2220) ∨ (¬ p2437) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2437) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p3575) ∨ (¬ p4509) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial23215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory12471 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8)
  exact rule23215 (meaning t m 2027) (meaning t m 2220) (meaning t m 2437) (meaning t m 3096) (meaning t m 3574) (meaning t m 3575) (meaning t m 4509) (meaning t m 4984) source

theorem rule23216 (p2027 p2441 p2449 p3574 p3580 p4278 p4715 : Prop) (h : (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4278) ∨ (¬ p2441)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12472 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule23216 (meaning t m 2027) (meaning t m 2441) (meaning t m 2449) (meaning t m 3574) (meaning t m 3580) (meaning t m 4278) (meaning t m 4715) source

theorem rule23218 (p2011 p2027 p2427 p2765 p3105 p4110 p4244 : Prop) (h : (¬ p2011) ∨ (¬ p3105) ∨ (¬ p4244) ∨ p2765 ∨ (¬ p2427) ∨ (¬ p4110) ∨ p2027) : (¬ p2011) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p4110) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial23218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory12474 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule23218 (meaning t m 2011) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3105) (meaning t m 4110) (meaning t m 4244) source

theorem rule23219 (p2363 p2459 p3550 : Prop) (h : (¬ p3550) ∨ (¬ p2459) ∨ p2363) : (p2363) ∨ (¬ p2459) ∨ (¬ p3550) := by
  classical
  tauto

theorem initial23219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3550)) := by
  have source := ElevenTheory.theory12475 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23219 (meaning t m 2363) (meaning t m 2459) (meaning t m 3550) source

theorem rule23220 (p2027 p2088 p2295 p2312 p4261 p4371 p4590 p4757 : Prop) (h : p2027 ∨ (¬ p2312) ∨ (¬ p4371) ∨ (¬ p2088) ∨ (¬ p4757) ∨ (¬ p4261) ∨ (¬ p4590) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4590) ∨ (¬ p4757) := by
  classical
  tauto

theorem initial23220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4757)) := by
  have source := ElevenTheory.theory12476 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 7) (m.theta 8 9)
  exact rule23220 (meaning t m 2027) (meaning t m 2088) (meaning t m 2295) (meaning t m 2312) (meaning t m 4261) (meaning t m 4371) (meaning t m 4590) (meaning t m 4757) source

theorem rule23222 (p1997 p2027 p2230 p2765 p2901 p3540 p3952 p4001 : Prop) (h : (¬ p2230) ∨ (¬ p4001) ∨ (¬ p2901) ∨ p2765 ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3952) ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3540) ∨ (¬ p3952) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial23222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory12478 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule23222 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2765) (meaning t m 2901) (meaning t m 3540) (meaning t m 3952) (meaning t m 4001) source

theorem rule23225 (p2027 p3609 p4348 p4423 p4805 p5559 : Prop) (h : (¬ p4805) ∨ (¬ p5559) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p4423) ∨ (¬ p3609)) : (p2027) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4423) ∨ (¬ p4805) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial23225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory12481 t (m.theta 2 7) (m.theta 2 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule23225 (meaning t m 2027) (meaning t m 3609) (meaning t m 4348) (meaning t m 4423) (meaning t m 4805) (meaning t m 5559) source

theorem rule23228 (p2027 p2499 p2972 p3948 p4031 p4032 p4715 : Prop) (h : (¬ p4032) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4715) ∨ (¬ p2499) ∨ (¬ p4031)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4032) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12484 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule23228 (meaning t m 2027) (meaning t m 2499) (meaning t m 2972) (meaning t m 3948) (meaning t m 4031) (meaning t m 4032) (meaning t m 4715) source

theorem rule23229 (p2027 p2122 p2177 p2245 p2774 p2952 p3146 p3661 p4118 p4733 p4905 : Prop) (h : (¬ p2952) ∨ (¬ p2122) ∨ (¬ p2245) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4733) ∨ (¬ p4905) ∨ (¬ p2774) ∨ (¬ p4118) ∨ (¬ p3146) ∨ (¬ p3661)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial23229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory12485 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23229 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2245) (meaning t m 2774) (meaning t m 2952) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4733) (meaning t m 4905) source

theorem rule23230 (p2027 p2307 p2498 p2850 p3822 p4715 p5016 p5220 : Prop) (h : (¬ p2850) ∨ (¬ p5016) ∨ (¬ p2498) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p5220) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2498) ∨ (¬ p2850) ∨ (¬ p3822) ∨ (¬ p4715) ∨ (¬ p5016) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial23230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory12486 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule23230 (meaning t m 2027) (meaning t m 2307) (meaning t m 2498) (meaning t m 2850) (meaning t m 3822) (meaning t m 4715) (meaning t m 5016) (meaning t m 5220) source

theorem rule23231 (p2027 p2850 p2927 p3516 p3543 p3686 p4324 p4644 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p4644) ∨ (¬ p4324) ∨ (¬ p2927) ∨ (¬ p3543) ∨ (¬ p3686) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2927) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3686) ∨ (¬ p4324) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12487 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule23231 (meaning t m 2027) (meaning t m 2850) (meaning t m 2927) (meaning t m 3516) (meaning t m 3543) (meaning t m 3686) (meaning t m 4324) (meaning t m 4644) source

end SunPrize.SMT
