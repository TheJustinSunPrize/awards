import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory023
import SunPrize.Certificate.Theory024
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule17950 (p2001 p2027 p2373 p2622 p2630 p2656 p3051 p4235 p4399 : Prop) (h : (¬ p2001) ∨ (¬ p4399) ∨ (¬ p3051) ∨ (¬ p2630) ∨ (¬ p2373) ∨ p2027 ∨ p2622 ∨ (¬ p2656) ∨ (¬ p4235)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2373) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial17950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory7222 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule17950 (meaning t m 2001) (meaning t m 2027) (meaning t m 2373) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3051) (meaning t m 4235) (meaning t m 4399) source

theorem rule17952 (p1984 p3474 p3555 p4875 : Prop) (h : (¬ p3555) ∨ (¬ p1984) ∨ p3474 ∨ p4875) : (¬ p1984) ∨ (p3474) ∨ (¬ p3555) ∨ (p4875) := by
  classical
  tauto

theorem initial17952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 4875) := by
  have source := ElevenTheory.theory7224 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5)
  exact rule17952 (meaning t m 1984) (meaning t m 3474) (meaning t m 3555) (meaning t m 4875) source

theorem rule17954 (p1988 p2027 p2417 p2622 p2630 p2761 p3389 p3519 p4116 : Prop) (h : (¬ p2417) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p2630) ∨ (¬ p2761) ∨ (¬ p1988) ∨ p2622 ∨ p2027 ∨ (¬ p4116)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2417) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial17954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory7226 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17954 (meaning t m 1988) (meaning t m 2027) (meaning t m 2417) (meaning t m 2622) (meaning t m 2630) (meaning t m 2761) (meaning t m 3389) (meaning t m 3519) (meaning t m 4116) source

theorem rule17956 (p1988 p2027 p2406 p2409 p2761 p3051 p3246 p4109 : Prop) (h : (¬ p3246) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p3051) ∨ p2409) : (¬ p1988) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial17956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory7228 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17956 (meaning t m 1988) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 4109) source

theorem rule17957 (p1983 p2027 p2406 p2409 p2417 p2589 p3389 : Prop) (h : (¬ p2417) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2589) ∨ p2409 ∨ (¬ p1983) ∨ (¬ p3389)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial17957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory7229 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule17957 (meaning t m 1983) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2417) (meaning t m 2589) (meaning t m 3389) source

theorem rule17958 (p1998 p2027 p2545 p2881 p2951 p2992 p3051 p4111 : Prop) (h : (¬ p2992) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4111) ∨ p2545 ∨ (¬ p3051) ∨ (¬ p2951) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2545) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7230 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17958 (meaning t m 1998) (meaning t m 2027) (meaning t m 2545) (meaning t m 2881) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) (meaning t m 4111) source

theorem rule17963 (p2005 p2027 p2187 p2230 p2233 p2563 p3956 : Prop) (h : (¬ p2187) ∨ p2233 ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p3956) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2563) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial17963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7235 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule17963 (meaning t m 2005) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2233) (meaning t m 2563) (meaning t m 3956) source

theorem rule17964 (p1988 p2027 p2707 p2761 p2842 p3516 p3577 p3585 : Prop) (h : p2842 ∨ (¬ p1988) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3577) ∨ (¬ p3516) ∨ (¬ p3585)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2707) ∨ (¬ p2761) ∨ (p2842) ∨ (¬ p3516) ∨ (¬ p3577) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7236 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17964 (meaning t m 1988) (meaning t m 2027) (meaning t m 2707) (meaning t m 2761) (meaning t m 2842) (meaning t m 3516) (meaning t m 3577) (meaning t m 3585) source

theorem rule17965 (p1984 p2027 p2737 p2997 p3365 p3568 p3688 p3873 p4337 : Prop) (h : p2027 ∨ (¬ p4337) ∨ (¬ p3568) ∨ (¬ p3873) ∨ p2997 ∨ (¬ p3365) ∨ (¬ p3688) ∨ (¬ p1984) ∨ (¬ p2737)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2737) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial17965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory7237 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule17965 (meaning t m 1984) (meaning t m 2027) (meaning t m 2737) (meaning t m 2997) (meaning t m 3365) (meaning t m 3568) (meaning t m 3688) (meaning t m 3873) (meaning t m 4337) source

theorem rule17968 (p1984 p2027 p2287 p2295 p2737 p3365 p3549 p3873 p3953 : Prop) (h : (¬ p3953) ∨ (¬ p1984) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p3873) ∨ (¬ p2737) ∨ p2287 ∨ (¬ p3365) ∨ (¬ p3549)) : (¬ p1984) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3549) ∨ (¬ p3873) ∨ (¬ p3953) := by
  classical
  tauto

theorem initial17968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3953)) := by
  have source := ElevenTheory.theory7240 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule17968 (meaning t m 1984) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2737) (meaning t m 3365) (meaning t m 3549) (meaning t m 3873) (meaning t m 3953) source

theorem rule17971 (p1998 p2027 p3474 p3537 p3583 p3609 p4348 : Prop) (h : (¬ p3583) ∨ p3474 ∨ (¬ p4348) ∨ (¬ p3537) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p3474) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3609) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7243 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17971 (meaning t m 1998) (meaning t m 2027) (meaning t m 3474) (meaning t m 3537) (meaning t m 3583) (meaning t m 3609) (meaning t m 4348) source

theorem rule17972 (p1984 p2027 p2737 p2938 p3365 p3583 p3873 p4244 : Prop) (h : (¬ p1984) ∨ (¬ p3873) ∨ p2938 ∨ (¬ p3365) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4244)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2737) ∨ (p2938) ∨ (¬ p3365) ∨ (¬ p3583) ∨ (¬ p3873) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial17972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory7244 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule17972 (meaning t m 1984) (meaning t m 2027) (meaning t m 2737) (meaning t m 2938) (meaning t m 3365) (meaning t m 3583) (meaning t m 3873) (meaning t m 4244) source

theorem rule17973 (p1976 p2027 p2202 p2737 p3365 p3585 p3684 : Prop) (h : (¬ p3585) ∨ p2202 ∨ (¬ p1976) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3684)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial17973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7245 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule17973 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2737) (meaning t m 3365) (meaning t m 3585) (meaning t m 3684) source

theorem rule17974 (p2005 p2027 p2829 p3474 p3483 p3583 p4137 : Prop) (h : p2027 ∨ p3474 ∨ (¬ p4137) ∨ (¬ p2005) ∨ (¬ p3583) ∨ (¬ p3483) ∨ (¬ p2829)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2829) ∨ (p3474) ∨ (¬ p3483) ∨ (¬ p3583) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial17974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7246 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule17974 (meaning t m 2005) (meaning t m 2027) (meaning t m 2829) (meaning t m 3474) (meaning t m 3483) (meaning t m 3583) (meaning t m 4137) source

theorem rule17975 (p1998 p2027 p2406 p2409 p2589 p2881 p3389 p3569 : Prop) (h : (¬ p1998) ∨ p2409 ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3569) ∨ (¬ p2589) ∨ (¬ p3389)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2589) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial17975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory7247 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17975 (meaning t m 1998) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2589) (meaning t m 2881) (meaning t m 3389) (meaning t m 3569) source

theorem rule17978 (p2005 p2027 p2383 p2545 p2641 p3567 p3956 p4111 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p4111) ∨ (¬ p3567) ∨ (¬ p2641) ∨ (¬ p2383) ∨ (¬ p2005) ∨ (¬ p3956)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2383) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3956) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7250 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule17978 (meaning t m 2005) (meaning t m 2027) (meaning t m 2383) (meaning t m 2545) (meaning t m 2641) (meaning t m 3567) (meaning t m 3956) (meaning t m 4111) source

theorem rule17980 (p1998 p2027 p2114 p2406 p2589 p2911 p3389 p3541 : Prop) (h : p2114 ∨ (¬ p2589) ∨ (¬ p2406) ∨ (¬ p2911) ∨ (¬ p3541) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3389)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial17980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory7252 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule17980 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2406) (meaning t m 2589) (meaning t m 2911) (meaning t m 3389) (meaning t m 3541) source

theorem rule17982 (p1985 p2027 p2598 p2611 p2911 p3201 p3570 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p2911) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3570) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial17982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory7254 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17982 (meaning t m 1985) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 2911) (meaning t m 3201) (meaning t m 3570) source

theorem rule17983 (p1990 p2027 p2307 p2545 p2641 p3097 p3567 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p3567) ∨ p2545 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3567) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7255 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17983 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2545) (meaning t m 2641) (meaning t m 3097) (meaning t m 3567) (meaning t m 4111) source

theorem rule17985 (p1997 p2027 p2156 p2951 p2992 p3042 p4110 p4360 : Prop) (h : (¬ p4110) ∨ (¬ p1997) ∨ (¬ p4360) ∨ (¬ p2992) ∨ p3042 ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2951)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (p3042) ∨ (¬ p4110) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7257 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6)
  exact rule17985 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2951) (meaning t m 2992) (meaning t m 3042) (meaning t m 4110) (meaning t m 4360) source

theorem rule17986 (p1985 p2027 p2246 p2264 p2545 p2807 p3570 p4111 : Prop) (h : (¬ p2264) ∨ (¬ p4111) ∨ (¬ p3570) ∨ p2545 ∨ (¬ p1985) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p2807)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (p2545) ∨ (¬ p2807) ∨ (¬ p3570) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7258 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17986 (meaning t m 1985) (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2545) (meaning t m 2807) (meaning t m 3570) (meaning t m 4111) source

theorem rule17988 (p1978 p2027 p2274 p2765 p3073 p3549 p3697 p3857 p4317 : Prop) (h : (¬ p1978) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p3697) ∨ (¬ p3549) ∨ p2765 ∨ (¬ p4317) ∨ (¬ p2274)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3073) ∨ (¬ p3549) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial17988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory7260 t (m.theta 0 5) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule17988 (meaning t m 1978) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 3073) (meaning t m 3549) (meaning t m 3697) (meaning t m 3857) (meaning t m 4317) source

theorem rule17989 (p1987 p2027 p2331 p2764 p3292 p4195 p5284 : Prop) (h : p2764 ∨ (¬ p2331) ∨ (¬ p4195) ∨ (¬ p3292) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p5284)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2331) ∨ (p2764) ∨ (¬ p3292) ∨ (¬ p4195) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial17989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7261 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 9 10)
  exact rule17989 (meaning t m 1987) (meaning t m 2027) (meaning t m 2331) (meaning t m 2764) (meaning t m 3292) (meaning t m 4195) (meaning t m 5284) source

theorem rule17990 (p1988 p2027 p2598 p2611 p2850 p2982 p3680 : Prop) (h : (¬ p2598) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2850) ∨ p2611 ∨ (¬ p2982) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial17990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory7262 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule17990 (meaning t m 1988) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 2982) (meaning t m 3680) source

theorem rule17993 (p1998 p2027 p2363 p2611 p2774 p2819 p4348 : Prop) (h : p2611 ∨ (¬ p2363) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2774) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7265 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17993 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2611) (meaning t m 2774) (meaning t m 2819) (meaning t m 4348) source

theorem rule17994 (p1998 p2027 p2177 p2202 p2307 p2440 p2578 p3016 : Prop) (h : (¬ p1998) ∨ (¬ p3016) ∨ p2202 ∨ (¬ p2578) ∨ (¬ p2307) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2440)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2578) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial17994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory7266 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17994 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2307) (meaning t m 2440) (meaning t m 2578) (meaning t m 3016) source

theorem rule17996 (p1986 p3498 p3584 p4595 : Prop) (h : (¬ p1986) ∨ (¬ p3584) ∨ p3498 ∨ p4595) : (¬ p1986) ∨ (p3498) ∨ (¬ p3584) ∨ (p4595) := by
  classical
  tauto

theorem initial17996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 4595) := by
  have source := ElevenTheory.theory7268 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule17996 (meaning t m 1986) (meaning t m 3498) (meaning t m 3584) (meaning t m 4595) source

theorem rule17999 (p1998 p2027 p2230 p2611 p2911 p3201 p3362 p3684 : Prop) (h : (¬ p2911) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3684) ∨ p2611 ∨ (¬ p2230) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (p2611) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial17999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7271 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule17999 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2611) (meaning t m 2911) (meaning t m 3201) (meaning t m 3362) (meaning t m 3684) source

theorem rule18000 (p1975 p2027 p2192 p2299 p2341 p2873 p3646 p4988 : Prop) (h : (¬ p4988) ∨ (¬ p2341) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2192) ∨ p2873 ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (p2873) ∨ (¬ p3646) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial18000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory7272 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18000 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2299) (meaning t m 2341) (meaning t m 2873) (meaning t m 3646) (meaning t m 4988) source

theorem rule18002 (p1987 p2027 p2462 p2946 p3414 p3947 p4315 : Prop) (h : (¬ p3947) ∨ p2027 ∨ (¬ p2946) ∨ p2462 ∨ (¬ p1987) ∨ (¬ p4315) ∨ (¬ p3414)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7274 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule18002 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2946) (meaning t m 3414) (meaning t m 3947) (meaning t m 4315) source

theorem rule18006 (p1984 p2027 p2284 p2938 p3555 p4173 p4320 : Prop) (h : (¬ p1984) ∨ (¬ p2284) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4173) ∨ p2938 ∨ (¬ p4320)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2284) ∨ (p2938) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial18006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory7278 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18006 (meaning t m 1984) (meaning t m 2027) (meaning t m 2284) (meaning t m 2938) (meaning t m 3555) (meaning t m 4173) (meaning t m 4320) source

theorem rule18007 (p1984 p2027 p2668 p2997 p3568 p3591 p3923 : Prop) (h : (¬ p3591) ∨ (¬ p1984) ∨ (¬ p3923) ∨ p2027 ∨ p2997 ∨ (¬ p2668) ∨ (¬ p3568)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial18007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory7279 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18007 (meaning t m 1984) (meaning t m 2027) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3591) (meaning t m 3923) source

theorem rule18009 (p1984 p2027 p2247 p2462 p3568 p4107 p4154 : Prop) (h : (¬ p4154) ∨ (¬ p1984) ∨ (¬ p3568) ∨ (¬ p2247) ∨ p2027 ∨ p2462 ∨ (¬ p4107)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2462) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial18009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory7281 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9)
  exact rule18009 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2462) (meaning t m 3568) (meaning t m 4107) (meaning t m 4154) source

theorem rule18011 (p1990 p2027 p2156 p2688 p2992 p3115 p4032 : Prop) (h : (¬ p2156) ∨ (¬ p3115) ∨ (¬ p2992) ∨ (¬ p4032) ∨ (¬ p1990) ∨ p2027 ∨ p2688) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial18011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory7283 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule18011 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2688) (meaning t m 2992) (meaning t m 3115) (meaning t m 4032) source

theorem rule18013 (p1990 p2027 p2563 p2766 p3570 p4235 p4348 : Prop) (h : (¬ p4235) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3570) ∨ p2766 ∨ (¬ p4348)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7285 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18013 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2766) (meaning t m 3570) (meaning t m 4235) (meaning t m 4348) source

theorem rule18014 (p1985 p2027 p2656 p2688 p2727 p2911 p3389 p3570 : Prop) (h : (¬ p1985) ∨ p2688 ∨ (¬ p2911) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial18014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory7286 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule18014 (meaning t m 1985) (meaning t m 2027) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2911) (meaning t m 3389) (meaning t m 3570) source

theorem rule18015 (p2011 p2088 p4080 p4450 : Prop) (h : p4080 ∨ p4450 ∨ (¬ p2088) ∨ (¬ p2011)) : (¬ p2011) ∨ (¬ p2088) ∨ (p4080) ∨ (p4450) := by
  classical
  tauto

theorem initial18015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 4080) ∨ (meaning t m 4450) := by
  have source := ElevenTheory.theory7287 t (m.theta 0 8) (m.theta 5 9) (m.theta 8 9)
  exact rule18015 (meaning t m 2011) (meaning t m 2088) (meaning t m 4080) (meaning t m 4450) source

theorem rule18017 (p1990 p2148 p3051 p3097 p4559 : Prop) (h : p4559 ∨ p2148 ∨ (¬ p3051) ∨ (¬ p1990) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2148) ∨ (¬ p3051) ∨ (¬ p3097) ∨ (p4559) := by
  classical
  tauto

theorem initial18017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 4559) := by
  have source := ElevenTheory.theory7289 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule18017 (meaning t m 1990) (meaning t m 2148) (meaning t m 3051) (meaning t m 3097) (meaning t m 4559) source

theorem rule18023 (p1998 p2027 p2233 p2881 p3276 p3355 p4322 p4402 : Prop) (h : (¬ p4322) ∨ p2233 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p4402) ∨ (¬ p3355) ∨ (¬ p3276)) : (¬ p1998) ∨ (p2027) ∨ (p2233) ∨ (¬ p2881) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4322) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial18023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory7295 t (m.theta 0 4) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 9 10)
  exact rule18023 (meaning t m 1998) (meaning t m 2027) (meaning t m 2233) (meaning t m 2881) (meaning t m 3276) (meaning t m 3355) (meaning t m 4322) (meaning t m 4402) source

theorem rule18024 (p1988 p2027 p2417 p2753 p2761 p2842 p3471 p3585 p3658 : Prop) (h : (¬ p2753) ∨ (¬ p3471) ∨ (¬ p1988) ∨ p2842 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2761) ∨ (¬ p2417) ∨ (¬ p3658)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (p2842) ∨ (¬ p3471) ∨ (¬ p3585) ∨ (¬ p3658) := by
  classical
  tauto

theorem initial18024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) := by
  have source := ElevenTheory.theory7296 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18024 (meaning t m 1988) (meaning t m 2027) (meaning t m 2417) (meaning t m 2753) (meaning t m 2761) (meaning t m 2842) (meaning t m 3471) (meaning t m 3585) (meaning t m 3658) source

theorem rule18025 (p1990 p2027 p2563 p2997 p3319 p3822 p3918 p4033 p4948 : Prop) (h : (¬ p3918) ∨ p2997 ∨ (¬ p4948) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p3319) ∨ (¬ p4033) ∨ (¬ p2563) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2997) ∨ (¬ p3319) ∨ (¬ p3822) ∨ (¬ p3918) ∨ (¬ p4033) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial18025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7297 t (m.theta 1 6) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule18025 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2997) (meaning t m 3319) (meaning t m 3822) (meaning t m 3918) (meaning t m 4033) (meaning t m 4948) source

theorem rule18031 (p1998 p2027 p2177 p2553 p2598 p2611 p3422 : Prop) (h : (¬ p2598) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2553) ∨ p2611 ∨ (¬ p3422) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial18031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory7303 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18031 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2598) (meaning t m 2611) (meaning t m 3422) source

theorem rule18032 (p1981 p2027 p2352 p2598 p2611 p3483 p4137 p4375 : Prop) (h : p2611 ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p4137) ∨ (¬ p3483) ∨ (¬ p2598) ∨ (¬ p4375)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3483) ∨ (¬ p4137) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial18032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory7304 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule18032 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 2611) (meaning t m 3483) (meaning t m 4137) (meaning t m 4375) source

theorem rule18033 (p1985 p2027 p2132 p2284 p2545 p2780 p2870 p3413 p4428 : Prop) (h : (¬ p2132) ∨ (¬ p1985) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2870) ∨ p2545 ∨ (¬ p3413) ∨ (¬ p4428) ∨ (¬ p2284)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2780) ∨ (¬ p2870) ∨ (¬ p3413) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial18033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory7305 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18033 (meaning t m 1985) (meaning t m 2027) (meaning t m 2132) (meaning t m 2284) (meaning t m 2545) (meaning t m 2780) (meaning t m 2870) (meaning t m 3413) (meaning t m 4428) source

theorem rule18037 (p2018 p2027 p2098 p2780 p2829 p2842 p3585 : Prop) (h : (¬ p2018) ∨ p2842 ∨ (¬ p2098) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2780) ∨ (¬ p2829)) : (¬ p2018) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial18037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7309 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 8)
  exact rule18037 (meaning t m 2018) (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule18041 (p1986 p2027 p2299 p2588 p2766 p3584 p4348 : Prop) (h : (¬ p4348) ∨ p2766 ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3584)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (p2766) ∨ (¬ p3584) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7313 t (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18041 (meaning t m 1986) (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 2766) (meaning t m 3584) (meaning t m 4348) source

theorem rule18044 (p1985 p2027 p2156 p2870 p3043 p3758 p4032 : Prop) (h : p3043 ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4032) ∨ (¬ p2156)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2870) ∨ (p3043) ∨ (¬ p3758) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial18044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2870)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory7316 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule18044 (meaning t m 1985) (meaning t m 2027) (meaning t m 2156) (meaning t m 2870) (meaning t m 3043) (meaning t m 3758) (meaning t m 4032) source

theorem rule18045 (p1994 p2027 p2114 p2493 p3379 p3574 p3954 : Prop) (h : (¬ p3954) ∨ p2114 ∨ (¬ p3379) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3574) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7317 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule18045 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2493) (meaning t m 3379) (meaning t m 3574) (meaning t m 3954) source

theorem rule18048 (p2590 p3584 p3684 : Prop) (h : (¬ p2590) ∨ (¬ p3684) ∨ p3584) : (¬ p2590) ∨ (p3584) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial18048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2590)) ∨ (meaning t m 3584) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7320 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule18048 (meaning t m 2590) (meaning t m 3584) (meaning t m 3684) source

theorem rule18049 (p1981 p2027 p2611 p2696 p3005 p3256 p4347 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p4347) ∨ (¬ p3256) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7321 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18049 (meaning t m 1981) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 4347) source

theorem rule18050 (p1982 p2027 p2363 p2611 p3166 p4009 p4117 p5580 : Prop) (h : (¬ p3166) ∨ p2027 ∨ p2611 ∨ (¬ p5580) ∨ (¬ p4117) ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p4009)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p4117) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7322 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18050 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2611) (meaning t m 3166) (meaning t m 4009) (meaning t m 4117) (meaning t m 5580) source

theorem rule18051 (p1998 p2027 p2264 p2323 p2331 p2685 p4195 : Prop) (h : (¬ p2331) ∨ (¬ p2685) ∨ p2323 ∨ (¬ p4195) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2264)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2685) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial18051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory7323 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule18051 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2331) (meaning t m 2685) (meaning t m 4195) source

theorem rule18052 (p2017 p2027 p2274 p2284 p2688 p2992 p3791 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p2017) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p3791) ∨ (¬ p2274)) : (¬ p2017) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3791) := by
  classical
  tauto

theorem initial18052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3791)) := by
  have source := ElevenTheory.theory7324 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10)
  exact rule18052 (meaning t m 2017) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2688) (meaning t m 2992) (meaning t m 3791) source

theorem rule18053 (p1993 p2027 p2247 p2688 p3073 p3449 p4118 : Prop) (h : (¬ p1993) ∨ p2688 ∨ (¬ p4118) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2247) ∨ (¬ p3073)) : (¬ p1993) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial18053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7325 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule18053 (meaning t m 1993) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3073) (meaning t m 3449) (meaning t m 4118) source

theorem rule18055 (p1981 p2027 p2187 p2323 p2331 p4228 p4393 : Prop) (h : p2323 ∨ (¬ p2187) ∨ p2027 ∨ (¬ p4228) ∨ (¬ p2331) ∨ (¬ p1981) ∨ (¬ p4393)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p4228) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial18055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory7327 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 8)
  exact rule18055 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2323) (meaning t m 2331) (meaning t m 4228) (meaning t m 4393) source

theorem rule18057 (p1995 p2027 p2765 p2982 p3379 p3834 p4110 p4388 : Prop) (h : (¬ p3834) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4388) ∨ (¬ p1995) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2982)) : (¬ p1995) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4110) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial18057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory7329 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule18057 (meaning t m 1995) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 3379) (meaning t m 3834) (meaning t m 4110) (meaning t m 4388) source

theorem rule18060 (p2020 p2027 p2331 p2611 p3005 p3979 p4117 p4195 p4417 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p2331) ∨ (¬ p4417) ∨ (¬ p2020) ∨ (¬ p3005) ∨ (¬ p3979)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2331) ∨ (p2611) ∨ (¬ p3005) ∨ (¬ p3979) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial18060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory7332 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10)
  exact rule18060 (meaning t m 2020) (meaning t m 2027) (meaning t m 2331) (meaning t m 2611) (meaning t m 3005) (meaning t m 3979) (meaning t m 4117) (meaning t m 4195) (meaning t m 4417) source

theorem rule18061 (p1975 p2027 p2114 p2819 p3830 p3917 p3954 p3955 p5152 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p3955) ∨ (¬ p3954) ∨ (¬ p3917) ∨ (¬ p1975) ∨ (¬ p2819) ∨ (¬ p3830) ∨ (¬ p5152)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2819) ∨ (¬ p3830) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p3955) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial18061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory7333 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule18061 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2819) (meaning t m 3830) (meaning t m 3917) (meaning t m 3954) (meaning t m 3955) (meaning t m 5152) source

theorem rule18063 (p1995 p2027 p3146 p3379 p3578 p3860 p4261 : Prop) (h : (¬ p3379) ∨ (¬ p1995) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3860) ∨ p3578) : (¬ p1995) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (p3578) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial18063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory7335 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18063 (meaning t m 1995) (meaning t m 2027) (meaning t m 3146) (meaning t m 3379) (meaning t m 3578) (meaning t m 3860) (meaning t m 4261) source

theorem rule18065 (p1982 p2027 p2114 p2363 p3063 p3093 p3954 : Prop) (h : (¬ p3063) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p1982) ∨ p2114 ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7337 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18065 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3954) source

theorem rule18070 (p1990 p2027 p2247 p2688 p3093 p3319 p3744 : Prop) (h : p2688 ∨ (¬ p1990) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3319) ∨ (¬ p3093)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial18070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory7342 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 5 6) (m.theta 6 9)
  exact rule18070 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3093) (meaning t m 3319) (meaning t m 3744) source

theorem rule18072 (p2000 p2027 p2766 p3904 p3979 p4120 p4347 p5568 : Prop) (h : (¬ p2000) ∨ (¬ p4347) ∨ (¬ p4120) ∨ p2766 ∨ p2027 ∨ (¬ p3979) ∨ (¬ p3904) ∨ (¬ p5568)) : (¬ p2000) ∨ (p2027) ∨ (p2766) ∨ (¬ p3904) ∨ (¬ p3979) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory7344 t (m.theta 0 4) (m.theta 0 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18072 (meaning t m 2000) (meaning t m 2027) (meaning t m 2766) (meaning t m 3904) (meaning t m 3979) (meaning t m 4120) (meaning t m 4347) (meaning t m 5568) source

theorem rule18073 (p2020 p2027 p2114 p3399 p3527 p3941 p3954 : Prop) (h : p2114 ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p2020) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7345 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8) (m.theta 8 10)
  exact rule18073 (meaning t m 2020) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3527) (meaning t m 3941) (meaning t m 3954) source

theorem rule18076 (p1979 p2027 p2982 p3136 p3578 p3880 p4035 p4040 : Prop) (h : p3578 ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p2982) ∨ (¬ p4040) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2982) ∨ (¬ p3136) ∨ (p3578) ∨ (¬ p3880) ∨ (¬ p4035) ∨ (¬ p4040) := by
  classical
  tauto

theorem initial18076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3136)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4040)) := by
  have source := ElevenTheory.theory7348 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule18076 (meaning t m 1979) (meaning t m 2027) (meaning t m 2982) (meaning t m 3136) (meaning t m 3578) (meaning t m 3880) (meaning t m 4035) (meaning t m 4040) source

theorem rule18079 (p2015 p2027 p2169 p2363 p2534 p3868 p4105 p4186 p4442 : Prop) (h : (¬ p2015) ∨ (¬ p4186) ∨ (¬ p2534) ∨ (¬ p3868) ∨ (¬ p4105) ∨ (¬ p4442) ∨ (¬ p2363) ∨ p2027 ∨ p2169) : (¬ p2015) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3868) ∨ (¬ p4105) ∨ (¬ p4186) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial18079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory7351 t (m.theta 1 6) (m.theta 1 7) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9)
  exact rule18079 (meaning t m 2015) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 3868) (meaning t m 4105) (meaning t m 4186) (meaning t m 4442) source

theorem rule18081 (p2007 p2027 p2611 p2696 p3005 p4009 p4286 : Prop) (h : (¬ p4009) ∨ (¬ p3005) ∨ p2611 ∨ p2027 ∨ (¬ p2007) ∨ (¬ p2696) ∨ (¬ p4286)) : (¬ p2007) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial18081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory7353 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10)
  exact rule18081 (meaning t m 2007) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3005) (meaning t m 4009) (meaning t m 4286) source

theorem rule18082 (p1982 p2027 p2528 p2611 p2630 p2696 p3083 : Prop) (h : (¬ p1982) ∨ p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p2528) ∨ (¬ p2630)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial18082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory7354 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule18082 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2611) (meaning t m 2630) (meaning t m 2696) (meaning t m 3083) source

theorem rule18085 (p1994 p2027 p2247 p2493 p2688 p3379 p3574 : Prop) (h : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2493) ∨ (p2688) ∨ (¬ p3379) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial18085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory7357 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule18085 (meaning t m 1994) (meaning t m 2027) (meaning t m 2247) (meaning t m 2493) (meaning t m 2688) (meaning t m 3379) (meaning t m 3574) source

theorem rule18086 (p2005 p2027 p2459 p2481 p2633 p3016 p3857 p4256 : Prop) (h : (¬ p2481) ∨ (¬ p2459) ∨ (¬ p4256) ∨ (¬ p3857) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2005) ∨ p2633) : (¬ p2005) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2481) ∨ (p2633) ∨ (¬ p3016) ∨ (¬ p3857) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2481)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7358 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18086 (meaning t m 2005) (meaning t m 2027) (meaning t m 2459) (meaning t m 2481) (meaning t m 2633) (meaning t m 3016) (meaning t m 3857) (meaning t m 4256) source

theorem rule18088 (p1994 p2027 p2114 p2922 p3379 p3742 p3954 : Prop) (h : p2114 ∨ (¬ p3954) ∨ (¬ p1994) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3379)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3742) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7360 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule18088 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2922) (meaning t m 3379) (meaning t m 3742) (meaning t m 3954) source

theorem rule18089 (p1997 p2027 p2114 p2241 p2542 p2727 p3954 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p2241) ∨ (¬ p1997) ∨ (¬ p3954)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7361 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5)
  exact rule18089 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2542) (meaning t m 2727) (meaning t m 3954) source

theorem rule18090 (p2005 p2997 p3956 p4405 : Prop) (h : (¬ p3956) ∨ p2997 ∨ (¬ p2005) ∨ p4405) : (¬ p2005) ∨ (p2997) ∨ (¬ p3956) ∨ (p4405) := by
  classical
  tauto

theorem initial18090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3956)) ∨ (meaning t m 4405) := by
  have source := ElevenTheory.theory7362 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18090 (meaning t m 2005) (meaning t m 2997) (meaning t m 3956) (meaning t m 4405) source

theorem rule18091 (p1997 p2027 p2542 p2630 p2688 p3189 p3877 : Prop) (h : p2688 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p1997) ∨ (¬ p3189) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p3189) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial18091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory7363 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule18091 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2630) (meaning t m 2688) (meaning t m 3189) (meaning t m 3877) source

theorem rule18092 (p1990 p2027 p2247 p2688 p3093 p3097 p3309 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial18092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory7364 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule18092 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3093) (meaning t m 3097) (meaning t m 3309) source

theorem rule18093 (p1985 p2901 p3042 p5062 : Prop) (h : p5062 ∨ p3042 ∨ (¬ p2901) ∨ (¬ p1985)) : (¬ p1985) ∨ (¬ p2901) ∨ (p3042) ∨ (p5062) := by
  classical
  tauto

theorem initial18093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 3042) ∨ (meaning t m 5062) := by
  have source := ElevenTheory.theory7365 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 7)
  exact rule18093 (meaning t m 1985) (meaning t m 2901) (meaning t m 3042) (meaning t m 5062) source

theorem rule18094 (p1975 p2027 p2295 p2611 p2651 p2797 p2810 p4117 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p4117) ∨ (¬ p1975) ∨ (¬ p2810) ∨ (¬ p2651) ∨ (¬ p2295) ∨ (¬ p2797)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial18094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory7366 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule18094 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2651) (meaning t m 2797) (meaning t m 2810) (meaning t m 4117) source

theorem rule18096 (p1998 p2027 p2264 p2323 p2651 p2685 p2810 : Prop) (h : p2323 ∨ (¬ p2685) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p2264) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial18096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory7368 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule18096 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2651) (meaning t m 2685) (meaning t m 2810) source

theorem rule18097 (p1996 p2027 p2323 p2685 p3286 p3506 p5387 p5453 : Prop) (h : p2323 ∨ (¬ p1996) ∨ (¬ p5387) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p3286) ∨ (¬ p5453) ∨ (¬ p3506)) : (¬ p1996) ∨ (p2027) ∨ (p2323) ∨ (¬ p2685) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p5387) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial18097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory7369 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 9) (m.theta 3 7) (m.theta 3 9) (m.theta 9 10)
  exact rule18097 (meaning t m 1996) (meaning t m 2027) (meaning t m 2323) (meaning t m 2685) (meaning t m 3286) (meaning t m 3506) (meaning t m 5387) (meaning t m 5453) source

theorem rule18098 (p1979 p2027 p3128 p3136 p3461 p4035 p5284 : Prop) (h : (¬ p3461) ∨ p3128 ∨ (¬ p1979) ∨ (¬ p3136) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p5284)) : (¬ p1979) ∨ (p2027) ∨ (p3128) ∨ (¬ p3136) ∨ (¬ p3461) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7370 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule18098 (meaning t m 1979) (meaning t m 2027) (meaning t m 3128) (meaning t m 3136) (meaning t m 3461) (meaning t m 4035) (meaning t m 5284) source

theorem rule18099 (p2020 p2027 p2611 p2651 p2810 p3005 p4009 p4117 : Prop) (h : (¬ p2651) ∨ p2611 ∨ (¬ p2810) ∨ (¬ p4009) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p2020)) : (¬ p2020) ∨ (p2027) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial18099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory7371 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 10)
  exact rule18099 (meaning t m 2020) (meaning t m 2027) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 3005) (meaning t m 4009) (meaning t m 4117) source

theorem rule18100 (p1981 p2027 p2611 p2651 p2668 p2797 p2810 p4117 : Prop) (h : (¬ p2668) ∨ p2611 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial18100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory7372 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule18100 (meaning t m 1981) (meaning t m 2027) (meaning t m 2611) (meaning t m 2651) (meaning t m 2668) (meaning t m 2797) (meaning t m 2810) (meaning t m 4117) source

theorem rule18103 (p1981 p2027 p2352 p2611 p2651 p2797 p2810 p3984 p4117 : Prop) (h : p2611 ∨ (¬ p1981) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p2352) ∨ (¬ p2810) ∨ (¬ p2797) ∨ (¬ p3984)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial18103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory7375 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule18103 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2611) (meaning t m 2651) (meaning t m 2797) (meaning t m 2810) (meaning t m 3984) (meaning t m 4117) source

theorem rule18104 (p1980 p2027 p2114 p2797 p3707 p4035 p5284 p5333 : Prop) (h : (¬ p4035) ∨ p2114 ∨ (¬ p5284) ∨ (¬ p1980) ∨ (¬ p3707) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p5333)) : (¬ p1980) ∨ (p2027) ∨ (p2114) ∨ (¬ p2797) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p5284) ∨ (¬ p5333) := by
  classical
  tauto

theorem initial18104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5333)) := by
  have source := ElevenTheory.theory7376 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 9 10)
  exact rule18104 (meaning t m 1980) (meaning t m 2027) (meaning t m 2114) (meaning t m 2797) (meaning t m 3707) (meaning t m 4035) (meaning t m 5284) (meaning t m 5333) source

theorem rule18108 (p1998 p2027 p2132 p2177 p2274 p2611 p2860 : Prop) (h : (¬ p2274) ∨ (¬ p1998) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2177) ∨ p2611) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (p2611) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial18108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory7380 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18108 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2177) (meaning t m 2274) (meaning t m 2611) (meaning t m 2860) source

theorem rule18109 (p2001 p2027 p2132 p2373 p2611 p2870 p4235 : Prop) (h : (¬ p2001) ∨ p2611 ∨ p2027 ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p4235) ∨ (¬ p2132)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2373) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7381 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule18109 (meaning t m 2001) (meaning t m 2027) (meaning t m 2132) (meaning t m 2373) (meaning t m 2611) (meaning t m 2870) (meaning t m 4235) source

theorem rule18111 (p1983 p2027 p2598 p2611 p3276 p3333 p4381 : Prop) (h : (¬ p2598) ∨ p2611 ∨ p2027 ∨ (¬ p4381) ∨ (¬ p1983) ∨ (¬ p3276) ∨ (¬ p3333)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7383 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule18111 (meaning t m 1983) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 3276) (meaning t m 3333) (meaning t m 4381) source

theorem rule18112 (p1979 p2027 p2252 p2299 p2633 p2963 p2992 p3097 p3745 : Prop) (h : (¬ p3097) ∨ (¬ p2299) ∨ p2027 ∨ p2633 ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p1979) ∨ (¬ p2252) ∨ (¬ p2992)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3097) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial18112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory7384 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18112 (meaning t m 1979) (meaning t m 2027) (meaning t m 2252) (meaning t m 2299) (meaning t m 2633) (meaning t m 2963) (meaning t m 2992) (meaning t m 3097) (meaning t m 3745) source

theorem rule18113 (p1987 p2027 p2252 p2963 p2992 p2997 p3568 p4315 : Prop) (h : (¬ p2992) ∨ (¬ p2963) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p3568) ∨ p2997 ∨ (¬ p4315) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7385 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule18113 (meaning t m 1987) (meaning t m 2027) (meaning t m 2252) (meaning t m 2963) (meaning t m 2992) (meaning t m 2997) (meaning t m 3568) (meaning t m 4315) source

theorem rule18115 (p1991 p2027 p2169 p2363 p2952 p3692 p3952 p3988 : Prop) (h : (¬ p2952) ∨ (¬ p1991) ∨ (¬ p2363) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3988) ∨ p2169) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial18115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory7387 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18115 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2952) (meaning t m 3692) (meaning t m 3952) (meaning t m 3988) source

theorem rule18118 (p1997 p2027 p2406 p2437 p2928 p3498 p4256 : Prop) (h : (¬ p1997) ∨ (¬ p2928) ∨ p3498 ∨ (¬ p2406) ∨ (¬ p2437) ∨ (¬ p4256) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (p3498) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7390 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule18118 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2437) (meaning t m 2928) (meaning t m 3498) (meaning t m 4256) source

theorem rule18121 (p1987 p2027 p2143 p2737 p2951 p2997 p3097 p3583 p3952 : Prop) (h : (¬ p2951) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p3583) ∨ (¬ p2737) ∨ (¬ p1987) ∨ p2997 ∨ (¬ p3097)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2737) ∨ (¬ p2951) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial18121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2951)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory7393 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule18121 (meaning t m 1987) (meaning t m 2027) (meaning t m 2143) (meaning t m 2737) (meaning t m 2951) (meaning t m 2997) (meaning t m 3097) (meaning t m 3583) (meaning t m 3952) source

theorem rule18125 (p1976 p2027 p2780 p3128 p3737 p3744 p4329 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4329) ∨ (¬ p2780) ∨ p3128 ∨ (¬ p3737) ∨ (¬ p3744)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2780) ∨ (p3128) ∨ (¬ p3737) ∨ (¬ p3744) ∨ (¬ p4329) := by
  classical
  tauto

theorem initial18125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4329)) := by
  have source := ElevenTheory.theory7397 t (m.theta 0 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 9)
  exact rule18125 (meaning t m 1976) (meaning t m 2027) (meaning t m 2780) (meaning t m 3128) (meaning t m 3737) (meaning t m 3744) (meaning t m 4329) source

theorem rule18126 (p1983 p2027 p2417 p2699 p3399 p4075 p5503 : Prop) (h : (¬ p3399) ∨ p2699 ∨ p2027 ∨ (¬ p5503) ∨ (¬ p1983) ∨ (¬ p2417) ∨ (¬ p4075)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial18126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory7398 t (m.theta 0 1) (m.theta 1 7) (m.theta 4 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18126 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2699) (meaning t m 3399) (meaning t m 4075) (meaning t m 5503) source

theorem rule18127 (p1989 p2027 p2462 p3486 p3791 p4107 p5660 : Prop) (h : p2462 ∨ (¬ p1989) ∨ (¬ p4107) ∨ (¬ p3486) ∨ (¬ p3791) ∨ (¬ p5660) ∨ p2027) : (¬ p1989) ∨ (p2027) ∨ (p2462) ∨ (¬ p3486) ∨ (¬ p3791) ∨ (¬ p4107) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial18127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory7399 t (m.theta 1 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18127 (meaning t m 1989) (meaning t m 2027) (meaning t m 2462) (meaning t m 3486) (meaning t m 3791) (meaning t m 4107) (meaning t m 5660) source

theorem rule18128 (p1991 p2027 p2299 p2963 p3568 p3982 p5558 : Prop) (h : (¬ p2963) ∨ (¬ p1991) ∨ p3982 ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p5558)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial18128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory7400 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule18128 (meaning t m 1991) (meaning t m 2027) (meaning t m 2299) (meaning t m 2963) (meaning t m 3568) (meaning t m 3982) (meaning t m 5558) source

theorem rule18129 (p1987 p2027 p2545 p2737 p3083 p3585 p3874 : Prop) (h : p2027 ∨ (¬ p3874) ∨ (¬ p3083) ∨ p2545 ∨ (¬ p3585) ∨ (¬ p2737) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2737) ∨ (¬ p3083) ∨ (¬ p3585) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial18129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory7401 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8)
  exact rule18129 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2737) (meaning t m 3083) (meaning t m 3585) (meaning t m 3874) source

theorem rule18131 (p1988 p2027 p2528 p2598 p2611 p3266 p3641 : Prop) (h : (¬ p3641) ∨ (¬ p2598) ∨ (¬ p3266) ∨ p2611 ∨ (¬ p2528) ∨ p2027 ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3266) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial18131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory7403 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18131 (meaning t m 1988) (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2611) (meaning t m 3266) (meaning t m 3641) source

theorem rule18134 (p1986 p2027 p2406 p2509 p2545 p3083 p3684 : Prop) (h : (¬ p2509) ∨ (¬ p3684) ∨ (¬ p2406) ∨ (¬ p3083) ∨ p2545 ∨ p2027 ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (p2545) ∨ (¬ p3083) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial18134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7406 t (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule18134 (meaning t m 1986) (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2545) (meaning t m 3083) (meaning t m 3684) source

theorem rule18136 (p2002 p2027 p2476 p2545 p2829 p3083 p3363 p3585 : Prop) (h : (¬ p2002) ∨ p2027 ∨ p2545 ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3585)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2476) ∨ (p2545) ∨ (¬ p2829) ∨ (¬ p3083) ∨ (¬ p3363) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial18136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7408 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8)
  exact rule18136 (meaning t m 2002) (meaning t m 2027) (meaning t m 2476) (meaning t m 2545) (meaning t m 2829) (meaning t m 3083) (meaning t m 3363) (meaning t m 3585) source

theorem rule18137 (p2005 p2027 p2493 p3193 p3343 p3498 p4256 : Prop) (h : (¬ p2005) ∨ (¬ p3343) ∨ (¬ p3193) ∨ (¬ p2493) ∨ p2027 ∨ p3498 ∨ (¬ p4256)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (p3498) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7409 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 4 9)
  exact rule18137 (meaning t m 2005) (meaning t m 2027) (meaning t m 2493) (meaning t m 3193) (meaning t m 3343) (meaning t m 3498) (meaning t m 4256) source

theorem rule18139 (p1987 p2027 p2696 p2764 p2780 p4037 p4191 p4337 : Prop) (h : (¬ p1987) ∨ (¬ p2696) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p4037) ∨ (¬ p4337) ∨ (¬ p2780) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (p2764) ∨ (¬ p2780) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial18139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory7411 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule18139 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2764) (meaning t m 2780) (meaning t m 4037) (meaning t m 4191) (meaning t m 4337) source

theorem rule18144 (p1998 p2355 p2449 p4666 : Prop) (h : (¬ p1998) ∨ p2355 ∨ p4666 ∨ (¬ p2449)) : (¬ p1998) ∨ (p2355) ∨ (¬ p2449) ∨ (p4666) := by
  classical
  tauto

theorem initial18144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 4666) := by
  have source := ElevenTheory.theory7416 t (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18144 (meaning t m 1998) (meaning t m 2355) (meaning t m 2449) (meaning t m 4666) source

theorem rule18146 (p1989 p2027 p2156 p2388 p3156 p4120 p4173 : Prop) (h : p2027 ∨ p2388 ∨ (¬ p4173) ∨ (¬ p2156) ∨ (¬ p1989) ∨ (¬ p3156) ∨ (¬ p4120)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2156) ∨ (p2388) ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial18146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7418 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule18146 (meaning t m 1989) (meaning t m 2027) (meaning t m 2156) (meaning t m 2388) (meaning t m 3156) (meaning t m 4120) (meaning t m 4173) source

theorem rule18147 (p1988 p2027 p2699 p2928 p3222 p3276 p3389 p4079 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3276) ∨ (¬ p2928) ∨ p2699 ∨ (¬ p4079) ∨ (¬ p3222)) : (¬ p1988) ∨ (p2027) ∨ (p2699) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3389) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial18147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory7419 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 9 10)
  exact rule18147 (meaning t m 1988) (meaning t m 2027) (meaning t m 2699) (meaning t m 2928) (meaning t m 3222) (meaning t m 3276) (meaning t m 3389) (meaning t m 4079) source

theorem rule18148 (p1982 p2027 p2233 p2518 p2528 p2928 p3389 : Prop) (h : p2027 ∨ (¬ p2528) ∨ (¬ p1982) ∨ (¬ p2928) ∨ (¬ p3389) ∨ p2233 ∨ (¬ p2518)) : (¬ p1982) ∨ (p2027) ∨ (p2233) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial18148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory7420 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule18148 (meaning t m 1982) (meaning t m 2027) (meaning t m 2233) (meaning t m 2518) (meaning t m 2528) (meaning t m 2928) (meaning t m 3389) source

theorem rule18151 (p1989 p2027 p2156 p2355 p2951 p3136 p3572 p4173 : Prop) (h : (¬ p4173) ∨ p2027 ∨ (¬ p1989) ∨ (¬ p2156) ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p3572) ∨ p2355) : (¬ p1989) ∨ (p2027) ∨ (¬ p2156) ∨ (p2355) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial18151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7423 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule18151 (meaning t m 1989) (meaning t m 2027) (meaning t m 2156) (meaning t m 2355) (meaning t m 2951) (meaning t m 3136) (meaning t m 3572) (meaning t m 4173) source

theorem rule18152 (p1975 p2027 p2881 p2938 p3516 p3551 p4107 : Prop) (h : (¬ p2881) ∨ (¬ p4107) ∨ p2938 ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial18152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7424 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18152 (meaning t m 1975) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3516) (meaning t m 3551) (meaning t m 4107) source

theorem rule18154 (p1982 p2027 p2363 p2622 p2797 p2963 p3166 p4417 : Prop) (h : (¬ p2797) ∨ (¬ p2963) ∨ p2622 ∨ (¬ p3166) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4417)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial18154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory7426 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18154 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2622) (meaning t m 2797) (meaning t m 2963) (meaning t m 3166) (meaning t m 4417) source

theorem rule18155 (p1987 p2027 p2699 p2727 p2749 p2774 p2810 p3589 p3688 : Prop) (h : (¬ p1987) ∨ (¬ p2810) ∨ (¬ p3688) ∨ (¬ p3589) ∨ (¬ p2774) ∨ p2027 ∨ p2699 ∨ (¬ p2749) ∨ (¬ p2727)) : (¬ p1987) ∨ (p2027) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2774) ∨ (¬ p2810) ∨ (¬ p3589) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial18155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory7427 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule18155 (meaning t m 1987) (meaning t m 2027) (meaning t m 2699) (meaning t m 2727) (meaning t m 2749) (meaning t m 2774) (meaning t m 2810) (meaning t m 3589) (meaning t m 3688) source

theorem rule18156 (p1976 p2027 p2534 p2589 p2766 p2850 p3874 p3905 : Prop) (h : (¬ p1976) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p2534) ∨ (¬ p3874) ∨ (¬ p2589) ∨ p2027 ∨ p2766) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p2850) ∨ (¬ p3874) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial18156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory7428 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule18156 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2589) (meaning t m 2766) (meaning t m 2850) (meaning t m 3874) (meaning t m 3905) source

theorem rule18160 (p1976 p2027 p2534 p2764 p3055 p3874 p4444 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p4444) ∨ p2764 ∨ (¬ p3055) ∨ (¬ p2534) ∨ (¬ p3874)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (p2764) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7432 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18160 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2764) (meaning t m 3055) (meaning t m 3874) (meaning t m 4444) source

theorem rule18161 (p1988 p2027 p2622 p2797 p2963 p3286 p3461 p4367 : Prop) (h : (¬ p4367) ∨ (¬ p1988) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3286) ∨ p2622 ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p3461) ∨ (¬ p4367) := by
  classical
  tauto

theorem initial18161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4367)) := by
  have source := ElevenTheory.theory7433 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule18161 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2797) (meaning t m 2963) (meaning t m 3286) (meaning t m 3461) (meaning t m 4367) source

theorem rule18164 (p1979 p2027 p2459 p2633 p2946 p3172 p4118 : Prop) (h : (¬ p4118) ∨ (¬ p1979) ∨ p2027 ∨ p2633 ∨ (¬ p2459) ∨ (¬ p3172) ∨ (¬ p2946)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial18164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7436 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18164 (meaning t m 1979) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2946) (meaning t m 3172) (meaning t m 4118) source

theorem rule18166 (p1979 p2027 p2766 p2946 p3414 p3553 p4348 : Prop) (h : (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p1979) ∨ p2027 ∨ p2766 ∨ (¬ p2946)) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7438 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18166 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 2946) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) source

theorem rule18167 (p2743 p3364 p3367 : Prop) (h : (¬ p3364) ∨ (¬ p3367) ∨ (¬ p2743)) : (¬ p2743) ∨ (¬ p3364) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial18167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory7439 (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule18167 (meaning t m 2743) (meaning t m 3364) (meaning t m 3367) source

theorem rule18170 (p1975 p2287 p2553 p4976 : Prop) (h : (¬ p2553) ∨ (¬ p1975) ∨ p2287 ∨ p4976) : (¬ p1975) ∨ (p2287) ∨ (¬ p2553) ∨ (p4976) := by
  classical
  tauto

theorem initial18170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory7442 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule18170 (meaning t m 1975) (meaning t m 2287) (meaning t m 2553) (meaning t m 4976) source

theorem rule18172 (p1988 p2027 p2233 p2352 p2363 p2573 p3266 : Prop) (h : (¬ p2352) ∨ (¬ p2363) ∨ p2027 ∨ p2233 ∨ (¬ p3266) ∨ (¬ p1988) ∨ (¬ p2573)) : (¬ p1988) ∨ (p2027) ∨ (p2233) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial18172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory7444 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18172 (meaning t m 1988) (meaning t m 2027) (meaning t m 2233) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3266) source

theorem rule18173 (p1981 p2027 p2352 p2699 p3093 p3319 p4137 : Prop) (h : (¬ p3093) ∨ (¬ p1981) ∨ (¬ p4137) ∨ p2699 ∨ (¬ p2352) ∨ p2027 ∨ (¬ p3319)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial18173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7445 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule18173 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 4137) source

theorem rule18177 (p2001 p2027 p2622 p2630 p2657 p2946 p3156 : Prop) (h : (¬ p2001) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p2657) ∨ (¬ p2630) ∨ p2622) : (¬ p2001) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial18177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory7449 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule18177 (meaning t m 2001) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2946) (meaning t m 3156) source

theorem rule18178 (p1976 p2027 p2459 p2633 p2780 p4347 p4358 : Prop) (h : (¬ p2780) ∨ (¬ p4358) ∨ (¬ p1976) ∨ p2027 ∨ p2633 ∨ (¬ p4347) ∨ (¬ p2459)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7450 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18178 (meaning t m 1976) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2780) (meaning t m 4347) (meaning t m 4358) source

theorem rule18179 (p1990 p2027 p2323 p2563 p2901 p2946 p4235 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p4235) ∨ (¬ p2563) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2323) ∨ (¬ p2563) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7451 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18179 (meaning t m 1990) (meaning t m 2027) (meaning t m 2323) (meaning t m 2563) (meaning t m 2901) (meaning t m 2946) (meaning t m 4235) source

theorem rule18180 (p1997 p2027 p2210 p2409 p2891 p3452 p4235 : Prop) (h : (¬ p2210) ∨ p2027 ∨ p2409 ∨ (¬ p4235) ∨ (¬ p1997) ∨ (¬ p3452) ∨ (¬ p2891)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p2891) ∨ (¬ p3452) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7452 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule18180 (meaning t m 1997) (meaning t m 2027) (meaning t m 2210) (meaning t m 2409) (meaning t m 2891) (meaning t m 3452) (meaning t m 4235) source

theorem rule18182 (p1977 p2027 p2299 p2313 p2667 p3982 p4154 p5558 : Prop) (h : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p1977) ∨ (¬ p4154) ∨ (¬ p2667) ∨ p2027 ∨ (¬ p5558) ∨ p3982) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (p3982) ∨ (¬ p4154) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial18182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory7454 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule18182 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2667) (meaning t m 3982) (meaning t m 4154) (meaning t m 5558) source

theorem rule18183 (p1998 p2027 p2148 p2911 p3051 p4129 p5503 : Prop) (h : (¬ p5503) ∨ (¬ p4129) ∨ p2148 ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2911) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2148) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p4129) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial18183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory7455 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule18183 (meaning t m 1998) (meaning t m 2027) (meaning t m 2148) (meaning t m 2911) (meaning t m 3051) (meaning t m 4129) (meaning t m 5503) source

theorem rule18184 (p2011 p2027 p3115 p3623 p4075 p4320 p5660 : Prop) (h : (¬ p3115) ∨ (¬ p2011) ∨ p2027 ∨ (¬ p4075) ∨ (¬ p4320) ∨ (¬ p5660) ∨ p3623) : (¬ p2011) ∨ (p2027) ∨ (¬ p3115) ∨ (p3623) ∨ (¬ p4075) ∨ (¬ p4320) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial18184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory7456 t (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 10)
  exact rule18184 (meaning t m 2011) (meaning t m 2027) (meaning t m 3115) (meaning t m 3623) (meaning t m 4075) (meaning t m 4320) (meaning t m 5660) source

theorem rule18186 (p1999 p2027 p2148 p2563 p3051 p3125 p4235 : Prop) (h : p2148 ∨ (¬ p3125) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p1999) ∨ (¬ p4235) ∨ (¬ p2563)) : (¬ p1999) ∨ (p2027) ∨ (p2148) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3125) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7458 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule18186 (meaning t m 1999) (meaning t m 2027) (meaning t m 2148) (meaning t m 2563) (meaning t m 3051) (meaning t m 3125) (meaning t m 4235) source

theorem rule18187 (p1983 p2027 p2323 p2651 p3276 p3343 p4381 : Prop) (h : (¬ p3343) ∨ p2323 ∨ (¬ p3276) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p1983) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7459 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule18187 (meaning t m 1983) (meaning t m 2027) (meaning t m 2323) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 4381) source

theorem rule18188 (p1988 p2027 p2323 p2417 p2437 p2651 p2761 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p1988) ∨ (¬ p2651) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2437)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial18188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory7460 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18188 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2761) source

theorem rule18189 (p1997 p2027 p2699 p3707 p3830 p4322 p4948 : Prop) (h : (¬ p3830) ∨ (¬ p3707) ∨ p2027 ∨ (¬ p4948) ∨ p2699 ∨ (¬ p1997) ∨ (¬ p4322)) : (¬ p1997) ∨ (p2027) ∨ (p2699) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial18189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7461 t (m.theta 0 1) (m.theta 1 9) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule18189 (meaning t m 1997) (meaning t m 2027) (meaning t m 2699) (meaning t m 3707) (meaning t m 3830) (meaning t m 4322) (meaning t m 4948) source

theorem rule18191 (p2005 p2027 p2187 p2284 p2323 p2651 p3413 p3956 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2005) ∨ (¬ p3413) ∨ (¬ p2651) ∨ (¬ p3956) ∨ (¬ p2187)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7463 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule18191 (meaning t m 2005) (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2323) (meaning t m 2651) (meaning t m 3413) (meaning t m 3956) source

theorem rule18192 (p1990 p2027 p2114 p2284 p2737 p2811 p2958 p3051 p4320 : Prop) (h : p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p1990) ∨ (¬ p2284) ∨ (¬ p4320) ∨ (¬ p2958) ∨ (¬ p3051)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial18192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory7464 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18192 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2284) (meaning t m 2737) (meaning t m 2811) (meaning t m 2958) (meaning t m 3051) (meaning t m 4320) source

theorem rule18193 (p1987 p2027 p2766 p3177 p3877 p3941 p4348 p5590 : Prop) (h : (¬ p1987) ∨ (¬ p3941) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p3177) ∨ (¬ p5590) ∨ (¬ p4348) ∨ p2766) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial18193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory7465 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18193 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 3177) (meaning t m 3877) (meaning t m 3941) (meaning t m 4348) (meaning t m 5590) source

theorem rule18195 (p1994 p2027 p2284 p2630 p2688 p2992 p3758 p4392 : Prop) (h : (¬ p4392) ∨ (¬ p2630) ∨ (¬ p1994) ∨ p2688 ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3758)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3758) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial18195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory7467 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule18195 (meaning t m 1994) (meaning t m 2027) (meaning t m 2284) (meaning t m 2630) (meaning t m 2688) (meaning t m 2992) (meaning t m 3758) (meaning t m 4392) source

theorem rule18196 (p2010 p2027 p2202 p3222 p3238 p3346 p3389 : Prop) (h : (¬ p2010) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p3222) ∨ p2027 ∨ p2202 ∨ (¬ p3238)) : (¬ p2010) ∨ (p2027) ∨ (p2202) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial18196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory7468 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 9)
  exact rule18196 (meaning t m 2010) (meaning t m 2027) (meaning t m 2202) (meaning t m 3222) (meaning t m 3238) (meaning t m 3346) (meaning t m 3389) source

theorem rule18198 (p1985 p2027 p2323 p2331 p2901 p3136 p4195 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2901) ∨ (¬ p4195) ∨ (¬ p1985) ∨ (¬ p3136)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial18198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory7470 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule18198 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2901) (meaning t m 3136) (meaning t m 4195) source

theorem rule18201 (p1981 p2027 p2187 p2202 p2934 p3238 p4075 p4204 p5660 : Prop) (h : p2202 ∨ (¬ p3238) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p4075) ∨ (¬ p4204) ∨ (¬ p2934) ∨ (¬ p2187) ∨ (¬ p5660)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2202) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p4075) ∨ (¬ p4204) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial18201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory7473 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 10)
  exact rule18201 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2202) (meaning t m 2934) (meaning t m 3238) (meaning t m 4075) (meaning t m 4204) (meaning t m 5660) source

theorem rule18202 (p1982 p2027 p2148 p2373 p2459 p3051 p4042 p4235 : Prop) (h : (¬ p2373) ∨ p2148 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4042)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p3051) ∨ (¬ p4042) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7474 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18202 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2373) (meaning t m 2459) (meaning t m 3051) (meaning t m 4042) (meaning t m 4235) source

theorem rule18205 (p1990 p2027 p3063 p3093 p3623 p3989 p4366 : Prop) (h : p3623 ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p1990) ∨ (¬ p3989) ∨ (¬ p3093)) : (¬ p1990) ∨ (p2027) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (p3623) ∨ (¬ p3989) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7477 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 8)
  exact rule18205 (meaning t m 1990) (meaning t m 2027) (meaning t m 3063) (meaning t m 3093) (meaning t m 3623) (meaning t m 3989) (meaning t m 4366) source

theorem rule18206 (p2002 p2027 p2313 p2383 p2462 p4107 p4358 : Prop) (h : (¬ p4107) ∨ (¬ p2002) ∨ (¬ p2313) ∨ p2462 ∨ (¬ p4358) ∨ p2027 ∨ (¬ p2383)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (p2462) ∨ (¬ p4107) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7478 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule18206 (meaning t m 2002) (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 2462) (meaning t m 4107) (meaning t m 4358) source

theorem rule18207 (p1992 p2027 p2299 p2608 p2633 p3549 p3591 : Prop) (h : (¬ p2608) ∨ (¬ p3549) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3591) ∨ p2633 ∨ (¬ p2299)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial18207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory7479 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18207 (meaning t m 1992) (meaning t m 2027) (meaning t m 2299) (meaning t m 2608) (meaning t m 2633) (meaning t m 3549) (meaning t m 3591) source

theorem rule18209 (p1990 p2027 p2247 p2284 p2688 p3449 p3497 p4446 : Prop) (h : p2688 ∨ (¬ p2247) ∨ (¬ p1990) ∨ (¬ p3497) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p4446)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2284) ∨ (p2688) ∨ (¬ p3449) ∨ (¬ p3497) ∨ (¬ p4446) := by
  classical
  tauto

theorem initial18209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4446)) := by
  have source := ElevenTheory.theory7481 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule18209 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2284) (meaning t m 2688) (meaning t m 3449) (meaning t m 3497) (meaning t m 4446) source

theorem rule18210 (p1975 p2027 p2386 p2387 p2553 p3063 p3128 p4026 : Prop) (h : (¬ p2553) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p1975) ∨ p3128 ∨ (¬ p4026)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2553) ∨ (¬ p3063) ∨ (p3128) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial18210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3063)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory7482 t (m.theta 0 6) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule18210 (meaning t m 1975) (meaning t m 2027) (meaning t m 2386) (meaning t m 2387) (meaning t m 2553) (meaning t m 3063) (meaning t m 3128) (meaning t m 4026) source

theorem rule18211 (p1998 p2027 p2177 p2274 p2284 p2323 p2651 p3413 : Prop) (h : (¬ p1998) ∨ p2027 ∨ p2323 ∨ (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2651) ∨ (¬ p2274) ∨ (¬ p3413)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial18211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory7483 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18211 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2284) (meaning t m 2323) (meaning t m 2651) (meaning t m 3413) source

theorem rule18213 (p1982 p2027 p2166 p2528 p2873 p3969 p4286 : Prop) (h : p2873 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p2166) ∨ (¬ p4286) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2528) ∨ (p2873) ∨ (¬ p3969) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial18213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory7485 t (m.theta 1 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18213 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2528) (meaning t m 2873) (meaning t m 3969) (meaning t m 4286) source

theorem rule18215 (p1990 p2027 p2284 p2622 p2630 p2657 p2946 : Prop) (h : p2622 ∨ (¬ p2284) ∨ (¬ p1990) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2630)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial18215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory7487 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule18215 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2946) source

theorem rule18216 (p1985 p2027 p2449 p2545 p2657 p2807 p3690 : Prop) (h : (¬ p2807) ∨ p2545 ∨ (¬ p3690) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2657)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2449) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial18216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory7488 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule18216 (meaning t m 1985) (meaning t m 2027) (meaning t m 2449) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 3690) source

theorem rule18217 (p1977 p2027 p2169 p2274 p2313 p2957 p3662 p3989 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p2274) ∨ p2169 ∨ (¬ p2313) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p1977) ∨ (¬ p3989)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3989) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial18217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory7489 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18217 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 2957) (meaning t m 3662) (meaning t m 3989) (meaning t m 4198) source

theorem rule18218 (p1988 p2027 p2493 p2598 p2699 p3461 p3564 p3589 p3590 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3564) ∨ p2699 ∨ (¬ p1988) ∨ (¬ p3461) ∨ (¬ p2493) ∨ (¬ p3590)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3589) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial18218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory7490 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule18218 (meaning t m 1988) (meaning t m 2027) (meaning t m 2493) (meaning t m 2598) (meaning t m 2699) (meaning t m 3461) (meaning t m 3564) (meaning t m 3589) (meaning t m 3590) source

theorem rule18219 (p1982 p2027 p2545 p2657 p3286 p3506 p4444 : Prop) (h : (¬ p2657) ∨ (¬ p1982) ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p4444) ∨ p2027 ∨ p2545) : (¬ p1982) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7491 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18219 (meaning t m 1982) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 3286) (meaning t m 3506) (meaning t m 4444) source

theorem rule18221 (p1988 p2027 p2622 p2630 p2657 p3286 p3506 : Prop) (h : (¬ p3286) ∨ (¬ p3506) ∨ (¬ p1988) ∨ (¬ p2657) ∨ (¬ p2630) ∨ p2027 ∨ p2622) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3286) ∨ (¬ p3506) := by
  classical
  tauto

theorem initial18221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) := by
  have source := ElevenTheory.theory7493 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule18221 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3286) (meaning t m 3506) source

theorem rule18223 (p1983 p2027 p2449 p2622 p2630 p2657 p2807 : Prop) (h : (¬ p2807) ∨ p2622 ∨ (¬ p2449) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2657)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial18223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory7495 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule18223 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2807) source

theorem rule18224 (p1987 p2027 p2287 p2668 p2737 p3688 p4358 : Prop) (h : (¬ p2668) ∨ p2287 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4358) ∨ (¬ p3688)) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7496 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule18224 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2668) (meaning t m 2737) (meaning t m 3688) (meaning t m 4358) source

theorem rule18227 (p1987 p2027 p2252 p2633 p2992 p3414 p3553 p4315 : Prop) (h : (¬ p3414) ∨ p2633 ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2252) ∨ (¬ p2992) ∨ (¬ p1987) ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2252) ∨ (p2633) ∨ (¬ p2992) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7499 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule18227 (meaning t m 1987) (meaning t m 2027) (meaning t m 2252) (meaning t m 2633) (meaning t m 2992) (meaning t m 3414) (meaning t m 3553) (meaning t m 4315) source

theorem rule18228 (p1987 p2027 p2169 p2274 p2313 p2957 p3989 p4198 p4315 : Prop) (h : p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2169 ∨ (¬ p4198) ∨ (¬ p4315) ∨ (¬ p2957) ∨ (¬ p1987) ∨ (¬ p3989)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7500 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18228 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 2957) (meaning t m 3989) (meaning t m 4198) (meaning t m 4315) source

theorem rule18230 (p1998 p2027 p2177 p2287 p2307 p2387 p2668 : Prop) (h : (¬ p1998) ∨ (¬ p2307) ∨ p2287 ∨ (¬ p2668) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2387)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2287) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668) := by
  classical
  tauto

theorem initial18230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) := by
  have source := ElevenTheory.theory7502 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule18230 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2287) (meaning t m 2307) (meaning t m 2387) (meaning t m 2668) source

theorem rule18231 (p1982 p2027 p2177 p2233 p2459 p2553 p2573 : Prop) (h : p2233 ∨ (¬ p2573) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2553) ∨ (¬ p2177) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2233) ∨ (¬ p2459) ∨ (¬ p2553) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial18231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory7503 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18231 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2233) (meaning t m 2459) (meaning t m 2553) (meaning t m 2573) source

theorem rule18232 (p1987 p2027 p2545 p2657 p2737 p3166 p4242 p4963 : Prop) (h : (¬ p4242) ∨ (¬ p2737) ∨ (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p1987) ∨ (¬ p3166) ∨ (¬ p4963)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2737) ∨ (¬ p3166) ∨ (¬ p4242) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial18232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory7504 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8)
  exact rule18232 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2737) (meaning t m 3166) (meaning t m 4242) (meaning t m 4963) source

theorem rule18234 (p1977 p2027 p2169 p2667 p3483 p3946 p4154 p4358 : Prop) (h : (¬ p3946) ∨ (¬ p1977) ∨ p2169 ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3483) ∨ (¬ p4154) ∨ (¬ p2667)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2667) ∨ (¬ p3483) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7506 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule18234 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2667) (meaning t m 3483) (meaning t m 3946) (meaning t m 4154) (meaning t m 4358) source

theorem rule18236 (p1998 p2027 p2383 p2779 p2997 p3822 p3979 p5558 : Prop) (h : p2997 ∨ (¬ p2779) ∨ (¬ p3822) ∨ (¬ p3979) ∨ p2027 ∨ (¬ p5558) ∨ (¬ p2383) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2779) ∨ (p2997) ∨ (¬ p3822) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial18236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2779)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory7508 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule18236 (meaning t m 1998) (meaning t m 2027) (meaning t m 2383) (meaning t m 2779) (meaning t m 2997) (meaning t m 3822) (meaning t m 3979) (meaning t m 5558) source

theorem rule18238 (p1988 p2027 p2417 p2598 p2611 p2761 p3201 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p1988) ∨ (¬ p2417) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2761) ∨ (¬ p3201) := by
  classical
  tauto

theorem initial18238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3201)) := by
  have source := ElevenTheory.theory7510 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18238 (meaning t m 1988) (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2611) (meaning t m 2761) (meaning t m 3201) source

theorem rule18239 (p1977 p2027 p2545 p2657 p3654 p3987 p4037 p4154 : Prop) (h : (¬ p3987) ∨ (¬ p4154) ∨ (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p1977) ∨ (¬ p3654) ∨ (¬ p4037)) : (¬ p1977) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial18239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory7511 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule18239 (meaning t m 1977) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 3654) (meaning t m 3987) (meaning t m 4037) (meaning t m 4154) source

theorem rule18241 (p1992 p2027 p2143 p2177 p2997 p3556 p3570 p3583 : Prop) (h : (¬ p2177) ∨ p2997 ∨ (¬ p3556) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3583) ∨ (¬ p2143)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial18241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory7513 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule18241 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2177) (meaning t m 2997) (meaning t m 3556) (meaning t m 3570) (meaning t m 3583) source

theorem rule18242 (p3577 p3659 p4403 p4590 : Prop) (h : (¬ p4590) ∨ (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4403)) : (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4403) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial18242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory7514 (m.theta 0 7) (m.theta 0 8) (m.theta 2 7) (m.theta 7 8)
  exact rule18242 (meaning t m 3577) (meaning t m 3659) (meaning t m 4403) (meaning t m 4590) source

theorem rule18248 (p1997 p2027 p2542 p2842 p3422 p3564 p4037 p4194 : Prop) (h : (¬ p4037) ∨ (¬ p3564) ∨ p2842 ∨ (¬ p3422) ∨ p2027 ∨ (¬ p4194) ∨ (¬ p2542) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2842) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial18248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory7520 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule18248 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2842) (meaning t m 3422) (meaning t m 3564) (meaning t m 4037) (meaning t m 4194) source

theorem rule18249 (p1981 p2027 p2287 p2352 p2651 p2963 p3016 : Prop) (h : (¬ p1981) ∨ (¬ p3016) ∨ (¬ p2352) ∨ p2027 ∨ p2287 ∨ (¬ p2963) ∨ (¬ p2651)) : (¬ p1981) ∨ (p2027) ∨ (p2287) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial18249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory7521 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule18249 (meaning t m 1981) (meaning t m 2027) (meaning t m 2287) (meaning t m 2352) (meaning t m 2651) (meaning t m 2963) (meaning t m 3016) source

theorem rule18255 (p1975 p2027 p2114 p2553 p2651 p2737 p2811 p3016 : Prop) (h : (¬ p2811) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p2737) ∨ p2114) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial18255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory7527 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule18255 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2553) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3016) source

theorem rule18256 (p1984 p2027 p2247 p2996 p3553 p3982 p5558 : Prop) (h : (¬ p1984) ∨ p3982 ∨ (¬ p2996) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5558) ∨ (¬ p3553)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial18256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory7528 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10)
  exact rule18256 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2996) (meaning t m 3553) (meaning t m 3982) (meaning t m 5558) source

theorem rule18259 (p3922 p4514 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p3922) ∨ p4514) : (¬ p3922) ∨ (p4514) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial18259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3922)) ∨ (meaning t m 4514) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory7531 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 6)
  exact rule18259 (meaning t m 3922) (meaning t m 4514) (meaning t m 4564) source

theorem rule18261 (p1975 p2027 p2553 p2622 p2630 p3019 p3567 p3654 p4137 : Prop) (h : (¬ p3654) ∨ (¬ p3567) ∨ (¬ p1975) ∨ (¬ p4137) ∨ (¬ p2553) ∨ (¬ p3019) ∨ (¬ p2630) ∨ p2027 ∨ p2622) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3019) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial18261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7533 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule18261 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2622) (meaning t m 2630) (meaning t m 3019) (meaning t m 3567) (meaning t m 3654) (meaning t m 4137) source

theorem rule18262 (p1979 p2027 p2396 p2946 p2997 p3414 p3947 : Prop) (h : (¬ p2396) ∨ p2997 ∨ (¬ p1979) ∨ (¬ p3947) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p2946)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2946) ∨ (p2997) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial18262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory7534 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18262 (meaning t m 1979) (meaning t m 2027) (meaning t m 2396) (meaning t m 2946) (meaning t m 2997) (meaning t m 3414) (meaning t m 3947) source

theorem rule18263 (p1975 p2027 p2192 p2210 p2247 p2274 p2688 : Prop) (h : (¬ p2274) ∨ (¬ p2247) ∨ (¬ p1975) ∨ (¬ p2192) ∨ (¬ p2210) ∨ p2688 ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (p2688) := by
  classical
  tauto

theorem initial18263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2688) := by
  have source := ElevenTheory.theory7535 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule18263 (meaning t m 1975) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2247) (meaning t m 2274) (meaning t m 2688) source

theorem rule18264 (p2000 p2027 p2387 p2510 p2577 p3128 p4137 p4149 p5580 : Prop) (h : (¬ p2000) ∨ (¬ p2510) ∨ (¬ p4137) ∨ p3128 ∨ (¬ p4149) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p5580)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2577) ∨ (p3128) ∨ (¬ p4137) ∨ (¬ p4149) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7536 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule18264 (meaning t m 2000) (meaning t m 2027) (meaning t m 2387) (meaning t m 2510) (meaning t m 2577) (meaning t m 3128) (meaning t m 4137) (meaning t m 4149) (meaning t m 5580) source

theorem rule18265 (p2000 p2027 p2766 p3540 p3941 p4186 p4286 p4348 : Prop) (h : (¬ p4286) ∨ (¬ p3540) ∨ (¬ p2000) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4186) ∨ p2766 ∨ p2027) : (¬ p2000) ∨ (p2027) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3941) ∨ (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7537 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18265 (meaning t m 2000) (meaning t m 2027) (meaning t m 2766) (meaning t m 3540) (meaning t m 3941) (meaning t m 4186) (meaning t m 4286) (meaning t m 4348) source

theorem rule18266 (p1975 p2027 p2247 p2493 p2553 p2688 p3379 : Prop) (h : (¬ p1975) ∨ p2688 ∨ p2027 ∨ (¬ p3379) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2493)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (p2688) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial18266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory7538 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7)
  exact rule18266 (meaning t m 1975) (meaning t m 2027) (meaning t m 2247) (meaning t m 2493) (meaning t m 2553) (meaning t m 2688) (meaning t m 3379) source

theorem rule18267 (p1985 p2027 p2766 p2901 p3266 p4208 p4321 p4387 : Prop) (h : (¬ p4208) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p4321) ∨ (¬ p2901) ∨ p2766 ∨ (¬ p4387)) : (¬ p1985) ∨ (p2027) ∨ (p2766) ∨ (¬ p2901) ∨ (¬ p3266) ∨ (¬ p4208) ∨ (¬ p4321) ∨ (¬ p4387) := by
  classical
  tauto

theorem initial18267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4387)) := by
  have source := ElevenTheory.theory7539 t (m.theta 1 9) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18267 (meaning t m 1985) (meaning t m 2027) (meaning t m 2766) (meaning t m 2901) (meaning t m 3266) (meaning t m 4208) (meaning t m 4321) (meaning t m 4387) source

theorem rule18269 (p1997 p3008 p4110 p4718 : Prop) (h : (¬ p1997) ∨ p3008 ∨ (¬ p4110) ∨ p4718) : (¬ p1997) ∨ (p3008) ∨ (¬ p4110) ∨ (p4718) := by
  classical
  tauto

theorem initial18269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4718) := by
  have source := ElevenTheory.theory7541 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule18269 (meaning t m 1997) (meaning t m 3008) (meaning t m 4110) (meaning t m 4718) source

theorem rule18270 (p1997 p2027 p2148 p2192 p3051 p3486 p4110 : Prop) (h : p2148 ∨ (¬ p2192) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p3486) ∨ (¬ p3051)) : (¬ p1997) ∨ (p2027) ∨ (p2148) ∨ (¬ p2192) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7542 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18270 (meaning t m 1997) (meaning t m 2027) (meaning t m 2148) (meaning t m 2192) (meaning t m 3051) (meaning t m 3486) (meaning t m 4110) source

theorem rule18271 (p2010 p2027 p2437 p2518 p2699 p3379 p4256 : Prop) (h : (¬ p2010) ∨ (¬ p3379) ∨ (¬ p2437) ∨ p2027 ∨ p2699 ∨ (¬ p4256) ∨ (¬ p2518)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2518) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2518)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7543 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule18271 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2518) (meaning t m 2699) (meaning t m 3379) (meaning t m 4256) source

theorem rule18273 (p1994 p2287 p3574 p4976 : Prop) (h : (¬ p1994) ∨ p2287 ∨ p4976 ∨ (¬ p3574)) : (¬ p1994) ∨ (p2287) ∨ (¬ p3574) ∨ (p4976) := by
  classical
  tauto

theorem initial18273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory7545 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule18273 (meaning t m 1994) (meaning t m 2287) (meaning t m 3574) (meaning t m 4976) source

theorem rule18274 (p2010 p2027 p2437 p2459 p2534 p2633 p4256 : Prop) (h : (¬ p2010) ∨ p2633 ∨ (¬ p2437) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4256) ∨ (¬ p2534)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial18274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory7546 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18274 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 4256) source

theorem rule18276 (p1985 p2027 p2202 p2417 p2437 p2440 p3690 : Prop) (h : (¬ p2437) ∨ p2202 ∨ (¬ p1985) ∨ (¬ p3690) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2417)) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial18276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory7548 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule18276 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2437) (meaning t m 2440) (meaning t m 3690) source

theorem rule18277 (p1984 p2027 p2299 p2766 p3549 p3591 p4348 : Prop) (h : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3591) ∨ (¬ p4348) ∨ (¬ p2299) ∨ (¬ p3549)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7549 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18277 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 3549) (meaning t m 3591) (meaning t m 4348) source

theorem rule18278 (p1988 p2027 p2611 p2696 p3115 p3136 p3680 : Prop) (h : (¬ p2696) ∨ p2611 ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3136) ∨ (¬ p3115) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial18278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory7550 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule18278 (meaning t m 1988) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 3680) source

theorem rule18279 (p1988 p2027 p2114 p3222 p3276 p3379 p3954 : Prop) (h : p2114 ∨ (¬ p3379) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3276) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial18279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory7551 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 9) (m.theta 9 10)
  exact rule18279 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 3954) source

theorem rule18280 (p2001 p2027 p2611 p2696 p3005 p3256 p3692 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p3005) ∨ (¬ p2001) ∨ (¬ p3692) ∨ (¬ p2696) ∨ (¬ p3256)) : (¬ p2001) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial18280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7552 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18280 (meaning t m 2001) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3692) source

theorem rule18281 (p1985 p2027 p2323 p2901 p3136 p3166 p3877 : Prop) (h : (¬ p1985) ∨ p2027 ∨ (¬ p3166) ∨ (¬ p2901) ∨ p2323 ∨ (¬ p3136) ∨ (¬ p3877)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3166) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial18281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory7553 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7)
  exact rule18281 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2901) (meaning t m 3136) (meaning t m 3166) (meaning t m 3877) source

theorem rule18284 (p2018 p2027 p2098 p2938 p3055 p3684 p4235 : Prop) (h : (¬ p2018) ∨ p2938 ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p3055) ∨ (¬ p2098) ∨ p2027) : (¬ p2018) ∨ (p2027) ∨ (¬ p2098) ∨ (p2938) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7556 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7)
  exact rule18284 (meaning t m 2018) (meaning t m 2027) (meaning t m 2098) (meaning t m 2938) (meaning t m 3055) (meaning t m 3684) (meaning t m 4235) source

theorem rule18285 (p1987 p2027 p2138 p2202 p2427 p2696 p4316 p4320 : Prop) (h : p2027 ∨ (¬ p2696) ∨ (¬ p4316) ∨ (¬ p2138) ∨ (¬ p4320) ∨ (¬ p1987) ∨ (¬ p2427) ∨ p2202) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2696) ∨ (¬ p4316) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial18285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory7557 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule18285 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2202) (meaning t m 2427) (meaning t m 2696) (meaning t m 4316) (meaning t m 4320) source

theorem rule18286 (p1995 p2027 p2589 p2928 p2938 p3389 p4235 : Prop) (h : (¬ p2589) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3389) ∨ p2938 ∨ (¬ p2928) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (p2938) ∨ (¬ p3389) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7558 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule18286 (meaning t m 1995) (meaning t m 2027) (meaning t m 2589) (meaning t m 2928) (meaning t m 2938) (meaning t m 3389) (meaning t m 4235) source

theorem rule18288 (p2563 p3957 p4210 p4512 : Prop) (h : (¬ p4210) ∨ (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4512)) : (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4210) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial18288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory7560 (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6)
  exact rule18288 (meaning t m 2563) (meaning t m 3957) (meaning t m 4210) (meaning t m 4512) source

theorem rule18290 (p1978 p2027 p2938 p3497 p3646 p3747 p4228 p4336 p4393 : Prop) (h : (¬ p1978) ∨ (¬ p4228) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p3747) ∨ p2938 ∨ (¬ p4393) ∨ (¬ p4336)) : (¬ p1978) ∨ (p2027) ∨ (p2938) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p3747) ∨ (¬ p4228) ∨ (¬ p4336) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial18290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory7562 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 10)
  exact rule18290 (meaning t m 1978) (meaning t m 2027) (meaning t m 2938) (meaning t m 3497) (meaning t m 3646) (meaning t m 3747) (meaning t m 4228) (meaning t m 4336) (meaning t m 4393) source

theorem rule18291 (p1976 p2027 p3324 p3365 p3982 p4195 p5580 : Prop) (h : p3982 ∨ (¬ p3324) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p5580) ∨ (¬ p1976) ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (p3982) ∨ (¬ p4195) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory7563 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10)
  exact rule18291 (meaning t m 1976) (meaning t m 2027) (meaning t m 3324) (meaning t m 3365) (meaning t m 3982) (meaning t m 4195) (meaning t m 5580) source

theorem rule18292 (p1992 p2027 p2608 p2633 p2928 p3452 p3644 : Prop) (h : (¬ p2608) ∨ p2633 ∨ (¬ p3452) ∨ (¬ p1992) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p2928)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial18292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory7564 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8)
  exact rule18292 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2633) (meaning t m 2928) (meaning t m 3452) (meaning t m 3644) source

theorem rule18293 (p1991 p2027 p2545 p2810 p2963 p3914 p4426 p5717 : Prop) (h : (¬ p4426) ∨ p2545 ∨ (¬ p2963) ∨ (¬ p5717) ∨ (¬ p3914) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2810)) : (¬ p1991) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3914) ∨ (¬ p4426) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial18293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory7565 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 10)
  exact rule18293 (meaning t m 1991) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 2963) (meaning t m 3914) (meaning t m 4426) (meaning t m 5717) source

theorem rule18296 (p1997 p2027 p2545 p2810 p2951 p3051 p3136 p4235 : Prop) (h : (¬ p2951) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2810) ∨ (¬ p1997) ∨ (¬ p3051) ∨ (¬ p3136) ∨ p2545) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7568 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule18296 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) (meaning t m 4235) source

theorem rule18297 (p1992 p2027 p2459 p2608 p2633 p3544 p4261 p4366 : Prop) (h : (¬ p2608) ∨ (¬ p1992) ∨ p2027 ∨ p2633 ∨ (¬ p4366) ∨ (¬ p4261) ∨ (¬ p3544) ∨ (¬ p2459)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7569 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18297 (meaning t m 1992) (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2633) (meaning t m 3544) (meaning t m 4261) (meaning t m 4366) source

theorem rule18302 (p1997 p2027 p2137 p2839 p2842 p3051 p3585 p4235 : Prop) (h : (¬ p2137) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2839) ∨ p2842 ∨ (¬ p4235) ∨ (¬ p3051) ∨ (¬ p3585)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p3051) ∨ (¬ p3585) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial18302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7574 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule18302 (meaning t m 1997) (meaning t m 2027) (meaning t m 2137) (meaning t m 2839) (meaning t m 2842) (meaning t m 3051) (meaning t m 3585) (meaning t m 4235) source

theorem rule18303 (p1984 p2409 p3954 p4376 : Prop) (h : p2409 ∨ p4376 ∨ (¬ p1984) ∨ (¬ p3954)) : (¬ p1984) ∨ (p2409) ∨ (¬ p3954) ∨ (p4376) := by
  classical
  tauto

theorem initial18303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3954)) ∨ (meaning t m 4376) := by
  have source := ElevenTheory.theory7575 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4)
  exact rule18303 (meaning t m 1984) (meaning t m 2409) (meaning t m 3954) (meaning t m 4376) source

theorem rule18313 (p1992 p2027 p2608 p2764 p3817 p4366 p4381 : Prop) (h : (¬ p1992) ∨ (¬ p4366) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p4381) ∨ p2764) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial18313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7585 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule18313 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2764) (meaning t m 3817) (meaning t m 4366) (meaning t m 4381) source

theorem rule18315 (p1992 p2027 p2388 p2598 p3365 p3585 p4315 : Prop) (h : p2027 ∨ p2388 ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3365) ∨ (¬ p1992) ∨ (¬ p4315)) : (¬ p1992) ∨ (p2027) ∨ (p2388) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7587 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule18315 (meaning t m 1992) (meaning t m 2027) (meaning t m 2388) (meaning t m 2598) (meaning t m 3365) (meaning t m 3585) (meaning t m 4315) source

end SunPrize.SMT
