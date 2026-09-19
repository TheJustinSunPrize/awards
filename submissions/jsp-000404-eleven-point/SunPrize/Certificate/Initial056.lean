import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory040
import SunPrize.Certificate.Theory041
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule24255 (p2588 p3097 p4203 : Prop) (h : (¬ p4203) ∨ (¬ p2588) ∨ p3097) : (¬ p2588) ∨ (p3097) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial24255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (meaning t m 3097) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory13511 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule24255 (meaning t m 2588) (meaning t m 3097) (meaning t m 4203) source

theorem rule24257 (p2027 p2608 p2737 p3452 p3590 p4749 : Prop) (h : (¬ p4749) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p2608) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial24257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory13513 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4)
  exact rule24257 (meaning t m 2027) (meaning t m 2608) (meaning t m 2737) (meaning t m 3452) (meaning t m 3590) (meaning t m 4749) source

theorem rule24258 (p1982 p2027 p2132 p2373 p2842 p3055 p3146 p3695 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p1982) ∨ (¬ p2373) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p2132) ∨ p2842) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2373) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial24258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory13514 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule24258 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2373) (meaning t m 2842) (meaning t m 3055) (meaning t m 3146) (meaning t m 3695) source

theorem rule24259 (p2027 p2563 p2668 p3880 p4446 p4560 p4993 : Prop) (h : (¬ p2668) ∨ (¬ p4560) ∨ (¬ p2563) ∨ (¬ p4993) ∨ (¬ p4446) ∨ p2027 ∨ (¬ p3880)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3880) ∨ (¬ p4446) ∨ (¬ p4560) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial24259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4560)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory13515 t (m.theta 1 8) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule24259 (meaning t m 2027) (meaning t m 2563) (meaning t m 2668) (meaning t m 3880) (meaning t m 4446) (meaning t m 4560) (meaning t m 4993) source

theorem rule24262 (p2027 p2427 p3989 p4110 p4140 p4501 : Prop) (h : (¬ p4140) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13518 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule24262 (meaning t m 2027) (meaning t m 2427) (meaning t m 3989) (meaning t m 4110) (meaning t m 4140) (meaning t m 4501) source

theorem rule24263 (p1982 p2027 p2156 p2233 p2363 p2373 p4110 p4399 p4441 : Prop) (h : (¬ p2156) ∨ p2233 ∨ p2027 ∨ (¬ p4399) ∨ (¬ p4110) ∨ (¬ p4441) ∨ (¬ p1982) ∨ (¬ p2373) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (p2233) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial24263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory13519 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24263 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2233) (meaning t m 2363) (meaning t m 2373) (meaning t m 4110) (meaning t m 4399) (meaning t m 4441) source

theorem rule24265 (p3587 p4778 p5049 : Prop) (h : (¬ p5049) ∨ (¬ p3587) ∨ p4778) : (¬ p3587) ∨ (p4778) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial24265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3587)) ∨ (meaning t m 4778) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory13521 t (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule24265 (meaning t m 3587) (meaning t m 4778) (meaning t m 5049) source

theorem rule24268 (p2027 p2230 p2247 p2427 p2996 p3246 p3553 p4668 p5190 : Prop) (h : (¬ p4668) ∨ (¬ p5190) ∨ (¬ p2996) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2427) ∨ (¬ p2247) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4668) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial24268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13524 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24268 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 2996) (meaning t m 3246) (meaning t m 3553) (meaning t m 4668) (meaning t m 5190) source

theorem rule24269 (p2027 p2589 p2696 p2850 p3905 p4749 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p4749) ∨ (¬ p2850) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial24269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory13525 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule24269 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 2850) (meaning t m 3905) (meaning t m 4749) source

theorem rule24271 (p2027 p2137 p2156 p2737 p4173 p4874 p5049 : Prop) (h : (¬ p2737) ∨ (¬ p4874) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2156) ∨ (¬ p2137)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2737) ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial24271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory13527 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule24271 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2737) (meaning t m 4173) (meaning t m 4874) (meaning t m 5049) source

theorem rule24272 (p1987 p2027 p2633 p2696 p3055 p3644 p3742 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p1987) ∨ (¬ p3742) ∨ (¬ p2696) ∨ p2633) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial24272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory13528 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule24272 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2696) (meaning t m 3055) (meaning t m 3644) (meaning t m 3742) (meaning t m 4343) source

theorem rule24273 (p2027 p2166 p3486 p3644 p4042 p4277 : Prop) (h : (¬ p3644) ∨ p2027 ∨ (¬ p4277) ∨ (¬ p4042) ∨ (¬ p3486) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3486) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial24273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory13529 t (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule24273 (meaning t m 2027) (meaning t m 2166) (meaning t m 3486) (meaning t m 3644) (meaning t m 4042) (meaning t m 4277) source

theorem rule24274 (p2027 p2132 p2742 p2922 p3540 p3905 p4281 p5052 : Prop) (h : (¬ p2742) ∨ (¬ p3540) ∨ (¬ p2132) ∨ (¬ p2922) ∨ (¬ p5052) ∨ (¬ p4281) ∨ (¬ p3905) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2742) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4281) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial24274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory13530 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 4 7)
  exact rule24274 (meaning t m 2027) (meaning t m 2132) (meaning t m 2742) (meaning t m 2922) (meaning t m 3540) (meaning t m 3905) (meaning t m 4281) (meaning t m 5052) source

theorem rule24276 (p3425 p3589 p4366 p4424 : Prop) (h : (¬ p3589) ∨ (¬ p4424) ∨ (¬ p4366) ∨ p3425) : (p3425) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial24276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3425) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory13532 (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 7)
  exact rule24276 (meaning t m 3425) (meaning t m 3589) (meaning t m 4366) (meaning t m 4424) source

theorem rule24277 (p2027 p2156 p3540 p4110 p4399 p4644 : Prop) (h : p2027 ∨ (¬ p3540) ∨ (¬ p4399) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3540) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13533 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule24277 (meaning t m 2027) (meaning t m 2156) (meaning t m 3540) (meaning t m 4110) (meaning t m 4399) (meaning t m 4644) source

theorem rule24278 (p2027 p2132 p2742 p2778 p3319 p3946 p4759 p5052 : Prop) (h : (¬ p2778) ∨ (¬ p3319) ∨ (¬ p2132) ∨ (¬ p3946) ∨ (¬ p5052) ∨ (¬ p2742) ∨ (¬ p4759) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4759) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial24278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory13534 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 9)
  exact rule24278 (meaning t m 2027) (meaning t m 2132) (meaning t m 2742) (meaning t m 2778) (meaning t m 3319) (meaning t m 3946) (meaning t m 4759) (meaning t m 5052) source

theorem rule24280 (p2027 p2248 p2417 p2437 p2651 p3486 p3555 p3570 p4668 : Prop) (h : (¬ p2437) ∨ (¬ p2248) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p3570) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13536 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24280 (meaning t m 2027) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4668) source

theorem rule24281 (p2027 p2248 p2295 p2331 p2396 p3486 p3555 p3570 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p2396) ∨ (¬ p3555) ∨ (¬ p2295) ∨ (¬ p3486) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13537 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24281 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4668) source

theorem rule24283 (p2027 p2470 p3343 p3366 p3371 p3425 p3555 p4256 p4324 p4638 p5190 : Prop) (h : p2027 ∨ (¬ p4256) ∨ (¬ p2470) ∨ (¬ p3371) ∨ (¬ p3366) ∨ (¬ p4638) ∨ (¬ p5190) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3425) ∨ (¬ p3555) ∨ (¬ p4256) ∨ (¬ p4324) ∨ (¬ p4638) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial24283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13539 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 9)
  exact rule24283 (meaning t m 2027) (meaning t m 2470) (meaning t m 3343) (meaning t m 3366) (meaning t m 3371) (meaning t m 3425) (meaning t m 3555) (meaning t m 4256) (meaning t m 4324) (meaning t m 4638) (meaning t m 5190) source

theorem rule24289 (p2027 p2138 p2331 p2363 p2668 p3694 p4786 p5118 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p2138) ∨ (¬ p3694) ∨ (¬ p2331) ∨ (¬ p4786) ∨ (¬ p5118) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2668)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13545 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24289 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3694) (meaning t m 4786) (meaning t m 5118) (meaning t m 5568) source

theorem rule24290 (p2027 p3564 p3956 p4345 p5118 p5580 : Prop) (h : p2027 ∨ (¬ p4345) ∨ (¬ p3956) ∨ (¬ p5580) ∨ (¬ p3564) ∨ (¬ p5118)) : (p2027) ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial24290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13546 t (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule24290 (meaning t m 2027) (meaning t m 3564) (meaning t m 3956) (meaning t m 4345) (meaning t m 5118) (meaning t m 5580) source

theorem rule24291 (p2027 p3483 p3876 p3946 p4031 p4198 p4375 p4644 : Prop) (h : (¬ p4031) ∨ (¬ p3876) ∨ (¬ p4198) ∨ (¬ p3483) ∨ (¬ p3946) ∨ (¬ p4644) ∨ p2027 ∨ (¬ p4375)) : (p2027) ∨ (¬ p3483) ∨ (¬ p3876) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p4375) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13547 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 9)
  exact rule24291 (meaning t m 2027) (meaning t m 3483) (meaning t m 3876) (meaning t m 3946) (meaning t m 4031) (meaning t m 4198) (meaning t m 4375) (meaning t m 4644) source

theorem rule24292 (p2027 p2528 p2542 p3878 p4118 p4608 : Prop) (h : (¬ p2542) ∨ (¬ p2528) ∨ (¬ p4608) ∨ p2027 ∨ (¬ p3878) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2542) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial24292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory13548 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule24292 (meaning t m 2027) (meaning t m 2528) (meaning t m 2542) (meaning t m 3878) (meaning t m 4118) (meaning t m 4608) source

theorem rule24295 (p2027 p2870 p3212 p3556 p3758 p5046 : Prop) (h : (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p5046) ∨ p2027 ∨ (¬ p3212)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial24295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory13551 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule24295 (meaning t m 2027) (meaning t m 2870) (meaning t m 3212) (meaning t m 3556) (meaning t m 3758) (meaning t m 5046) source

theorem rule24298 (p2027 p2136 p2295 p2573 p3791 p4120 p4188 p4340 p4389 p4419 p4444 p4826 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p4419) ∨ (¬ p4188) ∨ (¬ p4340) ∨ (¬ p4120) ∨ (¬ p2136) ∨ (¬ p4826) ∨ (¬ p3791) ∨ (¬ p2573) ∨ (¬ p2295) ∨ (¬ p4389)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2295) ∨ (¬ p2573) ∨ (¬ p3791) ∨ (¬ p4120) ∨ (¬ p4188) ∨ (¬ p4340) ∨ (¬ p4389) ∨ (¬ p4419) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13554 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 8) (m.theta 3 6) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24298 (meaning t m 2027) (meaning t m 2136) (meaning t m 2295) (meaning t m 2573) (meaning t m 3791) (meaning t m 4120) (meaning t m 4188) (meaning t m 4340) (meaning t m 4389) (meaning t m 4419) (meaning t m 4444) (meaning t m 4826) source

theorem rule24299 (p2027 p2138 p2573 p3343 p3574 p3690 p4244 p4419 p4638 : Prop) (h : (¬ p3690) ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p4419) ∨ (¬ p3343) ∨ (¬ p4638) ∨ p2027 ∨ (¬ p3574)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4638) := by
  classical
  tauto

theorem initial24299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4638)) := by
  have source := ElevenTheory.theory13555 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule24299 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3343) (meaning t m 3574) (meaning t m 3690) (meaning t m 4244) (meaning t m 4419) (meaning t m 4638) source

theorem rule24300 (p2027 p2138 p2331 p3506 p3690 p4191 p4244 p4421 p4621 p4786 : Prop) (h : p2027 ∨ (¬ p3690) ∨ (¬ p4786) ∨ (¬ p2331) ∨ (¬ p4421) ∨ (¬ p3506) ∨ (¬ p4621) ∨ (¬ p4191) ∨ (¬ p2138) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4191) ∨ (¬ p4244) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial24300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory13556 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24300 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 3506) (meaning t m 3690) (meaning t m 4191) (meaning t m 4244) (meaning t m 4421) (meaning t m 4621) (meaning t m 4786) source

theorem rule24304 (p1992 p2027 p2608 p3146 p3578 p3860 p4261 : Prop) (h : p3578 ∨ (¬ p3860) ∨ (¬ p2608) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4261)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial24304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory13560 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule24304 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 3146) (meaning t m 3578) (meaning t m 3860) (meaning t m 4261) source

theorem rule24309 (p2027 p2138 p2241 p2727 p3083 p3570 p4244 p4420 p4736 : Prop) (h : p2027 ∨ (¬ p4420) ∨ (¬ p3570) ∨ (¬ p3083) ∨ (¬ p2138) ∨ (¬ p4736) ∨ (¬ p4244) ∨ (¬ p2727) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13565 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule24309 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2727) (meaning t m 3083) (meaning t m 3570) (meaning t m 4244) (meaning t m 4420) (meaning t m 4736) source

theorem rule24312 (p2027 p3097 p3212 p3646 p4624 p5045 : Prop) (h : (¬ p4624) ∨ (¬ p5045) ∨ (¬ p3212) ∨ (¬ p3097) ∨ (¬ p3646) ∨ p2027) : (p2027) ∨ (¬ p3097) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4624) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial24312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory13568 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule24312 (meaning t m 2027) (meaning t m 3097) (meaning t m 3212) (meaning t m 3646) (meaning t m 4624) (meaning t m 5045) source

theorem rule24313 (p2027 p2241 p2449 p2589 p3027 p3744 p4110 p4625 p5193 : Prop) (h : (¬ p5193) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p2589) ∨ (¬ p3744) ∨ (¬ p2449) ∨ (¬ p4110) ∨ (¬ p3027) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4625) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13569 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule24313 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2589) (meaning t m 3027) (meaning t m 3744) (meaning t m 4110) (meaning t m 4625) (meaning t m 5193) source

theorem rule24314 (p2027 p3055 p3399 p3527 p3941 p4425 p4736 p5119 p5160 : Prop) (h : (¬ p4736) ∨ (¬ p5160) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p3399) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p3055) ∨ p2027) : (p2027) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory13570 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24314 (meaning t m 2027) (meaning t m 3055) (meaning t m 3399) (meaning t m 3527) (meaning t m 3941) (meaning t m 4425) (meaning t m 4736) (meaning t m 5119) (meaning t m 5160) source

theorem rule24315 (p2027 p3201 p3584 p3956 p4501 p4710 : Prop) (h : (¬ p4501) ∨ (¬ p3956) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4710) ∨ (¬ p3201)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial24315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory13571 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule24315 (meaning t m 2027) (meaning t m 3201) (meaning t m 3584) (meaning t m 3956) (meaning t m 4501) (meaning t m 4710) source

theorem rule24316 (p2027 p2363 p3055 p3063 p3093 p3684 p4736 p4948 p5059 : Prop) (h : (¬ p4736) ∨ (¬ p3684) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p2363) ∨ (¬ p4948) ∨ (¬ p5059)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3684) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial24316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory13572 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24316 (meaning t m 2027) (meaning t m 2363) (meaning t m 3055) (meaning t m 3063) (meaning t m 3093) (meaning t m 3684) (meaning t m 4736) (meaning t m 4948) (meaning t m 5059) source

theorem rule24317 (p2761 p3266 p4443 : Prop) (h : (¬ p3266) ∨ (¬ p4443) ∨ p2761) : (p2761) ∨ (¬ p3266) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial24317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2761) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory13573 (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24317 (meaning t m 2761) (meaning t m 3266) (meaning t m 4443) source

theorem rule24318 (p2027 p2589 p3222 p3347 p4235 p4952 p5104 : Prop) (h : (¬ p3222) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p4952) ∨ (¬ p2589) ∨ (¬ p5104)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3222) ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p4952) ∨ (¬ p5104) := by
  classical
  tauto

theorem initial24318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5104)) := by
  have source := ElevenTheory.theory13574 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9)
  exact rule24318 (meaning t m 2027) (meaning t m 2589) (meaning t m 3222) (meaning t m 3347) (meaning t m 4235) (meaning t m 4952) (meaning t m 5104) source

theorem rule24320 (p2027 p2396 p3055 p3093 p3309 p3644 p3876 p4668 p4736 : Prop) (h : (¬ p4668) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p4736) ∨ (¬ p3093) ∨ (¬ p3644) ∨ (¬ p3309) ∨ (¬ p3876) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13576 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24320 (meaning t m 2027) (meaning t m 2396) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3644) (meaning t m 3876) (meaning t m 4668) (meaning t m 4736) source

theorem rule24322 (p3904 p4984 p5197 : Prop) (h : (¬ p3904) ∨ (¬ p4984) ∨ p5197) : (¬ p3904) ∨ (¬ p4984) ∨ (p5197) := by
  classical
  tauto

theorem initial24322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4984)) ∨ (meaning t m 5197) := by
  have source := ElevenTheory.theory13578 (m.theta 0 4) (m.theta 0 5) (m.theta 0 7)
  exact rule24322 (meaning t m 3904) (meaning t m 4984) (meaning t m 5197) source

theorem rule24324 (p3572 p4315 p4386 : Prop) (h : (¬ p4386) ∨ (¬ p4315) ∨ p3572) : (p3572) ∨ (¬ p4315) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial24324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3572) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory13580 (m.theta 2 3) (m.theta 3 5) (m.theta 3 7)
  exact rule24324 (meaning t m 3572) (meaning t m 4315) (meaning t m 4386) source

theorem rule24326 (p2657 p3055 p4117 p4343 : Prop) (h : (¬ p4117) ∨ (¬ p3055) ∨ (¬ p4343) ∨ p2657) : (p2657) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial24326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2657) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory13582 (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 4)
  exact rule24326 (meaning t m 2657) (meaning t m 3055) (meaning t m 4117) (meaning t m 4343) source

theorem rule24328 (p2027 p2319 p2341 p2441 p2982 p3644 p4356 p5046 : Prop) (h : (¬ p2319) ∨ p4356 ∨ (¬ p3644) ∨ (¬ p5046) ∨ (¬ p2441) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2982) ∨ (¬ p3644) ∨ (p4356) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial24328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 4356) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory13584 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8)
  exact rule24328 (meaning t m 2027) (meaning t m 2319) (meaning t m 2341) (meaning t m 2441) (meaning t m 2982) (meaning t m 3644) (meaning t m 4356) (meaning t m 5046) source

theorem rule24329 (p2027 p2579 p2608 p3537 p4019 p4137 p4191 p5119 p5193 : Prop) (h : (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4137) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p2579) ∨ (¬ p4019)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4019) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13585 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule24329 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 3537) (meaning t m 4019) (meaning t m 4137) (meaning t m 4191) (meaning t m 5119) (meaning t m 5193) source

theorem rule24330 (p2027 p2707 p2743 p3414 p4325 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p2743) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p4325)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3414) ∨ (¬ p4325) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial24330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13586 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule24330 (meaning t m 2027) (meaning t m 2707) (meaning t m 2743) (meaning t m 3414) (meaning t m 4325) (meaning t m 4787) source

theorem rule24331 (p2027 p3319 p4037 p4111 p4759 p4975 : Prop) (h : (¬ p4037) ∨ (¬ p4759) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p4975)) : (p2027) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4111) ∨ (¬ p4759) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial24331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory13587 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule24331 (meaning t m 2027) (meaning t m 3319) (meaning t m 4037) (meaning t m 4111) (meaning t m 4759) (meaning t m 4975) source

theorem rule24332 (p2027 p2122 p2963 p3568 p4426 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4426) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4426) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial24332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13588 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule24332 (meaning t m 2027) (meaning t m 2122) (meaning t m 2963) (meaning t m 3568) (meaning t m 4426) (meaning t m 4787) source

theorem rule24334 (p2027 p2598 p3365 p3683 p3877 p5008 : Prop) (h : (¬ p5008) ∨ (¬ p3683) ∨ (¬ p3365) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3877)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p3877) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial24334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory13590 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8)
  exact rule24334 (meaning t m 2027) (meaning t m 2598) (meaning t m 3365) (meaning t m 3683) (meaning t m 3877) (meaning t m 5008) source

theorem rule24335 (p2027 p2598 p3365 p3683 p4315 p4701 : Prop) (h : (¬ p3365) ∨ (¬ p2598) ∨ (¬ p4701) ∨ (¬ p3683) ∨ p2027 ∨ (¬ p4315)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4315) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13591 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5)
  exact rule24335 (meaning t m 2027) (meaning t m 2598) (meaning t m 3365) (meaning t m 3683) (meaning t m 4315) (meaning t m 4701) source

theorem rule24337 (p2299 p3644 p3921 : Prop) (h : (¬ p3921) ∨ (¬ p2299) ∨ p3644) : (¬ p2299) ∨ (p3644) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial24337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (meaning t m 3644) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory13593 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24337 (meaning t m 2299) (meaning t m 3644) (meaning t m 3921) source

theorem rule24345 (p2578 p3567 p4389 : Prop) (h : (¬ p3567) ∨ (¬ p4389) ∨ p2578) : (p2578) ∨ (¬ p3567) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial24345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2578) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory13601 (m.theta 0 6) (m.theta 3 6) (m.theta 4 6)
  exact rule24345 (meaning t m 2578) (meaning t m 3567) (meaning t m 4389) source

theorem rule24348 (p2027 p2248 p2901 p2946 p3246 p3588 p3659 p3954 p4668 : Prop) (h : (¬ p2946) ∨ (¬ p4668) ∨ (¬ p2901) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p2248) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3659)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13604 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24348 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4668) source

theorem rule24349 (p2027 p3201 p3556 p3569 p3684 p4533 : Prop) (h : p2027 ∨ (¬ p4533) ∨ (¬ p3556) ∨ (¬ p3684) ∨ (¬ p3569) ∨ (¬ p3201)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3556) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial24349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory13605 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule24349 (meaning t m 2027) (meaning t m 3201) (meaning t m 3556) (meaning t m 3569) (meaning t m 3684) (meaning t m 4533) source

theorem rule24353 (p3873 p4419 p5190 : Prop) (h : (¬ p3873) ∨ (¬ p5190) ∨ p4419) : (¬ p3873) ∨ (p4419) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial24353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3873)) ∨ (meaning t m 4419) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13609 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4)
  exact rule24353 (meaning t m 3873) (meaning t m 4419) (meaning t m 5190) source

theorem rule24355 (p2027 p2143 p2427 p2829 p3365 p3366 p3483 p3556 p4368 p4948 p5052 : Prop) (h : (¬ p4368) ∨ (¬ p5052) ∨ p2027 ∨ (¬ p3483) ∨ (¬ p2427) ∨ (¬ p2829) ∨ (¬ p3366) ∨ (¬ p3365) ∨ (¬ p3556) ∨ (¬ p4948) ∨ (¬ p2143)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2427) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3483) ∨ (¬ p3556) ∨ (¬ p4368) ∨ (¬ p4948) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial24355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory13611 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9)
  exact rule24355 (meaning t m 2027) (meaning t m 2143) (meaning t m 2427) (meaning t m 2829) (meaning t m 3365) (meaning t m 3366) (meaning t m 3483) (meaning t m 3556) (meaning t m 4368) (meaning t m 4948) (meaning t m 5052) source

theorem rule24358 (p2881 p3945 p4107 p4275 : Prop) (h : (¬ p3945) ∨ (¬ p2881) ∨ (¬ p4275) ∨ (¬ p4107)) : (¬ p2881) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial24358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory13614 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24358 (meaning t m 2881) (meaning t m 3945) (meaning t m 4107) (meaning t m 4275) source

theorem rule24359 (p2505 p3541 p4869 : Prop) (h : (¬ p3541) ∨ (¬ p2505) ∨ p4869) : (¬ p2505) ∨ (¬ p3541) ∨ (p4869) := by
  classical
  tauto

theorem initial24359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3541)) ∨ (meaning t m 4869) := by
  have source := ElevenTheory.theory13615 (m.theta 1 2) (m.theta 1 4) (m.theta 1 6)
  exact rule24359 (meaning t m 2505) (meaning t m 3541) (meaning t m 4869) source

theorem rule24360 (p2027 p2132 p2313 p2742 p2778 p3309 p4759 p5052 : Prop) (h : p2027 ∨ (¬ p4759) ∨ (¬ p2132) ∨ (¬ p2742) ∨ (¬ p5052) ∨ (¬ p3309) ∨ (¬ p2313) ∨ (¬ p2778)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2313) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3309) ∨ (¬ p4759) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial24360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory13616 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 7)
  exact rule24360 (meaning t m 2027) (meaning t m 2132) (meaning t m 2313) (meaning t m 2742) (meaning t m 2778) (meaning t m 3309) (meaning t m 4759) (meaning t m 5052) source

theorem rule24361 (p1984 p2027 p2997 p3097 p3583 p3758 p3954 : Prop) (h : (¬ p3583) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3954) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3758)) : (¬ p1984) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial24361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory13617 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule24361 (meaning t m 1984) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3583) (meaning t m 3758) (meaning t m 3954) source

theorem rule24362 (p2027 p2156 p2870 p3556 p4110 p4885 : Prop) (h : (¬ p4110) ∨ (¬ p2156) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p4885) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial24362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory13618 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24362 (meaning t m 2027) (meaning t m 2156) (meaning t m 2870) (meaning t m 3556) (meaning t m 4110) (meaning t m 4885) source

theorem rule24363 (p2027 p2248 p3166 p3256 p3266 p3588 p3954 p4423 p4831 : Prop) (h : (¬ p3266) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2248) ∨ (¬ p4831) ∨ (¬ p3588) ∨ (¬ p4423) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4423) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial24363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory13619 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24363 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3588) (meaning t m 3954) (meaning t m 4423) (meaning t m 4831) source

theorem rule24365 (p1993 p2611 p2651 p4117 p5011 : Prop) (h : (¬ p4117) ∨ (¬ p1993) ∨ (¬ p2651) ∨ p2611 ∨ p5011) : (¬ p1993) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (p5011) := by
  classical
  tauto

theorem initial24365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 4117)) ∨ (meaning t m 5011) := by
  have source := ElevenTheory.theory13621 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 4) (m.theta 3 8)
  exact rule24365 (meaning t m 1993) (meaning t m 2611) (meaning t m 2651) (meaning t m 4117) (meaning t m 5011) source

theorem rule24366 (p2027 p2313 p2630 p2696 p3083 p3309 p3923 p4596 p4733 p5015 : Prop) (h : (¬ p2630) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4596) ∨ (¬ p3083) ∨ (¬ p2696) ∨ (¬ p5015) ∨ p2027 ∨ (¬ p4733)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4596) ∨ (¬ p4733) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial24366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory13622 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule24366 (meaning t m 2027) (meaning t m 2313) (meaning t m 2630) (meaning t m 2696) (meaning t m 3083) (meaning t m 3309) (meaning t m 3923) (meaning t m 4596) (meaning t m 4733) (meaning t m 5015) source

theorem rule24367 (p2027 p2248 p2299 p2373 p2542 p2651 p3549 p3591 p4902 : Prop) (h : (¬ p2373) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2299) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2542) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13623 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule24367 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2373) (meaning t m 2542) (meaning t m 2651) (meaning t m 3549) (meaning t m 3591) (meaning t m 4902) source

theorem rule24368 (p2027 p2363 p2696 p3136 p3156 p3860 p4261 p4433 p4733 : Prop) (h : (¬ p4261) ∨ (¬ p2363) ∨ (¬ p4733) ∨ (¬ p3860) ∨ (¬ p3156) ∨ (¬ p3136) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p2696)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4433) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13624 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24368 (meaning t m 2027) (meaning t m 2363) (meaning t m 2696) (meaning t m 3136) (meaning t m 3156) (meaning t m 3860) (meaning t m 4261) (meaning t m 4433) (meaning t m 4733) source

theorem rule24370 (p2027 p2417 p2437 p2651 p2753 p3645 p3646 p3950 p3989 p4117 p4347 p4877 : Prop) (h : (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p2437) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3950) ∨ (¬ p4117) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4117) ∨ (¬ p4347) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13626 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24370 (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2753) (meaning t m 3645) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4117) (meaning t m 4347) (meaning t m 4877) source

theorem rule24371 (p1998 p2027 p2753 p2764 p2911 p3471 p3645 p3646 p3744 p4191 p4253 p4877 p5503 : Prop) (h : (¬ p4191) ∨ (¬ p1998) ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p4253) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2911) ∨ (¬ p2753) ∨ p2764 ∨ (¬ p3744) ∨ (¬ p3471) ∨ (¬ p5503)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p2911) ∨ (¬ p3471) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4877) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial24371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory13627 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule24371 (meaning t m 1998) (meaning t m 2027) (meaning t m 2753) (meaning t m 2764) (meaning t m 2911) (meaning t m 3471) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 4191) (meaning t m 4253) (meaning t m 4877) (meaning t m 5503) source

theorem rule24372 (p2027 p2387 p2598 p2753 p3201 p3204 p3692 p3868 p4441 p4444 p4512 p4826 p4877 : Prop) (h : (¬ p4826) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p4444) ∨ (¬ p3204) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4441) ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p4512) ∨ (¬ p2387) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3204) ∨ (¬ p3692) ∨ (¬ p3868) ∨ (¬ p4441) ∨ (¬ p4444) ∨ (¬ p4512) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13628 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24372 (meaning t m 2027) (meaning t m 2387) (meaning t m 2598) (meaning t m 2753) (meaning t m 3201) (meaning t m 3204) (meaning t m 3692) (meaning t m 3868) (meaning t m 4441) (meaning t m 4444) (meaning t m 4512) (meaning t m 4826) (meaning t m 4877) source

theorem rule24373 (p2027 p2598 p2753 p3201 p3645 p3646 p3744 p3868 p4191 p4826 p4877 : Prop) (h : (¬ p2753) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p3645) ∨ (¬ p3868) ∨ (¬ p3744) ∨ (¬ p3646) ∨ (¬ p4191) ∨ (¬ p4877) ∨ (¬ p2598) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3868) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13629 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24373 (meaning t m 2027) (meaning t m 2598) (meaning t m 2753) (meaning t m 3201) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 3868) (meaning t m 4191) (meaning t m 4826) (meaning t m 4877) source

theorem rule24374 (p2027 p2210 p2264 p2685 p2696 p2753 p3817 p4366 p4666 p4877 : Prop) (h : (¬ p2685) ∨ (¬ p4877) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2210) ∨ (¬ p4666) ∨ (¬ p2696) ∨ (¬ p4366) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13630 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24374 (meaning t m 2027) (meaning t m 2210) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) (meaning t m 4877) source

theorem rule24376 (p2027 p2753 p3093 p3286 p3506 p3817 p4117 p4366 p4425 p4512 p4638 p4877 : Prop) (h : (¬ p3506) ∨ (¬ p3093) ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p4638) ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p3817) ∨ (¬ p4512) ∨ (¬ p4425) ∨ p2027) : (p2027) ∨ (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4117) ∨ (¬ p4366) ∨ (¬ p4425) ∨ (¬ p4512) ∨ (¬ p4638) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13632 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 1 7) (m.theta 3 9) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24376 (meaning t m 2027) (meaning t m 2753) (meaning t m 3093) (meaning t m 3286) (meaning t m 3506) (meaning t m 3817) (meaning t m 4117) (meaning t m 4366) (meaning t m 4425) (meaning t m 4512) (meaning t m 4638) (meaning t m 4877) source

theorem rule24379 (p2027 p2210 p2417 p2598 p2753 p3201 p3860 p3950 p4261 p4877 : Prop) (h : (¬ p2210) ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p4877) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2417) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13635 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule24379 (meaning t m 2027) (meaning t m 2210) (meaning t m 2417) (meaning t m 2598) (meaning t m 2753) (meaning t m 3201) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 4877) source

theorem rule24381 (p2027 p2960 p3051 p3136 p3572 p3699 : Prop) (h : (¬ p2960) ∨ (¬ p3136) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3699)) : (p2027) ∨ (¬ p2960) ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial24381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory13637 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule24381 (meaning t m 2027) (meaning t m 2960) (meaning t m 3051) (meaning t m 3136) (meaning t m 3572) (meaning t m 3699) source

theorem rule24382 (p2027 p2542 p2870 p3742 p4001 p4885 : Prop) (h : (¬ p4001) ∨ (¬ p4885) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2870) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial24382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory13638 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule24382 (meaning t m 2027) (meaning t m 2542) (meaning t m 2870) (meaning t m 3742) (meaning t m 4001) (meaning t m 4885) source

theorem rule24384 (p1990 p2027 p2202 p2352 p3422 p3684 p3989 : Prop) (h : p2202 ∨ (¬ p1990) ∨ (¬ p2352) ∨ (¬ p3422) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial24384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory13640 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule24384 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 3422) (meaning t m 3684) (meaning t m 3989) source

theorem rule24386 (p2027 p2248 p2901 p2946 p3954 p4129 p4379 p4826 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p2901) ∨ (¬ p3954) ∨ (¬ p4826) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p4379) ∨ (¬ p2248) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3954) ∨ (¬ p4129) ∨ (¬ p4379) ∨ (¬ p4826) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial24386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory13642 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 9) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24386 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3954) (meaning t m 4129) (meaning t m 4379) (meaning t m 4826) (meaning t m 5387) source

theorem rule24387 (p2027 p2248 p2437 p2651 p3555 p3868 p4322 p4363 p4826 : Prop) (h : (¬ p4322) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p4363) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3555) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13643 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24387 (meaning t m 2027) (meaning t m 2248) (meaning t m 2437) (meaning t m 2651) (meaning t m 3555) (meaning t m 3868) (meaning t m 4322) (meaning t m 4363) (meaning t m 4826) source

theorem rule24388 (p2027 p2505 p2590 p2928 p3063 p3956 p4644 : Prop) (h : (¬ p3956) ∨ (¬ p2590) ∨ (¬ p4644) ∨ (¬ p3063) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p2505)) : (p2027) ∨ (¬ p2505) ∨ (¬ p2590) ∨ (¬ p2928) ∨ (¬ p3063) ∨ (¬ p3956) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13644 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule24388 (meaning t m 2027) (meaning t m 2505) (meaning t m 2590) (meaning t m 2928) (meaning t m 3063) (meaning t m 3956) (meaning t m 4644) source

theorem rule24389 (p2027 p2737 p2952 p3136 p4236 p4734 : Prop) (h : (¬ p4734) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial24389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory13645 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5)
  exact rule24389 (meaning t m 2027) (meaning t m 2737) (meaning t m 2952) (meaning t m 3136) (meaning t m 4236) (meaning t m 4734) source

theorem rule24390 (p2027 p2210 p2749 p2922 p3540 p4108 p4281 p4877 : Prop) (h : (¬ p4877) ∨ (¬ p4281) ∨ (¬ p2749) ∨ (¬ p2210) ∨ (¬ p3540) ∨ (¬ p4108) ∨ p2027 ∨ (¬ p2922)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2749) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4281) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13646 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7)
  exact rule24390 (meaning t m 2027) (meaning t m 2210) (meaning t m 2749) (meaning t m 2922) (meaning t m 3540) (meaning t m 4108) (meaning t m 4281) (meaning t m 4877) source

theorem rule24391 (p2027 p2210 p2928 p3452 p4210 p4644 : Prop) (h : (¬ p4210) ∨ (¬ p4644) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13647 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7)
  exact rule24391 (meaning t m 2027) (meaning t m 2210) (meaning t m 2928) (meaning t m 3452) (meaning t m 4210) (meaning t m 4644) source

theorem rule24393 (p3694 p3747 p4244 : Prop) (h : (¬ p3694) ∨ (¬ p3747) ∨ p4244) : (¬ p3694) ∨ (¬ p3747) ∨ (p4244) := by
  classical
  tauto

theorem initial24393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3747)) ∨ (meaning t m 4244) := by
  have source := ElevenTheory.theory13649 (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule24393 (meaning t m 3694) (meaning t m 3747) (meaning t m 4244) source

theorem rule24394 (p2027 p2245 p2749 p3027 p3379 p3414 p5216 : Prop) (h : (¬ p3414) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p3379) ∨ (¬ p3027) ∨ (¬ p2749) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2749) ∨ (¬ p3027) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13650 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 7)
  exact rule24394 (meaning t m 2027) (meaning t m 2245) (meaning t m 2749) (meaning t m 3027) (meaning t m 3379) (meaning t m 3414) (meaning t m 5216) source

theorem rule24396 (p2027 p2299 p2696 p3136 p3156 p3549 p3591 p4733 p4902 : Prop) (h : (¬ p4733) ∨ (¬ p3136) ∨ (¬ p3591) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2299) ∨ (¬ p4902) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13652 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule24396 (meaning t m 2027) (meaning t m 2299) (meaning t m 2696) (meaning t m 3136) (meaning t m 3156) (meaning t m 3549) (meaning t m 3591) (meaning t m 4733) (meaning t m 4902) source

theorem rule24397 (p2027 p2386 p2387 p2505 p3063 p3574 p4814 : Prop) (h : (¬ p2386) ∨ (¬ p2387) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4814) ∨ (¬ p2505)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3574) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial24397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory13653 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule24397 (meaning t m 2027) (meaning t m 2386) (meaning t m 2387) (meaning t m 2505) (meaning t m 3063) (meaning t m 3574) (meaning t m 4814) source

theorem rule24398 (p2027 p2331 p2499 p2588 p2668 p2737 p2811 p3055 p4030 p4405 p4734 : Prop) (h : (¬ p2588) ∨ (¬ p2499) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4030) ∨ (¬ p3055) ∨ (¬ p2737) ∨ (¬ p4734) ∨ (¬ p2668) ∨ (¬ p4405)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4405) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial24398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory13654 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24398 (meaning t m 2027) (meaning t m 2331) (meaning t m 2499) (meaning t m 2588) (meaning t m 2668) (meaning t m 2737) (meaning t m 2811) (meaning t m 3055) (meaning t m 4030) (meaning t m 4405) (meaning t m 4734) source

theorem rule24399 (p2027 p2598 p2780 p3016 p4342 p4750 : Prop) (h : (¬ p3016) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4750) ∨ (¬ p4342)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial24399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13655 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule24399 (meaning t m 2027) (meaning t m 2598) (meaning t m 2780) (meaning t m 3016) (meaning t m 4342) (meaning t m 4750) source

theorem rule24400 (p2027 p2132 p3055 p3695 p3876 p4644 : Prop) (h : (¬ p4644) ∨ (¬ p3695) ∨ (¬ p2132) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p3055)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p3876) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13656 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule24400 (meaning t m 2027) (meaning t m 2132) (meaning t m 3055) (meaning t m 3695) (meaning t m 3876) (meaning t m 4644) source

theorem rule24401 (p2027 p3379 p3527 p3551 p3687 p5206 p5216 : Prop) (h : (¬ p3551) ∨ (¬ p3527) ∨ (¬ p5206) ∨ (¬ p3687) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3379)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3687) ∨ (¬ p5206) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 5206)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13657 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 7 8)
  exact rule24401 (meaning t m 2027) (meaning t m 3379) (meaning t m 3527) (meaning t m 3551) (meaning t m 3687) (meaning t m 5206) (meaning t m 5216) source

theorem rule24402 (p2027 p2132 p2509 p2534 p2870 p3246 p3452 p3950 p4733 : Prop) (h : (¬ p2534) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p2132) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p3950) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13658 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule24402 (meaning t m 2027) (meaning t m 2132) (meaning t m 2509) (meaning t m 2534) (meaning t m 2870) (meaning t m 3246) (meaning t m 3452) (meaning t m 3950) (meaning t m 4733) source

theorem rule24404 (p2027 p2449 p2685 p2696 p3591 p3923 p3950 p4347 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p2685) ∨ (¬ p3591) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3923) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13660 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24404 (meaning t m 2027) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3591) (meaning t m 3923) (meaning t m 3950) (meaning t m 4347) (meaning t m 4733) source

theorem rule24407 (p2027 p2132 p2753 p2870 p2881 p3379 p3817 p4366 p4666 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p2753) ∨ (¬ p4666) ∨ (¬ p4366) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13663 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24407 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) (meaning t m 5216) source

theorem rule24411 (p2027 p2589 p2753 p2761 p3347 p3434 p3471 p3880 p5123 p5216 p5568 : Prop) (h : (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3471) ∨ (¬ p3880) ∨ (¬ p3434) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2761) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3347) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3880) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13667 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule24411 (meaning t m 2027) (meaning t m 2589) (meaning t m 2753) (meaning t m 2761) (meaning t m 3347) (meaning t m 3434) (meaning t m 3471) (meaning t m 3880) (meaning t m 5123) (meaning t m 5216) (meaning t m 5568) source

theorem rule24412 (p1994 p2027 p2630 p2753 p2766 p2807 p3266 p3379 p3572 p3834 p4117 p4321 p5216 : Prop) (h : (¬ p3379) ∨ (¬ p4321) ∨ p2766 ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3834) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p2807) ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p5216) ∨ (¬ p3266)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2753) ∨ (p2766) ∨ (¬ p2807) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3572) ∨ (¬ p3834) ∨ (¬ p4117) ∨ (¬ p4321) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13668 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 8 9) (m.theta 9 10)
  exact rule24412 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2753) (meaning t m 2766) (meaning t m 2807) (meaning t m 3266) (meaning t m 3379) (meaning t m 3572) (meaning t m 3834) (meaning t m 4117) (meaning t m 4321) (meaning t m 5216) source

theorem rule24413 (p2027 p2589 p2696 p3506 p3755 p3880 p4729 p5123 p5568 : Prop) (h : (¬ p5123) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3755) ∨ (¬ p3506) ∨ (¬ p2696) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13669 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24413 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 3506) (meaning t m 3755) (meaning t m 3880) (meaning t m 4729) (meaning t m 5123) (meaning t m 5568) source

theorem rule24415 (p2027 p2210 p2449 p2685 p2696 p2753 p3692 p3860 p3906 p3950 p4877 : Prop) (h : (¬ p3950) ∨ (¬ p3906) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3692) ∨ (¬ p2449) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2685) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p3950) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13671 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24415 (meaning t m 2027) (meaning t m 2210) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3692) (meaning t m 3860) (meaning t m 3906) (meaning t m 3950) (meaning t m 4877) source

theorem rule24417 (p2027 p2807 p3266 p3346 p3572 p3755 p4117 p4425 p4729 p5109 : Prop) (h : (¬ p5109) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p3266) ∨ (¬ p3572) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3346) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2807) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4425) ∨ (¬ p4729) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial24417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory13673 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24417 (meaning t m 2027) (meaning t m 2807) (meaning t m 3266) (meaning t m 3346) (meaning t m 3572) (meaning t m 3755) (meaning t m 4117) (meaning t m 4425) (meaning t m 4729) (meaning t m 5109) source

theorem rule24418 (p2027 p2579 p2696 p2753 p3347 p3506 p3755 p3956 p5123 p5216 p5580 : Prop) (h : (¬ p3506) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3956) ∨ (¬ p5580) ∨ (¬ p5216) ∨ (¬ p5123) ∨ (¬ p3755) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3347)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p3956) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial24418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13674 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24418 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3506) (meaning t m 3755) (meaning t m 3956) (meaning t m 5123) (meaning t m 5216) (meaning t m 5580) source

theorem rule24419 (p2027 p2132 p2579 p2753 p3105 p3347 p3680 p3956 p5123 p5216 p5580 : Prop) (h : (¬ p3347) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3680) ∨ (¬ p5580) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p5216) ∨ (¬ p5123) ∨ (¬ p3956) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3347) ∨ (¬ p3680) ∨ (¬ p3956) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial24419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13675 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24419 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2753) (meaning t m 3105) (meaning t m 3347) (meaning t m 3680) (meaning t m 3956) (meaning t m 5123) (meaning t m 5216) (meaning t m 5580) source

theorem rule24420 (p2027 p2177 p2685 p2753 p2946 p3347 p3540 p3644 p4117 p4315 p4570 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p5216) ∨ (¬ p2685) ∨ (¬ p4315) ∨ (¬ p4570) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4570) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13676 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24420 (meaning t m 2027) (meaning t m 2177) (meaning t m 2685) (meaning t m 2753) (meaning t m 2946) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) (meaning t m 4117) (meaning t m 4315) (meaning t m 4570) (meaning t m 5216) source

theorem rule24421 (p2027 p2177 p2696 p2753 p2901 p3136 p3347 p3540 p3644 p4556 p5216 : Prop) (h : (¬ p2901) ∨ (¬ p2177) ∨ (¬ p3644) ∨ (¬ p3347) ∨ (¬ p4556) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p5216) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4556) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13677 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24421 (meaning t m 2027) (meaning t m 2177) (meaning t m 2696) (meaning t m 2753) (meaning t m 2901) (meaning t m 3136) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) (meaning t m 4556) (meaning t m 5216) source

theorem rule24422 (p2027 p2246 p2579 p2749 p2946 p3347 p3755 p3956 p4039 p4315 p4347 p4450 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p4039) ∨ (¬ p3755) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4315) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3755) ∨ (¬ p3956) ∨ (¬ p4039) ∨ (¬ p4315) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13678 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24422 (meaning t m 2027) (meaning t m 2246) (meaning t m 2579) (meaning t m 2749) (meaning t m 2946) (meaning t m 3347) (meaning t m 3755) (meaning t m 3956) (meaning t m 4039) (meaning t m 4315) (meaning t m 4347) (meaning t m 4450) (meaning t m 5216) source

theorem rule24424 (p2927 p4647 p4914 : Prop) (h : (¬ p2927) ∨ (¬ p4647) ∨ p4914) : (¬ p2927) ∨ (¬ p4647) ∨ (p4914) := by
  classical
  tauto

theorem initial24424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 4647)) ∨ (meaning t m 4914) := by
  have source := ElevenTheory.theory13680 t (m.theta 1 7) (m.theta 4 7) (m.theta 5 7)
  exact rule24424 (meaning t m 2927) (meaning t m 4647) (meaning t m 4914) source

theorem rule24426 (p2027 p2210 p2579 p2972 p3347 p3954 p3956 p4347 p4450 p5216 : Prop) (h : p2027 ∨ (¬ p4450) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p2972)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2972) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13682 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24426 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 2972) (meaning t m 3347) (meaning t m 3954) (meaning t m 3956) (meaning t m 4347) (meaning t m 4450) (meaning t m 5216) source

theorem rule24431 (p2027 p2696 p2753 p3005 p3256 p3379 p3591 p4026 p4604 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3005) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13687 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24431 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3379) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) (meaning t m 5216) source

theorem rule24432 (p1984 p2027 p2299 p2493 p2579 p2633 p2928 p3921 p4108 : Prop) (h : (¬ p4108) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2493) ∨ (¬ p2299) ∨ (¬ p2928) ∨ (¬ p3921) ∨ p2633) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial24432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory13688 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24432 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2493) (meaning t m 2579) (meaning t m 2633) (meaning t m 2928) (meaning t m 3921) (meaning t m 4108) source

theorem rule24433 (p2027 p2177 p3323 p3553 p4067 p4624 : Prop) (h : (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3323) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial24433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13689 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule24433 (meaning t m 2027) (meaning t m 2177) (meaning t m 3323) (meaning t m 3553) (meaning t m 4067) (meaning t m 4624) source

theorem rule24435 (p2027 p2579 p2946 p3156 p3969 p4117 p4137 p4191 p4729 p5119 : Prop) (h : (¬ p2946) ∨ (¬ p4729) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p5119) ∨ (¬ p4191) ∨ (¬ p2579) ∨ (¬ p4117) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4117) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4729) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial24435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13691 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule24435 (meaning t m 2027) (meaning t m 2579) (meaning t m 2946) (meaning t m 3156) (meaning t m 3969) (meaning t m 4117) (meaning t m 4137) (meaning t m 4191) (meaning t m 4729) (meaning t m 5119) source

theorem rule24436 (p1994 p2027 p2177 p2630 p2997 p3551 p3572 p4155 : Prop) (h : (¬ p4155) ∨ (¬ p1994) ∨ (¬ p3572) ∨ (¬ p2630) ∨ p2997 ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3551)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2630) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial24436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory13692 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24436 (meaning t m 1994) (meaning t m 2027) (meaning t m 2177) (meaning t m 2630) (meaning t m 2997) (meaning t m 3551) (meaning t m 3572) (meaning t m 4155) source

theorem rule24438 (p2027 p2132 p2619 p2753 p3146 p3379 p3860 p4286 p4370 p5118 p5216 : Prop) (h : (¬ p2132) ∨ (¬ p3379) ∨ (¬ p4286) ∨ (¬ p4370) ∨ (¬ p3860) ∨ (¬ p3146) ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p2619)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4286) ∨ (¬ p4370) ∨ (¬ p5118) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13694 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24438 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2753) (meaning t m 3146) (meaning t m 3379) (meaning t m 3860) (meaning t m 4286) (meaning t m 4370) (meaning t m 5118) (meaning t m 5216) source

theorem rule24439 (p2027 p2166 p3369 p3371 p3379 p4120 p5216 : Prop) (h : p2027 ∨ (¬ p3371) ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p4120) ∨ (¬ p2166) ∨ (¬ p3369)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13695 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 5 8)
  exact rule24439 (meaning t m 2027) (meaning t m 2166) (meaning t m 3369) (meaning t m 3371) (meaning t m 3379) (meaning t m 4120) (meaning t m 5216) source

theorem rule24441 (p2027 p2264 p2459 p2753 p2807 p3379 p3591 p4026 p4117 p4604 p5216 : Prop) (h : p2027 ∨ (¬ p3379) ∨ (¬ p4117) ∨ (¬ p4026) ∨ (¬ p2264) ∨ (¬ p3591) ∨ (¬ p5216) ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p2753) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2753) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4117) ∨ (¬ p4604) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13697 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24441 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2753) (meaning t m 2807) (meaning t m 3379) (meaning t m 3591) (meaning t m 4026) (meaning t m 4117) (meaning t m 4604) (meaning t m 5216) source

theorem rule24444 (p2027 p2230 p2440 p2922 p3540 p4814 : Prop) (h : (¬ p2440) ∨ (¬ p3540) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4814) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial24444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory13700 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule24444 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2922) (meaning t m 3540) (meaning t m 4814) source

theorem rule24445 (p2027 p2449 p2685 p2696 p3555 p3744 p4173 p4625 p4733 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p4173) ∨ (¬ p4733) ∨ (¬ p2685) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4625) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13701 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule24445 (meaning t m 2027) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4625) (meaning t m 4733) source

theorem rule24449 (p2027 p3097 p3591 p3830 p3957 p4624 p5152 : Prop) (h : (¬ p5152) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p3591) ∨ (¬ p4624) ∨ (¬ p3097) ∨ (¬ p3957)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p3957) ∨ (¬ p4624) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial24449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory13705 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule24449 (meaning t m 2027) (meaning t m 3097) (meaning t m 3591) (meaning t m 3830) (meaning t m 3957) (meaning t m 4624) (meaning t m 5152) source

theorem rule24451 (p2027 p2341 p2753 p3193 p3434 p3461 p3659 p3819 p4425 p4625 p5216 : Prop) (h : (¬ p4625) ∨ (¬ p2753) ∨ (¬ p3461) ∨ (¬ p5216) ∨ (¬ p4425) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p3819) ∨ (¬ p3434) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2753) ∨ (¬ p3193) ∨ (¬ p3434) ∨ (¬ p3461) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13707 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 9) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule24451 (meaning t m 2027) (meaning t m 2341) (meaning t m 2753) (meaning t m 3193) (meaning t m 3434) (meaning t m 3461) (meaning t m 3659) (meaning t m 3819) (meaning t m 4425) (meaning t m 4625) (meaning t m 5216) source

theorem rule24452 (p2696 p3471 p4781 : Prop) (h : (¬ p4781) ∨ (¬ p2696) ∨ p3471) : (¬ p2696) ∨ (p3471) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial24452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (meaning t m 3471) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory13708 (m.theta 0 2) (m.theta 2 3) (m.theta 2 7)
  exact rule24452 (meaning t m 2696) (meaning t m 3471) (meaning t m 4781) source

theorem rule24453 (p2027 p2499 p2588 p2717 p3452 p3471 p3570 p4556 p4733 : Prop) (h : (¬ p2717) ∨ (¬ p2588) ∨ (¬ p4733) ∨ (¬ p3570) ∨ (¬ p4556) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2717) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p4556) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13709 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24453 (meaning t m 2027) (meaning t m 2499) (meaning t m 2588) (meaning t m 2717) (meaning t m 3452) (meaning t m 3471) (meaning t m 3570) (meaning t m 4556) (meaning t m 4733) source

theorem rule24455 (p2027 p2156 p2630 p2957 p3758 p4392 p4701 : Prop) (h : (¬ p2156) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p4392) ∨ (¬ p2630) ∨ p2957 ∨ (¬ p4701)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2630) ∨ (p2957) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2957) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13711 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule24455 (meaning t m 2027) (meaning t m 2156) (meaning t m 2630) (meaning t m 2957) (meaning t m 3758) (meaning t m 4392) (meaning t m 4701) source

theorem rule24456 (p2027 p2166 p2210 p2780 p3969 p4347 p4358 p4736 p5122 : Prop) (h : (¬ p3969) ∨ (¬ p2166) ∨ (¬ p2780) ∨ (¬ p2210) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p5122) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial24456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory13712 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24456 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2780) (meaning t m 3969) (meaning t m 4347) (meaning t m 4358) (meaning t m 4736) (meaning t m 5122) source

theorem rule24457 (p3204 p4486 p4514 : Prop) (h : (¬ p3204) ∨ (¬ p4514) ∨ p4486) : (¬ p3204) ∨ (p4486) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial24457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3204)) ∨ (meaning t m 4486) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory13713 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6)
  exact rule24457 (meaning t m 3204) (meaning t m 4486) (meaning t m 4514) source

theorem rule24458 (p2027 p2579 p2608 p2839 p3105 p3956 p4347 p4450 p5193 : Prop) (h : (¬ p4450) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p2579) ∨ (¬ p4347) ∨ (¬ p5193) ∨ (¬ p2608) ∨ (¬ p3956) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13714 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24458 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3956) (meaning t m 4347) (meaning t m 4450) (meaning t m 5193) source

theorem rule24461 (p3857 p4170 p4347 : Prop) (h : (¬ p4170) ∨ (¬ p4347) ∨ p3857) : (p3857) ∨ (¬ p4170) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial24461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3857) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory13717 (m.theta 0 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24461 (meaning t m 3857) (meaning t m 4170) (meaning t m 4347) source

theorem rule24463 (p2331 p2946 p4336 : Prop) (h : (¬ p2946) ∨ (¬ p4336) ∨ p2331) : (p2331) ∨ (¬ p2946) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial24463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2331) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory13719 (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule24463 (meaning t m 2331) (meaning t m 2946) (meaning t m 4336) source

theorem rule24465 (p2982 p3105 p3698 : Prop) (h : (¬ p3105) ∨ (¬ p3698) ∨ p2982) : (p2982) ∨ (¬ p3105) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial24465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2982) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory13721 (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule24465 (meaning t m 2982) (meaning t m 3105) (meaning t m 3698) source

theorem rule24468 (p2946 p3286 p5038 : Prop) (h : (¬ p2946) ∨ (¬ p5038) ∨ p3286) : (¬ p2946) ∨ (p3286) ∨ (¬ p5038) := by
  classical
  tauto

theorem initial24468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (meaning t m 3286) ∨ (¬ (meaning t m 5038)) := by
  have source := ElevenTheory.theory13724 (m.theta 0 3) (m.theta 3 5) (m.theta 3 9)
  exact rule24468 (meaning t m 2946) (meaning t m 3286) (meaning t m 5038) source

theorem rule24472 (p2027 p2138 p2518 p3379 p4149 p4322 p4385 p4736 p5119 : Prop) (h : (¬ p4385) ∨ (¬ p2518) ∨ (¬ p4149) ∨ (¬ p3379) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p2138) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p4149) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial24472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13728 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule24472 (meaning t m 2027) (meaning t m 2138) (meaning t m 2518) (meaning t m 3379) (meaning t m 4149) (meaning t m 4322) (meaning t m 4385) (meaning t m 4736) (meaning t m 5119) source

theorem rule24480 (p2504 p3096 p4516 : Prop) (h : (¬ p4516) ∨ (¬ p3096) ∨ p2504) : (p2504) ∨ (¬ p3096) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial24480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2504) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory13736 (m.theta 1 6) (m.theta 4 6) (m.theta 5 6)
  exact rule24480 (meaning t m 2504) (meaning t m 3096) (meaning t m 4516) source

theorem rule24483 (p2027 p2928 p2972 p3948 p4644 p4948 : Prop) (h : (¬ p4644) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p3948) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2928) ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4644) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial24483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4644)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory13739 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 9)
  exact rule24483 (meaning t m 2027) (meaning t m 2928) (meaning t m 2972) (meaning t m 3948) (meaning t m 4644) (meaning t m 4948) source

theorem rule24492 (p1980 p2027 p2253 p2579 p2588 p2641 p2764 p2946 p3662 p4107 p4381 p5193 : Prop) (h : (¬ p4381) ∨ (¬ p2253) ∨ p2764 ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2946) ∨ (¬ p5193) ∨ (¬ p3662) ∨ (¬ p1980) ∨ (¬ p2641) ∨ (¬ p4107) ∨ (¬ p2579)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (p2764) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13748 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule24492 (meaning t m 1980) (meaning t m 2027) (meaning t m 2253) (meaning t m 2579) (meaning t m 2588) (meaning t m 2641) (meaning t m 2764) (meaning t m 2946) (meaning t m 3662) (meaning t m 4107) (meaning t m 4381) (meaning t m 5193) source

theorem rule24493 (p1998 p2027 p2264 p2579 p2696 p2766 p3434 p3589 p3947 p3956 p4347 p4781 p5193 : Prop) (h : (¬ p3947) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4781) ∨ (¬ p3589) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p5193) ∨ p2766) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p3434) ∨ (¬ p3589) ∨ (¬ p3947) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4781) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13749 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24493 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2579) (meaning t m 2696) (meaning t m 2766) (meaning t m 3434) (meaning t m 3589) (meaning t m 3947) (meaning t m 3956) (meaning t m 4347) (meaning t m 4781) (meaning t m 5193) source

theorem rule24495 (p2027 p2241 p2589 p3506 p3842 p3880 p5123 p5193 p5568 : Prop) (h : (¬ p5123) ∨ (¬ p3842) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p5568) ∨ (¬ p3506) ∨ (¬ p3880) ∨ (¬ p5193)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p3880) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13751 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24495 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3506) (meaning t m 3842) (meaning t m 3880) (meaning t m 5123) (meaning t m 5193) (meaning t m 5568) source

theorem rule24496 (p2020 p2027 p2241 p2264 p2589 p2997 p3027 p3097 p3941 p4110 p5193 : Prop) (h : p2027 ∨ (¬ p3027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p4110) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p5193) ∨ (¬ p2589) ∨ (¬ p2020) ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (p2997) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3941) ∨ (¬ p4110) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13752 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule24496 (meaning t m 2020) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2589) (meaning t m 2997) (meaning t m 3027) (meaning t m 3097) (meaning t m 3941) (meaning t m 4110) (meaning t m 5193) source

theorem rule24497 (p2027 p2241 p2449 p2589 p3027 p3692 p3880 p3950 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2449) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2241) ∨ (¬ p3880) ∨ (¬ p3027) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13753 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24497 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2589) (meaning t m 3027) (meaning t m 3692) (meaning t m 3880) (meaning t m 3950) (meaning t m 5193) source

theorem rule24498 (p2027 p2255 p2579 p2662 p3286 p3707 p3847 p4111 p4137 p4381 p4625 : Prop) (h : p2027 ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3847) ∨ (¬ p4137) ∨ (¬ p4111) ∨ (¬ p4625) ∨ (¬ p2579) ∨ (¬ p3286) ∨ (¬ p4381) ∨ (¬ p3707)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3286) ∨ (¬ p3707) ∨ (¬ p3847) ∨ (¬ p4111) ∨ (¬ p4137) ∨ (¬ p4381) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial24498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory13754 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24498 (meaning t m 2027) (meaning t m 2255) (meaning t m 2579) (meaning t m 2662) (meaning t m 3286) (meaning t m 3707) (meaning t m 3847) (meaning t m 4111) (meaning t m 4137) (meaning t m 4381) (meaning t m 4625) source

theorem rule24501 (p2027 p2992 p3742 p4111 p4241 p4644 : Prop) (h : (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4644) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2992) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13757 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule24501 (meaning t m 2027) (meaning t m 2992) (meaning t m 3742) (meaning t m 4111) (meaning t m 4241) (meaning t m 4644) source

theorem rule24502 (p2957 p3880 p4120 p4241 : Prop) (h : (¬ p4241) ∨ (¬ p2957) ∨ (¬ p4120) ∨ p3880) : (¬ p2957) ∨ (p3880) ∨ (¬ p4120) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial24502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory13758 (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule24502 (meaning t m 2957) (meaning t m 3880) (meaning t m 4120) (meaning t m 4241) source

theorem rule24503 (p1998 p2027 p2241 p2437 p2699 p2727 p2911 : Prop) (h : (¬ p1998) ∨ (¬ p2911) ∨ (¬ p2241) ∨ p2027 ∨ p2699 ∨ (¬ p2437) ∨ (¬ p2727)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2437) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial24503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory13759 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule24503 (meaning t m 1998) (meaning t m 2027) (meaning t m 2241) (meaning t m 2437) (meaning t m 2699) (meaning t m 2727) (meaning t m 2911) source

theorem rule24504 (p2264 p2911 p3579 : Prop) (h : (¬ p2911) ∨ (¬ p3579) ∨ p2264) : (p2264) ∨ (¬ p2911) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial24504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory13760 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule24504 (meaning t m 2264) (meaning t m 2911) (meaning t m 3579) source

theorem rule24505 (p2000 p2027 p2462 p2579 p3422 p3876 p3921 p4107 : Prop) (h : p2462 ∨ (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p4107) ∨ (¬ p3921) ∨ (¬ p3422) ∨ (¬ p3876)) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial24505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory13761 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule24505 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2579) (meaning t m 3422) (meaning t m 3876) (meaning t m 3921) (meaning t m 4107) source

theorem rule24506 (p2577 p5021 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2577) ∨ p5021) : (¬ p2577) ∨ (p5021) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (meaning t m 5021) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13762 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 6)
  exact rule24506 (meaning t m 2577) (meaning t m 5021) (meaning t m 5193) source

theorem rule24508 (p2509 p2579 p3347 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p3347) ∨ (¬ p2579) ∨ p2509) : (p2509) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial24508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory13764 (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule24508 (meaning t m 2509) (meaning t m 2579) (meaning t m 3347) (meaning t m 3573) source

theorem rule24509 (p2518 p2579 p3347 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p3347) ∨ (¬ p2579) ∨ (¬ p2518)) : (¬ p2518) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial24509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory13765 (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule24509 (meaning t m 2518) (meaning t m 2579) (meaning t m 3347) (meaning t m 3573) source

theorem rule24512 (p2027 p2960 p3516 p3690 p3952 p4204 p4988 : Prop) (h : (¬ p3690) ∨ (¬ p3516) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p2960) ∨ (¬ p3952) ∨ (¬ p4204)) : (p2027) ∨ (¬ p2960) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4204) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial24512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory13768 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule24512 (meaning t m 2027) (meaning t m 2960) (meaning t m 3516) (meaning t m 3690) (meaning t m 3952) (meaning t m 4204) (meaning t m 4988) source

theorem rule24514 (p2027 p2839 p3585 p3695 p4949 p5160 : Prop) (h : p2027 ∨ (¬ p3695) ∨ (¬ p3585) ∨ (¬ p2839) ∨ (¬ p4949) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4949) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4949)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory13770 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 9)
  exact rule24514 (meaning t m 2027) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 4949) (meaning t m 5160) source

theorem rule24516 (p1998 p2027 p2138 p2241 p2264 p2764 p3027 p3744 p3758 p4191 p4736 : Prop) (h : (¬ p2138) ∨ (¬ p1998) ∨ (¬ p2241) ∨ (¬ p3758) ∨ (¬ p3744) ∨ (¬ p4191) ∨ p2764 ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2264) ∨ (¬ p3027)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (p2764) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4191) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13772 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 9 10)
  exact rule24516 (meaning t m 1998) (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2264) (meaning t m 2764) (meaning t m 3027) (meaning t m 3744) (meaning t m 3758) (meaning t m 4191) (meaning t m 4736) source

theorem rule24517 (p2027 p2608 p2829 p3452 p3590 p5224 : Prop) (h : p2027 ∨ (¬ p5224) ∨ (¬ p3452) ∨ (¬ p2608) ∨ (¬ p3590) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p5224) := by
  classical
  tauto

theorem initial24517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 5224)) := by
  have source := ElevenTheory.theory13773 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6)
  exact rule24517 (meaning t m 2027) (meaning t m 2608) (meaning t m 2829) (meaning t m 3452) (meaning t m 3590) (meaning t m 5224) source

theorem rule24521 (p2027 p3548 p3707 p4668 p5233 p5363 p5387 : Prop) (h : (¬ p5233) ∨ (¬ p3548) ∨ (¬ p3707) ∨ p2027 ∨ (¬ p5387) ∨ (¬ p4668) ∨ (¬ p5363)) : (p2027) ∨ (¬ p3548) ∨ (¬ p3707) ∨ (¬ p4668) ∨ (¬ p5233) ∨ (¬ p5363) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial24521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5233)) ∨ (¬ (meaning t m 5363)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory13777 t (m.theta 1 7) (m.theta 1 9) (m.theta 2 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule24521 (meaning t m 2027) (meaning t m 3548) (meaning t m 3707) (meaning t m 4668) (meaning t m 5233) (meaning t m 5363) (meaning t m 5387) source

theorem rule24522 (p2027 p2241 p3506 p3540 p3644 p3842 p5123 p5193 p5558 : Prop) (h : (¬ p5123) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p5558) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3842)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3842) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial24522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13778 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24522 (meaning t m 2027) (meaning t m 2241) (meaning t m 3506) (meaning t m 3540) (meaning t m 3644) (meaning t m 3842) (meaning t m 5123) (meaning t m 5193) (meaning t m 5558) source

theorem rule24523 (p2027 p2608 p3537 p3540 p3644 p4019 p4348 p5122 p5193 : Prop) (h : (¬ p3537) ∨ (¬ p3540) ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p5122) ∨ (¬ p5193) ∨ (¬ p4019) ∨ p2027 ∨ (¬ p2608)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4019) ∨ (¬ p4348) ∨ (¬ p5122) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13779 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24523 (meaning t m 2027) (meaning t m 2608) (meaning t m 3537) (meaning t m 3540) (meaning t m 3644) (meaning t m 4019) (meaning t m 4348) (meaning t m 5122) (meaning t m 5193) source

theorem rule24524 (p1994 p2027 p2241 p2630 p2641 p2766 p3540 p3644 p4195 p4348 p5193 : Prop) (h : p2766 ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p3540) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p4195)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13780 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule24524 (meaning t m 1994) (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2641) (meaning t m 2766) (meaning t m 3540) (meaning t m 3644) (meaning t m 4195) (meaning t m 4348) (meaning t m 5193) source

theorem rule24528 (p2027 p2138 p3093 p3309 p3791 p4385 p4425 p4736 p4826 p4952 : Prop) (h : (¬ p2138) ∨ (¬ p4385) ∨ (¬ p3309) ∨ (¬ p4425) ∨ (¬ p4952) ∨ (¬ p3791) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4385) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p4826) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial24528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory13784 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24528 (meaning t m 2027) (meaning t m 2138) (meaning t m 3093) (meaning t m 3309) (meaning t m 3791) (meaning t m 4385) (meaning t m 4425) (meaning t m 4736) (meaning t m 4826) (meaning t m 4952) source

theorem rule24529 (p2027 p2166 p2210 p2459 p2476 p2534 p3347 p3954 p4902 p5216 : Prop) (h : (¬ p2210) ∨ (¬ p2534) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p2166) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13785 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24529 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 3347) (meaning t m 3954) (meaning t m 4902) (meaning t m 5216) source

theorem rule24531 (p2027 p2589 p2608 p2737 p3005 p3570 p4235 p4550 p5193 : Prop) (h : (¬ p4550) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3570) ∨ (¬ p5193) ∨ (¬ p4235) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4550) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13787 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule24531 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2737) (meaning t m 3005) (meaning t m 3570) (meaning t m 4235) (meaning t m 4550) (meaning t m 5193) source

theorem rule24533 (p2027 p2373 p2590 p2870 p3096 p3694 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p3096) ∨ (¬ p2870) ∨ (¬ p2590) ∨ (¬ p2373) ∨ (¬ p3694) ∨ p2027) : (p2027) ∨ (¬ p2373) ∨ (¬ p2590) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p3694) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13789 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule24533 (meaning t m 2027) (meaning t m 2373) (meaning t m 2590) (meaning t m 2870) (meaning t m 3096) (meaning t m 3694) (meaning t m 4558) source

theorem rule24534 (p2027 p2563 p3051 p3646 p4244 p4882 : Prop) (h : (¬ p4244) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial24534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory13790 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24534 (meaning t m 2027) (meaning t m 2563) (meaning t m 3051) (meaning t m 3646) (meaning t m 4244) (meaning t m 4882) source

theorem rule24535 (p1994 p2027 p2241 p2630 p2641 p2764 p3540 p4195 p4278 p4381 p5193 : Prop) (h : (¬ p4278) ∨ (¬ p4381) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p4195) ∨ (¬ p5193) ∨ p2764 ∨ (¬ p2630) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3540)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (p2764) ∨ (¬ p3540) ∨ (¬ p4195) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial24535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory13791 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule24535 (meaning t m 1994) (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2641) (meaning t m 2764) (meaning t m 3540) (meaning t m 4195) (meaning t m 4278) (meaning t m 4381) (meaning t m 5193) source

theorem rule24536 (p1994 p2027 p2440 p2766 p3570 p4235 p4348 : Prop) (h : p2766 ∨ (¬ p4235) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p1994) ∨ (¬ p3570)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2766) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial24536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory13792 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule24536 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2766) (meaning t m 3570) (meaning t m 4235) (meaning t m 4348) source

theorem rule24537 (p2027 p2295 p2417 p3922 p4026 p4396 p4712 : Prop) (h : p2027 ∨ (¬ p2417) ∨ (¬ p4396) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p2295) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2417) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial24537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory13793 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule24537 (meaning t m 2027) (meaning t m 2295) (meaning t m 2417) (meaning t m 3922) (meaning t m 4026) (meaning t m 4396) (meaning t m 4712) source

theorem rule24539 (p2027 p2156 p3564 p4032 p4033 p4718 : Prop) (h : (¬ p3564) ∨ (¬ p4718) ∨ (¬ p4032) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4033)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3564) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial24539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory13795 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule24539 (meaning t m 2027) (meaning t m 2156) (meaning t m 3564) (meaning t m 4032) (meaning t m 4033) (meaning t m 4718) source

theorem rule24541 (p2027 p2192 p2210 p2534 p3055 p3125 p3874 p4330 p4736 : Prop) (h : (¬ p2534) ∨ (¬ p2210) ∨ (¬ p4736) ∨ (¬ p3125) ∨ (¬ p3874) ∨ (¬ p2192) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4330)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3874) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial24541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13797 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule24541 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2534) (meaning t m 3055) (meaning t m 3125) (meaning t m 3874) (meaning t m 4330) (meaning t m 4736) source

theorem rule24542 (p1992 p2027 p2462 p2911 p3363 p3551 p3585 p4278 p5197 : Prop) (h : (¬ p1992) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p5197) ∨ p2462 ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p4278)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2911) ∨ (¬ p3363) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial24542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory13798 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24542 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2911) (meaning t m 3363) (meaning t m 3551) (meaning t m 3585) (meaning t m 4278) (meaning t m 5197) source

theorem rule24543 (p2027 p2459 p2717 p3238 p3452 p3471 p4733 p4948 p5059 : Prop) (h : (¬ p3471) ∨ (¬ p4733) ∨ (¬ p5059) ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p4948) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4733) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial24543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory13799 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24543 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 3238) (meaning t m 3452) (meaning t m 3471) (meaning t m 4733) (meaning t m 4948) (meaning t m 5059) source

theorem rule24544 (p2027 p2248 p2331 p3688 p3954 p4337 : Prop) (h : (¬ p2248) ∨ (¬ p4337) ∨ (¬ p3954) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3688)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial24544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory13800 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 6)
  exact rule24544 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3688) (meaning t m 3954) (meaning t m 4337) source

theorem rule24546 (p1988 p2027 p2122 p2396 p2761 p2774 p3043 p3238 p3452 p4733 p4948 : Prop) (h : (¬ p1988) ∨ (¬ p2761) ∨ p3043 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p4733) ∨ (¬ p3238) ∨ (¬ p2122)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (p3043) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4733) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial24546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory13802 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule24546 (meaning t m 1988) (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2761) (meaning t m 2774) (meaning t m 3043) (meaning t m 3238) (meaning t m 3452) (meaning t m 4733) (meaning t m 4948) source

theorem rule24547 (p2427 p4241 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p2427) ∨ (¬ p4241)) : (¬ p2427) ∨ (¬ p4241) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial24547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory13803 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule24547 (meaning t m 2427) (meaning t m 4241) (meaning t m 4320) source

theorem rule24549 (p2027 p2088 p2748 p2779 p2829 p3365 p3497 p3662 p4114 p4134 p4347 p4734 : Prop) (h : (¬ p3497) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p4734) ∨ (¬ p3365) ∨ (¬ p2748) ∨ (¬ p3662) ∨ (¬ p2829) ∨ (¬ p2779) ∨ (¬ p4347) ∨ (¬ p4114)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4114) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial24549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory13805 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24549 (meaning t m 2027) (meaning t m 2088) (meaning t m 2748) (meaning t m 2779) (meaning t m 2829) (meaning t m 3365) (meaning t m 3497) (meaning t m 3662) (meaning t m 4114) (meaning t m 4134) (meaning t m 4347) (meaning t m 4734) source

theorem rule24550 (p2533 p3880 p4948 : Prop) (h : (¬ p2533) ∨ (¬ p4948) ∨ p3880) : (¬ p2533) ∨ (p3880) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial24550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory13806 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule24550 (meaning t m 2533) (meaning t m 3880) (meaning t m 4948) source

theorem rule24555 (p2027 p2651 p3292 p3755 p4315 p4701 : Prop) (h : (¬ p3755) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p4701) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3292) ∨ (¬ p3755) ∨ (¬ p4315) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial24555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory13811 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 9)
  exact rule24555 (meaning t m 2027) (meaning t m 2651) (meaning t m 3292) (meaning t m 3755) (meaning t m 4315) (meaning t m 4701) source

theorem rule24558 (p2027 p2191 p2246 p2331 p2749 p3256 p3379 p3555 p4134 p4341 p4347 p5216 : Prop) (h : p2027 ∨ (¬ p5216) ∨ (¬ p4134) ∨ (¬ p3555) ∨ (¬ p2191) ∨ (¬ p3379) ∨ (¬ p2749) ∨ (¬ p3256) ∨ (¬ p2331) ∨ (¬ p4347) ∨ (¬ p2246) ∨ (¬ p4341)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2749) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4134) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13814 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24558 (meaning t m 2027) (meaning t m 2191) (meaning t m 2246) (meaning t m 2331) (meaning t m 2749) (meaning t m 3256) (meaning t m 3379) (meaning t m 3555) (meaning t m 4134) (meaning t m 4341) (meaning t m 4347) (meaning t m 5216) source

theorem rule24560 (p2027 p2122 p2177 p2774 p2928 p3452 p4278 p4666 p4733 : Prop) (h : (¬ p3452) ∨ (¬ p2122) ∨ (¬ p4278) ∨ (¬ p2928) ∨ (¬ p2177) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13816 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24560 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2774) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4666) (meaning t m 4733) source

theorem rule24562 (p3820 p3905 p5197 : Prop) (h : (¬ p3905) ∨ (¬ p5197) ∨ p3820) : (p3820) ∨ (¬ p3905) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial24562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3820) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory13818 (m.theta 0 2) (m.theta 0 4) (m.theta 0 7)
  exact rule24562 (meaning t m 3820) (meaning t m 3905) (meaning t m 5197) source

theorem rule24566 (p2027 p2139 p2156 p2274 p2476 p3791 p3905 p4340 p4444 p4826 p5373 : Prop) (h : (¬ p2139) ∨ (¬ p2476) ∨ (¬ p4340) ∨ (¬ p2274) ∨ (¬ p2156) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3791) ∨ (¬ p4826) ∨ (¬ p5373) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2476) ∨ (¬ p3791) ∨ (¬ p3905) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial24566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory13822 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24566 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2476) (meaning t m 3791) (meaning t m 3905) (meaning t m 4340) (meaning t m 4444) (meaning t m 4826) (meaning t m 5373) source

theorem rule24569 (p2027 p2383 p2797 p3877 p4584 p4769 : Prop) (h : (¬ p4769) ∨ (¬ p2797) ∨ (¬ p3877) ∨ (¬ p2383) ∨ (¬ p4584) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3877) ∨ (¬ p4584) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial24569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4584)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory13825 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule24569 (meaning t m 2027) (meaning t m 2383) (meaning t m 2797) (meaning t m 3877) (meaning t m 4584) (meaning t m 4769) source

theorem rule24570 (p2027 p2459 p2717 p2753 p3379 p3471 p3860 p5118 p5216 p5693 : Prop) (h : p2027 ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p5216) ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p5118) ∨ (¬ p2717) ∨ (¬ p5693) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3471) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5216) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial24570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory13826 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24570 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 2753) (meaning t m 3379) (meaning t m 3471) (meaning t m 3860) (meaning t m 5118) (meaning t m 5216) (meaning t m 5693) source

theorem rule24571 (p2027 p2749 p3073 p3379 p3857 p3859 p4416 p5216 : Prop) (h : (¬ p3379) ∨ (¬ p4416) ∨ (¬ p3073) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p2749) ∨ (¬ p5216) ∨ (¬ p3859)) : (p2027) ∨ (¬ p2749) ∨ (¬ p3073) ∨ (¬ p3379) ∨ (¬ p3857) ∨ (¬ p3859) ∨ (¬ p4416) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13827 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 8) (m.theta 8 9)
  exact rule24571 (meaning t m 2027) (meaning t m 2749) (meaning t m 3073) (meaning t m 3379) (meaning t m 3857) (meaning t m 3859) (meaning t m 4416) (meaning t m 5216) source

theorem rule24572 (p1990 p2027 p2169 p2284 p2696 p2753 p3136 p3379 p3564 p3834 p3956 p5148 p5216 : Prop) (h : p2027 ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p3564) ∨ (¬ p2753) ∨ (¬ p2284) ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p5148) ∨ (¬ p3956) ∨ p2169 ∨ (¬ p1990) ∨ (¬ p3834)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3834) ∨ (¬ p3956) ∨ (¬ p5148) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5148)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13828 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule24572 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2284) (meaning t m 2696) (meaning t m 2753) (meaning t m 3136) (meaning t m 3379) (meaning t m 3564) (meaning t m 3834) (meaning t m 3956) (meaning t m 5148) (meaning t m 5216) source

theorem rule24573 (p2027 p2166 p2210 p2498 p3096 p3591 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p2498) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2210) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2498) ∨ (¬ p3096) ∨ (¬ p3591) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial24573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory13829 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule24573 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2498) (meaning t m 3096) (meaning t m 3591) (meaning t m 4509) source

theorem rule24574 (p2027 p2717 p2753 p3379 p3471 p3860 p3979 p4138 p4261 p5122 p5216 : Prop) (h : (¬ p2717) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p4138) ∨ (¬ p3860) ∨ (¬ p5216) ∨ (¬ p3471) ∨ (¬ p4261) ∨ (¬ p3379) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3471) ∨ (¬ p3860) ∨ (¬ p3979) ∨ (¬ p4138) ∨ (¬ p4261) ∨ (¬ p5122) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13830 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24574 (meaning t m 2027) (meaning t m 2717) (meaning t m 2753) (meaning t m 3379) (meaning t m 3471) (meaning t m 3860) (meaning t m 3979) (meaning t m 4138) (meaning t m 4261) (meaning t m 5122) (meaning t m 5216) source

theorem rule24576 (p2027 p2210 p2696 p2753 p2797 p3323 p3860 p4261 p4330 p4877 : Prop) (h : (¬ p2797) ∨ (¬ p3323) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p4330) ∨ (¬ p3860) ∨ (¬ p2696) ∨ (¬ p4261) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13832 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9)
  exact rule24576 (meaning t m 2027) (meaning t m 2210) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3323) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) (meaning t m 4877) source

theorem rule24578 (p2027 p2927 p3222 p3379 p4366 p4640 : Prop) (h : p2027 ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p2927) ∨ (¬ p4640) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2927) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4640) := by
  classical
  tauto

theorem initial24578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4640)) := by
  have source := ElevenTheory.theory13834 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 4 9)
  exact rule24578 (meaning t m 2027) (meaning t m 2927) (meaning t m 3222) (meaning t m 3379) (meaning t m 4366) (meaning t m 4640) source

theorem rule24579 (p2027 p2210 p2685 p2696 p2753 p3834 p3931 p4321 p4826 p4877 : Prop) (h : (¬ p4321) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p4826) ∨ (¬ p3931) ∨ (¬ p2685) ∨ (¬ p3834)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3834) ∨ (¬ p3931) ∨ (¬ p4321) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13835 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 9) (m.theta 2 3) (m.theta 3 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24579 (meaning t m 2027) (meaning t m 2210) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3834) (meaning t m 3931) (meaning t m 4321) (meaning t m 4826) (meaning t m 4877) source

theorem rule24584 (p2027 p2476 p2534 p2685 p2696 p3931 p4444 p4729 p4826 : Prop) (h : (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2476) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p3931)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3931) ∨ (¬ p4444) ∨ (¬ p4729) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13840 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24584 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2685) (meaning t m 2696) (meaning t m 3931) (meaning t m 4444) (meaning t m 4729) (meaning t m 4826) source

theorem rule24585 (p2027 p3027 p3516 p4066 p4360 p4548 p4668 : Prop) (h : (¬ p4548) ∨ (¬ p4360) ∨ (¬ p4066) ∨ (¬ p3516) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4668)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial24585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13841 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 7 9)
  exact rule24585 (meaning t m 2027) (meaning t m 3027) (meaning t m 3516) (meaning t m 4066) (meaning t m 4360) (meaning t m 4548) (meaning t m 4668) source

theorem rule24587 (p2027 p2588 p3027 p3552 p4154 p4976 : Prop) (h : (¬ p3552) ∨ (¬ p4154) ∨ (¬ p4976) ∨ (¬ p3027) ∨ (¬ p2588) ∨ p2027) : (p2027) ∨ (¬ p2588) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4154) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial24587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory13843 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule24587 (meaning t m 2027) (meaning t m 2588) (meaning t m 3027) (meaning t m 3552) (meaning t m 4154) (meaning t m 4976) source

theorem rule24588 (p2027 p2132 p2187 p2459 p2860 p3860 p4133 p4261 p4733 : Prop) (h : p2027 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2860) ∨ (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13844 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24588 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2459) (meaning t m 2860) (meaning t m 3860) (meaning t m 4133) (meaning t m 4261) (meaning t m 4733) source

theorem rule24589 (p2027 p2132 p2499 p3055 p3695 p4030 p4715 : Prop) (h : (¬ p2499) ∨ (¬ p3695) ∨ (¬ p4030) ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p4715) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2499) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p4030) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial24589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory13845 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6)
  exact rule24589 (meaning t m 2027) (meaning t m 2132) (meaning t m 2499) (meaning t m 3055) (meaning t m 3695) (meaning t m 4030) (meaning t m 4715) source

theorem rule24591 (p2027 p2138 p2331 p2668 p2737 p2811 p3570 p4133 p4244 p4734 : Prop) (h : (¬ p2737) ∨ (¬ p3570) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p2331) ∨ (¬ p2811) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial24591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory13847 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule24591 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 2668) (meaning t m 2737) (meaning t m 2811) (meaning t m 3570) (meaning t m 4133) (meaning t m 4244) (meaning t m 4734) source

theorem rule24593 (p2027 p2210 p2598 p2753 p3422 p3564 p3690 p4366 p4621 p4877 p4909 : Prop) (h : (¬ p2753) ∨ (¬ p4366) ∨ (¬ p4909) ∨ (¬ p4621) ∨ (¬ p2598) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p4877) ∨ (¬ p3690) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4366) ∨ (¬ p4621) ∨ (¬ p4877) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial24593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory13849 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule24593 (meaning t m 2027) (meaning t m 2210) (meaning t m 2598) (meaning t m 2753) (meaning t m 3422) (meaning t m 3564) (meaning t m 3690) (meaning t m 4366) (meaning t m 4621) (meaning t m 4877) (meaning t m 4909) source

theorem rule24595 (p2027 p2417 p3556 p3690 p3741 p4533 : Prop) (h : (¬ p3690) ∨ (¬ p3741) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p4533) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial24595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory13851 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule24595 (meaning t m 2027) (meaning t m 2417) (meaning t m 3556) (meaning t m 3690) (meaning t m 3741) (meaning t m 4533) source

theorem rule24596 (p2245 p4733 p4789 : Prop) (h : (¬ p2245) ∨ (¬ p4733) ∨ p4789) : (¬ p2245) ∨ (¬ p4733) ∨ (p4789) := by
  classical
  tauto

theorem initial24596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 4733)) ∨ (meaning t m 4789) := by
  have source := ElevenTheory.theory13852 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3)
  exact rule24596 (meaning t m 2245) (meaning t m 4733) (meaning t m 4789) source

theorem rule24597 (p4357 p4897 p5049 : Prop) (h : (¬ p4357) ∨ (¬ p5049) ∨ p4897) : (¬ p4357) ∨ (p4897) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial24597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4357)) ∨ (meaning t m 4897) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory13853 t (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule24597 (meaning t m 4357) (meaning t m 4897) (meaning t m 5049) source

theorem rule24598 (p2027 p2780 p3471 p4358 p4475 p4501 : Prop) (h : (¬ p4475) ∨ (¬ p4358) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4501) ∨ p2027) : (p2027) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4358) ∨ (¬ p4475) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial24598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13854 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8)
  exact rule24598 (meaning t m 2027) (meaning t m 2780) (meaning t m 3471) (meaning t m 4358) (meaning t m 4475) (meaning t m 4501) source

theorem rule24600 (p2027 p2132 p2247 p2870 p2996 p3246 p3553 p4668 p4733 : Prop) (h : (¬ p4668) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2247) ∨ (¬ p4733) ∨ (¬ p3246) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13856 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24600 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2870) (meaning t m 2996) (meaning t m 3246) (meaning t m 3553) (meaning t m 4668) (meaning t m 4733) source

theorem rule24601 (p2156 p2190 p2220 : Prop) (h : (¬ p2190) ∨ (¬ p2156) ∨ p2220) : (¬ p2156) ∨ (¬ p2190) ∨ (p2220) := by
  classical
  tauto

theorem initial24601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (meaning t m 2220) := by
  have source := ElevenTheory.theory13857 (m.theta 0 5) (m.theta 5 6) (m.theta 5 8)
  exact rule24601 (meaning t m 2156) (meaning t m 2190) (meaning t m 2220) source

theorem rule24602 (p2027 p2098 p2247 p2996 p3553 p3609 p4133 p4347 p4733 : Prop) (h : (¬ p2996) ∨ (¬ p4347) ∨ (¬ p3553) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p3609) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13858 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24602 (meaning t m 2027) (meaning t m 2098) (meaning t m 2247) (meaning t m 2996) (meaning t m 3553) (meaning t m 3609) (meaning t m 4133) (meaning t m 4347) (meaning t m 4733) source

theorem rule24603 (p2027 p2220 p2247 p2996 p3146 p3266 p4391 p4521 p4831 : Prop) (h : (¬ p2996) ∨ (¬ p3146) ∨ (¬ p2247) ∨ (¬ p4391) ∨ (¬ p4521) ∨ (¬ p4831) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4391) ∨ (¬ p4521) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial24603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory13859 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24603 (meaning t m 2027) (meaning t m 2220) (meaning t m 2247) (meaning t m 2996) (meaning t m 3146) (meaning t m 3266) (meaning t m 4391) (meaning t m 4521) (meaning t m 4831) source

theorem rule24604 (p1998 p2027 p2177 p2202 p2563 p3246 p3872 p4107 : Prop) (h : p2202 ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p2563) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial24604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory13860 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24604 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2563) (meaning t m 3246) (meaning t m 3872) (meaning t m 4107) source

theorem rule24606 (p2027 p2363 p2774 p2819 p3238 p3452 p4733 p4948 p5059 : Prop) (h : (¬ p2819) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4948) ∨ (¬ p4733) ∨ (¬ p3452) ∨ (¬ p2363) ∨ (¬ p5059) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4733) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial24606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory13862 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule24606 (meaning t m 2027) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 3238) (meaning t m 3452) (meaning t m 4733) (meaning t m 4948) (meaning t m 5059) source

theorem rule24614 (p2027 p2143 p2187 p2387 p2870 p4198 p4558 : Prop) (h : p2027 ∨ (¬ p2143) ∨ (¬ p4558) ∨ (¬ p2387) ∨ (¬ p2187) ∨ (¬ p4198) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2870) ∨ (¬ p4198) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13870 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule24614 (meaning t m 2027) (meaning t m 2143) (meaning t m 2187) (meaning t m 2387) (meaning t m 2870) (meaning t m 4198) (meaning t m 4558) source

theorem rule24615 (p2027 p2493 p2542 p3238 p3584 p4750 : Prop) (h : (¬ p2542) ∨ (¬ p4750) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial24615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13871 t (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule24615 (meaning t m 2027) (meaning t m 2493) (meaning t m 2542) (meaning t m 3238) (meaning t m 3584) (meaning t m 4750) source

theorem rule24616 (p2027 p2098 p2247 p2996 p3553 p3609 p3692 p4733 p4902 : Prop) (h : (¬ p4733) ∨ (¬ p2996) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3553) ∨ (¬ p2247) ∨ (¬ p3609) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13872 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24616 (meaning t m 2027) (meaning t m 2098) (meaning t m 2247) (meaning t m 2996) (meaning t m 3553) (meaning t m 3609) (meaning t m 3692) (meaning t m 4733) (meaning t m 4902) source

end SunPrize.SMT
